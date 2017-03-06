package trepplein

import scala.concurrent.{ ExecutionContext, Future }
import scala.language.implicitConversions

abstract class Declaration {
  def name: Name
  def univParams: Vector[Level.Param]
  def ty: Expr

  def asAxiom: Axiom = Axiom(name, univParams, ty)
}
final case class Axiom(name: Name, univParams: Vector[Level.Param], ty: Expr) extends Declaration {
  def check(env: PreEnvironment): Unit = {
    require(!env.declarations.contains(name))
    require(ty.univParams.subsetOf(univParams.toSet))
    require(!ty.hasVars)
    require(!ty.hasLocals)
    val tc = new TypeChecker(env)
    require(tc.infer(ty).isInstanceOf[Sort])
  }
}
final case class Definition(name: Name, univParams: Vector[Level.Param],
    ty: Expr, value: Expr, height: Int = 0) extends Declaration {
  def check(env: PreEnvironment): Unit = {
    asAxiom.check(env)
    require(!value.hasVars)
    require(!value.hasLocals)
    val tc = new TypeChecker(env)
    tc.requireDefEq(tc.infer(value), ty)
  }
}

abstract class Builtin extends Declaration

trait Modification {
  def name: Name
  def declsFor(env: PreEnvironment): Seq[Declaration]
  def check(env: PreEnvironment): Unit
}
object Modification {
  implicit def ofAxiom(axiom: Axiom): Modification = AxiomMod(axiom)
}
final case class AxiomMod(ax: Axiom) extends Modification {
  def name: Name = ax.name
  override def declsFor(env: PreEnvironment): Seq[Declaration] = Seq(ax)
  override def check(env: PreEnvironment): Unit = ax.check(env)
}
final case class DefMod(defn: Definition) extends Modification {
  def name: Name = defn.name
  override def declsFor(env: PreEnvironment): Seq[Declaration] = {
    val height = (defn.value.constants.flatMap(env.get).collect { case d: Definition => d.height } + 0).max + 1
    Seq(defn.copy(height = height))
  }
  override def check(env: PreEnvironment): Unit = defn.check(env)
}

sealed class PreEnvironment protected (
    val declarations: Map[Name, Declaration],
    val proofObligations: List[Future[Option[Throwable]]],
    val checked: Boolean
) {

  def get(name: Name): Option[Declaration] =
    declarations.get(name)
  def apply(name: Name): Declaration =
    declarations(name)

  def addNow(mod: Modification): PreEnvironment = {
    if (checked) mod.check(this)
    new PreEnvironment(
      declarations ++ mod.declsFor(this).view.map(d => d.name -> d),
      proofObligations,
      checked
    )
  }

  def add(mod: Modification)(implicit executionContext: ExecutionContext): PreEnvironment =
    new PreEnvironment(
      declarations ++ mod.declsFor(this).view.map(d => d.name -> d),
      if (checked) Future {
        try {
          mod.check(this)
          None
        } catch {
          case t: Throwable =>
            Some(new Exception(s"${mod.name}: ${t.getMessage}", t))
        }
      } :: proofObligations
      else Nil,
      checked
    )

  def unchecked: PreEnvironment = new PreEnvironment(declarations, Nil, checked = false)

  def force(implicit executionContext: ExecutionContext): Future[Either[Seq[Throwable], Environment]] = {
    require(checked)
    Environment.force(this)
  }
}

final class Environment private (declarations: Map[Name, Declaration])
  extends PreEnvironment(declarations, Nil, checked = true)
object Environment {
  def force(preEnvironment: PreEnvironment)(implicit executionContext: ExecutionContext): Future[Either[Seq[Throwable], Environment]] =
    Future.sequence(preEnvironment.proofObligations).map(_.flatten).map {
      case Nil => Right(new Environment(preEnvironment.declarations))
      case exs => Left(exs)
    }

  def default = new Environment(Map())
}