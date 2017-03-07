package trepplein

import scala.concurrent.{ ExecutionContext, Future }
import scala.language.implicitConversions
import scala.util.Try

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
    val height = defn.value.constants.view.
      flatMap(env.get).
      collect { case d: Definition => d.height }.
      fold(0)(math.max) + 1

    Seq(defn.copy(height = height))
  }
  override def check(env: PreEnvironment): Unit = defn.check(env)
}

case class EnvironmentUpdateError(mod: Modification, msg: String) {
  override def toString = s"${mod.name}: $msg"
}

sealed class PreEnvironment protected (
    val declarations: Map[Name, Declaration],
    val proofObligations: List[Future[Option[EnvironmentUpdateError]]]
) {

  def get(name: Name): Option[Declaration] =
    declarations.get(name)
  def apply(name: Name): Declaration =
    declarations(name)

  private def addDeclsFor(mod: Modification): Map[Name, Declaration] =
    declarations ++ mod.declsFor(this).view.map(d => d.name -> d)

  def addWithFuture(mod: Modification)(implicit executionContext: ExecutionContext): (Future[Option[EnvironmentUpdateError]], PreEnvironment) = {
    val checkingTask = Future {
      Try(mod.check(this)).toEither.swap.toOption.
        map(t => EnvironmentUpdateError(mod, t.getMessage))
    }
    checkingTask -> new PreEnvironment(addDeclsFor(mod), checkingTask :: proofObligations)
  }

  def addNow(mod: Modification): PreEnvironment = {
    mod.check(this)
    new PreEnvironment(addDeclsFor(mod), proofObligations)
  }

  def add(mod: Modification)(implicit executionContext: ExecutionContext): PreEnvironment =
    addWithFuture(mod)._2

  def force(implicit executionContext: ExecutionContext): Future[Either[Seq[EnvironmentUpdateError], Environment]] =
    Environment.force(this)
}

final class Environment private (declarations: Map[Name, Declaration])
  extends PreEnvironment(declarations, Nil)
object Environment {
  def force(preEnvironment: PreEnvironment)(implicit executionContext: ExecutionContext): Future[Either[Seq[EnvironmentUpdateError], Environment]] =
    Future.sequence(preEnvironment.proofObligations).map(_.flatten).map {
      case Nil => Right(new Environment(preEnvironment.declarations))
      case exs => Left(exs)
    }

  def default = new Environment(Map())
}