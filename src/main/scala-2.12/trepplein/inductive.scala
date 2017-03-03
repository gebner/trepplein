package trepplein

import trepplein.Level.Param

final case class InductiveType(name: Name, univParams: Vector[Level.Param], ty: Expr) extends Builtin
final case class Elim(name: Name, ty: Expr, ind: InductiveType, univParams: Vector[Level.Param],
  numParams: Int, numIndices: Int, numMinors: Int,
  motive: Int, major: Int, depElim: Boolean,
  kIntro: Option[Name]) extends Builtin
final case class Intro(name: Name, ty: Expr, ind: InductiveType, univParams: Vector[Level.Param], compRule: Expr) extends Builtin

final case class CompiledIndMod(indMod: IndMod, env: PreEnvironment) {
  import indMod._
  val tc = new TypeChecker(env)

  def name: Name = inductiveType.name

  def univParams: Vector[Param] = inductiveType.univParams
  val indTy = Const(inductiveType.name, univParams)

  val ((params, indices), level) =
    inductiveType.ty match {
      case Pis(doms, Sort(lvl)) =>
        (doms.splitAt(numParams), lvl)
    }

  val elimIntoProp: Boolean = !NLevel.isNonZero(level) && (intros.size > 1 || intros.exists {
    case (_, Pis(doms, Apps(Const(inductiveType.name, _), introIndTyArgs))) =>
      val arguments = doms.drop(params.size)
      arguments.exists { arg =>
        tc.whnf(tc.infer(tc.infer(arg))) match {
          case Sort(l) => !NLevel.isZero(l)
          case _ => true
        }
      }
  })

  val elimLevel: Level = if (elimIntoProp) Level.Zero else Level.Param("l")
  val extraElimLevelParams: Vector[Param] = Vector(elimLevel).collect { case p: Level.Param => p }

  val useDepElim: Boolean = level != Level.Zero

  val motive: LocalConst = if (useDepElim)
    LocalConst(Binding("C", Pis(indices :+ LocalConst(Binding("c", Apps(indTy, params ++ indices), BinderInfo.Default)))(Sort(elimLevel)), BinderInfo.Default))
  else
    LocalConst(Binding("C", Pis(indices)(Sort(elimLevel)), BinderInfo.Default))

  def mkMotiveApp(indices: Seq[Expr], e: Expr): Expr =
    if (useDepElim) App(Apps(motive, indices), e) else Apps(motive, indices)

  val minorPremises: Vector[LocalConst] = intros.map {
    case (n, ty) =>
      Pis.drop(params.size, ty).instantiate(0, params.toVector.reverse) match {
        case Pis(arguments, Apps(Const(inductiveType.name, _), introIndTyArgs)) =>
          val ihs = arguments.collect {
            case recArg @ LocalConst(Binding(_, Pis(eps, Apps(Const(inductiveType.name, _), indTyArgs)), _), _) =>
              LocalConst(Binding("ih", Pis(eps)(mkMotiveApp(indTyArgs.drop(numParams), Apps(recArg, eps))), BinderInfo.Default))
          }
          LocalConst(Binding("h", Pis(arguments ++ ihs)(mkMotiveApp(introIndTyArgs.drop(numParams), Apps(Const(n, univParams), params ++ arguments))), BinderInfo.Default))
      }
  }

  val kIntro = intros match {
    case Vector((n, Pis(ps, _))) if ps.size == numParams && level == Level.Zero => Some(n)
    case _ => None
  }

  val majorPremise = LocalConst(Binding("x", Apps(indTy, params ++ indices), BinderInfo.Default))

  val elimType: Expr = Pis(params ++ Seq(motive) ++ minorPremises ++ indices :+ majorPremise)(mkMotiveApp(indices, majorPremise))

  val elimLevelParams = extraElimLevelParams ++ univParams
  val elimDecl = Elim(Name.Str(name, "rec"), elimType, inductiveType, elimLevelParams,
    numParams = numParams, motive = numParams, numIndices = indices.size, numMinors = minorPremises.size,
    major = numParams + 1 + minorPremises.size + indices.size, depElim = useDepElim,
    kIntro = kIntro)

  val compRules = intros.zip(minorPremises).map {
    case ((n, ty), minor) =>
      Pis.drop(params.size, ty).instantiate(0, params.toVector.reverse) match {
        case Pis(arguments, Apps(Const(inductiveType.name, _), introIndTyArgs)) =>
          val ihs = arguments.collect {
            case recArg @ LocalConst(Binding(_, Pis(eps, Apps(Const(inductiveType.name, _), indTyArgs)), _), _) =>
              // TODO: eps
              Apps(Const(elimDecl.name, elimLevelParams), params ++ Seq(motive) ++ minorPremises ++ indTyArgs.drop(numParams) :+ recArg)
          }
          Lams(params ++ Seq(motive) ++ minorPremises ++ arguments)(
            Apps(minor, arguments ++ ihs)
          )
      }
  }

  val introDecls: Vector[Intro] =
    for (((n, t), cr) <- intros.zip(compRules))
      yield Intro(n, t, inductiveType, inductiveType.univParams, cr)

  val decls = inductiveType +: introDecls :+ elimDecl
}

final case class IndMod(inductiveType: InductiveType, numParams: Int, intros: Vector[(Name, Expr)]) extends Modification {
  def name = inductiveType.name

  def declsFor(env: PreEnvironment) = CompiledIndMod(this, env).decls

  override def check(env0: PreEnvironment): Unit = {
    val compiled = new CompiledIndMod(this, env0)
    val withType = env0.addNow(inductiveType.asAxiom)
    val withIntros = compiled.introDecls.foldLeft(withType)((env, i) => { i.asAxiom.check(withType); env.addNow(i.asAxiom) })
    withIntros.addNow(compiled.elimDecl.asAxiom)
  }
}
