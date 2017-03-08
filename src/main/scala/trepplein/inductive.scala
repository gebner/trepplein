package trepplein

import trepplein.Level.Param

final case class InductiveType(name: Name, univParams: Vector[Level.Param], ty: Expr) extends Builtin
final case class Elim(name: Name, ty: Expr, ind: InductiveType, univParams: Vector[Level.Param],
  numParams: Int, numIndices: Int, numMinors: Int,
  motive: Int, major: Int, depElim: Boolean,
  kIntro: Option[Name]) extends Builtin
final case class Intro(name: Name, ty: Expr, ind: InductiveType, univParams: Vector[Level.Param], compRule: Expr) extends Builtin

final case class CompiledIndMod(indMod: IndMod, env: PreEnvironment) extends CompiledModification {
  import indMod._
  val tc = new TypeChecker(env.addNow(inductiveType.asAxiom))

  def name: Name = inductiveType.name

  def univParams: Vector[Param] = inductiveType.univParams
  val indTy = Const(inductiveType.name, univParams)

  object NormalizedPis {
    def unapply(e: Expr): Some[(List[LocalConst], Expr)] =
      tc.whnf(e) match {
        case Pis(lcs1, f) if lcs1.nonEmpty =>
          val NormalizedPis(lcs2, g) = f
          Some((lcs1 ::: lcs2, g))
        case f => Some((Nil, f))
      }

    def normalize(e: Expr): Expr =
      e match { case NormalizedPis(xs, f) => Pis(xs)(f) }

    def instantiate(e: Expr, ts: Seq[Expr]): Expr =
      Pis.instantiate(normalize(e), ts)
  }

  val ((params, indices), level) =
    inductiveType.ty match {
      case NormalizedPis(doms, Sort(lvl)) =>
        (doms.splitAt(numParams), lvl)
    }

  val elimIntoProp: Boolean = !Level.isNonZero(level) && (intros.size > 1 || intros.exists {
    case (_, NormalizedPis(doms, Apps(Const(inductiveType.name, _), introIndTyArgs))) =>
      val arguments = doms.drop(params.size)
      arguments.exists { arg =>
        !tc.isProof(arg) && !introIndTyArgs.contains(arg)
      }
  })

  val elimLevel: Level = if (elimIntoProp) Level.Zero else Level.Param("l")
  val extraElimLevelParams: Vector[Param] = Vector(elimLevel).collect { case p: Level.Param => p }

  val useDepElim: Boolean = level != Level.Zero

  val motiveType: Expr =
    if (useDepElim)
      Pis(indices :+ LocalConst(Binding("c", Apps(indTy, params ++ indices), BinderInfo.Default)))(Sort(elimLevel))
    else
      Pis(indices)(Sort(elimLevel))
  val motive = LocalConst(Binding("C", motiveType, BinderInfo.Implicit))

  def mkMotiveApp(indices: Seq[Expr], e: Expr): Expr =
    if (useDepElim) App(Apps(motive, indices), e) else Apps(motive, indices)

  val minorPremises: Vector[LocalConst] = intros.map {
    case (n, ty) =>
      NormalizedPis.instantiate(ty, params) match {
        case NormalizedPis(arguments, Apps(Const(inductiveType.name, _), introIndTyArgs)) =>
          val ihs = arguments.collect {
            case recArg @ LocalConst(Binding(_, NormalizedPis(eps, Apps(Const(inductiveType.name, _), indTyArgs)), _), _) =>
              LocalConst(Binding("ih", Pis(eps)(mkMotiveApp(indTyArgs.drop(numParams), Apps(recArg, eps))), BinderInfo.Default))
          }
          LocalConst(Binding("h", Pis(arguments ++ ihs)(mkMotiveApp(introIndTyArgs.drop(numParams), Apps(Const(n, univParams), params ++ arguments))), BinderInfo.Default))
      }
  }

  val kIntro: Option[Name] = intros match {
    case Vector((n, Pis(ps, _))) if ps.size == numParams && level == Level.Zero => Some(n)
    case _ => None
  }

  val majorPremise = LocalConst(Binding("x", Apps(indTy, params ++ indices), BinderInfo.Default))

  val elimType: Expr = Pis(params ++ Seq(motive) ++ minorPremises ++ indices :+ majorPremise)(mkMotiveApp(indices, majorPremise))

  val elimLevelParams: Vector[Param] = extraElimLevelParams ++ univParams
  val elimDecl = Elim(Name.Str(name, "rec"), elimType, inductiveType, elimLevelParams,
    numParams = numParams, motive = numParams, numIndices = indices.size, numMinors = minorPremises.size,
    major = numParams + 1 + minorPremises.size + indices.size, depElim = useDepElim,
    kIntro = kIntro)

  val compRules: Vector[Expr] = intros.zip(minorPremises).map {
    case ((_, ty), minor) =>
      NormalizedPis.instantiate(ty, params) match {
        case NormalizedPis(arguments, Apps(Const(inductiveType.name, _), _)) =>
          val ihs = arguments.collect {
            case recArg @ LocalConst(Binding(_, NormalizedPis(eps, Apps(Const(inductiveType.name, _), indTyArgs)), _), _) =>
              Lams(eps)(Apps(Const(elimDecl.name, elimLevelParams), params ++ Seq(motive) ++ minorPremises ++ indTyArgs.drop(numParams) :+ Apps(recArg, eps)))
          }
          Lams(params ++ Seq(motive) ++ minorPremises ++ arguments)(
            Apps(minor, arguments ++ ihs)
          )
      }
  }

  val introDecls: Vector[Intro] =
    for (((n, t), cr) <- intros.zip(compRules))
      yield Intro(n, t, inductiveType, inductiveType.univParams, cr)

  val decls: Vector[Declaration] = inductiveType +: introDecls :+ elimDecl

  def check(): Unit = {
    for (introDecl <- introDecls)
      require(!introDecl.compRule.hasLocals && !introDecl.compRule.hasVars)
    val withType = env.addNow(inductiveType.asAxiom)
    val withIntros = introDecls.foldLeft(withType)((env, i) => { i.asAxiom.check(withType); env.addNow(i.asAxiom) })
    withIntros.addNow(elimDecl.asAxiom)
  }
}

final case class IndMod(inductiveType: InductiveType, numParams: Int, intros: Vector[(Name, Expr)]) extends Modification {
  def name: Name = inductiveType.name

  def compile(env: PreEnvironment) = CompiledIndMod(this, env)
}
