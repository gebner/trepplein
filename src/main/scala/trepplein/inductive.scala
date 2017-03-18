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
  import tc.NormalizedPis

  def name: Name = inductiveType.name

  def univParams: Vector[Param] = inductiveType.univParams
  val indTy = Const(inductiveType.name, univParams)

  val ((params, indices), level) =
    inductiveType.ty match {
      case NormalizedPis(doms, Sort(lvl)) =>
        (doms.splitAt(numParams), lvl)
    }
  val indTyWParams = Apps(indTy, params)

  case class CompiledIntro(name: Name, ty: Expr) {
    val NormalizedPis(arguments, Apps(introType, introTyArgs)) = NormalizedPis.instantiate(ty, params)
    val introTyIndices: List[Expr] = introTyArgs.drop(numParams)

    type ArgInfo = Either[Expr, (List[LocalConst], List[Expr])]

    val argInfos: List[ArgInfo] = arguments.map {
      case LocalConst(Binding(_, NormalizedPis(eps, Apps(recArgIndTy @ Const(inductiveType.name, _), recArgs)), _), _) =>
        require(recArgs.size >= numParams)
        tc.requireDefEq(Apps(recArgIndTy, recArgs.take(numParams)), indTyWParams)
        Right((eps, recArgs.drop(numParams)))
      case nonRecArg => Left(nonRecArg)
    }

    lazy val ihs: Traversable[LocalConst] = (arguments, argInfos).zipped.collect {
      case (recArg, Right((eps, recIndices))) =>
        LocalConst(Binding("ih", Pis(eps)(mkMotiveApp(recIndices, Apps(recArg, eps))), BinderInfo.Default))
    }

    lazy val minorPremise = LocalConst(Binding("h", Pis(arguments ++ ihs)(mkMotiveApp(
      introTyIndices,
      Apps(Const(name, univParams), params ++ arguments)
    )), BinderInfo.Default))

    lazy val compRule: Expr = {
      val recCalls = arguments.zip(argInfos).collect {
        case (recArg, Right((eps, recArgIndices))) =>
          Lams(eps)(Apps(Const(elimDecl.name, elimLevelParams), params ++ Seq(motive) ++ minorPremises ++ recArgIndices :+ Apps(recArg, eps)))
      }
      Lams(params ++ Seq(motive) ++ minorPremises ++ arguments)(
        Apps(minorPremise, arguments ++ recCalls)
      )
    }

    def check(): Unit = {
      require(introTyArgs.size >= numParams)
      tc.requireDefEq(Apps(introType, introTyArgs.take(numParams)), Apps(indTy, params))

      val tc0 = new TypeChecker(env)
      arguments.zip(argInfos).foreach {
        case (_, Left(nonRecArg)) =>
          tc0.inferUniverseOfType(tc0.infer(nonRecArg))
        case (_, Right((eps, _))) =>
          for (e <- eps) tc0.inferUniverseOfType(tc0.infer(e))
      }

      require(!compRule.hasLocals)
      require(!compRule.hasVars)

      if (level.maybeNonZero) for (arg <- arguments) {
        val argLevel = tc.inferUniverseOfType(tc.infer(arg))
        require(argLevel <== level)
      }
    }
  }

  val compiledIntros: Vector[CompiledIntro] = intros.map(CompiledIntro.tupled)
  val kIntro: Option[Name] =
    compiledIntros match {
      case Vector(intro) if intro.arguments.isEmpty && level.isZero =>
        Some(intro.name)
      case _ => None
    }

  val elimIntoProp: Boolean = level.maybeZero &&
    (intros.size > 1 || compiledIntros.exists { intro =>
      intro.arguments.exists { arg => !tc.isProof(arg) && !intro.introTyArgs.contains(arg) }
    })
  val elimLevel: Level =
    if (elimIntoProp) Level.Zero
    else Level.Param(Name.fresh("l", univParams.map(_.param).toSet))
  val extraElimLevelParams: Vector[Param] =
    Vector(elimLevel).collect { case p: Level.Param => p }

  val useDepElim: Boolean = level.maybeNonZero
  val motiveType: Expr =
    if (useDepElim)
      Pis(indices :+ LocalConst(Binding("c", Apps(indTy, params ++ indices), BinderInfo.Default)))(Sort(elimLevel))
    else
      Pis(indices)(Sort(elimLevel))
  val motive = LocalConst(Binding("C", motiveType, BinderInfo.Implicit))
  def mkMotiveApp(indices: Seq[Expr], e: Expr): Expr =
    if (useDepElim) App(Apps(motive, indices), e) else Apps(motive, indices)

  val minorPremises: Vector[LocalConst] = compiledIntros.map { _.minorPremise }
  val majorPremise = LocalConst(Binding("x", Apps(indTy, params ++ indices), BinderInfo.Default))
  val elimType: Expr = Pis(params ++ Seq(motive) ++ minorPremises ++ indices :+ majorPremise)(mkMotiveApp(indices, majorPremise))
  val elimLevelParams: Vector[Param] = extraElimLevelParams ++ univParams
  val elimDecl = Elim(Name.Str(name, "rec"), elimType, inductiveType, elimLevelParams,
    numParams = numParams, motive = numParams, numIndices = indices.size, numMinors = minorPremises.size,
    major = numParams + 1 + minorPremises.size + indices.size, depElim = useDepElim,
    kIntro = kIntro)

  val introDecls: Vector[Intro] =
    for (i <- compiledIntros)
      yield Intro(i.name, i.ty, inductiveType, inductiveType.univParams, i.compRule)

  val decls: Vector[Declaration] = inductiveType +: introDecls :+ elimDecl

  def check(): Unit = {
    val withType = env.addNow(inductiveType.asAxiom)
    val withIntros = introDecls.foldLeft(withType)((env, i) => { i.asAxiom.check(withType); env.addNow(i.asAxiom) })
    withIntros.addNow(elimDecl.asAxiom)

    for (i <- compiledIntros) i.check()
  }
}

final case class IndMod(inductiveType: InductiveType, numParams: Int, intros: Vector[(Name, Expr)]) extends Modification {
  def name: Name = inductiveType.name

  def compile(env: PreEnvironment) = CompiledIndMod(this, env)
}
