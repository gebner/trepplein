package trepplein

import scala.collection.mutable

class TypeChecker(env: PreEnvironment) {
  def isDefEq(a: Level, b: Level): Boolean = NLevel.isEq(a, b)

  def checkDefEq(dom1: Binding, dom2: Binding): DefEqRes =
    checkDefEq(dom1.ty, dom2.ty)

  def isProp(s: Expr): Boolean = whnf(s) match {
    case Sort(Level.Zero) => true
    case _ => false
  }
  def isProposition(ty: Expr): Boolean = isProp(infer(ty))
  def isProof(p: Expr): Boolean = isProposition(infer(p))

  private def isProofIrrelevantEq(e1: Expr, e2: Expr): Boolean =
    isProof(e1) && isProof(e2) && checkDefEq(infer(e1), infer(e2)).isEmpty

  type DefEqRes = Option[(Expr, Expr)]
  private def reqDefEq(cond: Boolean, e1: Expr, e2: Expr) =
    if (cond) None else Some((e1, e2))

  def isDefEq(e1: Expr, e2: Expr): Boolean = checkDefEq(e1, e2).isEmpty

  private val defEqCache = mutable.Map[(Expr, Expr), DefEqRes]()
  def checkDefEq(e1: Expr, e2: Expr): DefEqRes =
    if (e1.eq(e2)) None else defEqCache.getOrElseUpdate((e1, e2), ((whnf(e1), whnf(e2)) match {
      case (Sort(l1), Sort(l2)) =>
        reqDefEq(isDefEq(l1, l2), e1, e2)
      case (Const(c1, ls1), Const(c2, ls2)) =>
        reqDefEq(c1 == c2 && ls1.size == ls2.size && (ls1, ls2).zipped.forall(isDefEq), e1, e2)
      case (LocalConst(_, i1), LocalConst(_, i2)) =>
        reqDefEq(i1 == i2, e1, e2)
      case (App(a1, b1), App(a2, b2)) =>
        checkDefEq(infer(a1), infer(a2)) orElse checkDefEq(a1, a2) orElse checkDefEq(b1, b2)
      case (Lam(dom1, b1), Lam(dom2, b2)) =>
        val lc = LocalConst(dom1)
        checkDefEq(dom1, dom2) orElse checkDefEq(b1.instantiate(lc), b2.instantiate(lc))
      case (e1_ @ Lam(dom1, _), e2_) =>
        checkDefEq(e1_, Lam(dom1, App(e2_, Var(0))))
      case (e1_, e2_ @ Lam(dom2, _)) =>
        checkDefEq(Lam(dom2, App(e1_, Var(0))), e2_)
      case (Pi(dom1, b1), Pi(dom2, b2)) =>
        val lc = LocalConst(dom1)
        checkDefEq(dom1, dom2) orElse checkDefEq(b1.instantiate(lc), b2.instantiate(lc))
      case (e1_, e2_) =>
        Some((e1_, e2_))
    }).filter(_ => !isProofIrrelevantEq(e1, e2)))

  private def whnfK(major: Expr, elim: Elim): Expr =
    elim.kIntro match {
      case Some(i) =>
        whnf(infer(major)) match {
          case majorTy @ Apps(Const(_, univParams), as) =>
            val synthIntro = Apps(Const(i, univParams), as.take(elim.numParams))
            if (isDefEq(infer(synthIntro), majorTy))
              synthIntro
            else
              whnf(major)
        }
      case None => whnf(major)
    }

  private val whnfCache = mutable.Map[Expr, Expr]()
  def whnf(e: Expr): Expr = whnfCache.getOrElseUpdate(e, {
    val Apps(fn, as) = e
    fn match {
      case Sort(l) => Sort(NLevel.simplify(l))
      case Lam(_, body) if as.nonEmpty =>
        whnf(Apps(body.instantiate(as.head), as.tail))
      case Let(_, value, body) =>
        // TODO: zeta
        whnf(Apps(body.instantiate(value), as))
      case Const(name, levels) =>
        env.get(name) match {
          case Some(defn: Definition) =>
            whnf(Apps(defn.value.instantiate(defn.univParams.zip(levels).toMap), as))
          case Some(elim: Elim) =>
            (for {
              major <- as.drop(elim.major).headOption
              Apps(Const(introC, _), introArgs) <- Some(whnfK(major, elim))
              Intro(_, _, indTy, _, compRule) <- env.get(introC)
              if indTy.name == elim.ind.name
            } yield whnf(
              Apps(
                compRule.instantiate(elim.univParams.zip(levels).toMap),
                as.take(elim.numParams + 1 + elim.numMinors) ++ introArgs.drop(elim.numParams) ++ as.drop(elim.major + 1)
              )
            )).getOrElse(e)
          case Some(QuotLift) if as.size >= 6 =>
            whnf(as(5)) match {
              case Apps(Const(quotMk, _), mkArgs) if env.get(quotMk).contains(QuotMk) =>
                whnf(Apps(App(as(3), mkArgs(2)), as.drop(6)))
              case _ =>
                e
            }
          case _ => e
        }
      case _: Var | _: LocalConst | _: Lam | _: Pi => e
    }
  })

  def requireDefEq(a: Expr, b: Expr): Unit =
    for ((a_, b_) <- checkDefEq(a, b))
      throw new IllegalArgumentException(s"\n$a_ =def\n$b_")

  def inferUniverseOfType(ty: Expr): Level =
    whnf(infer(ty)) match {
      case Sort(l) => l
      case s => throw new IllegalArgumentException(s"not a sort: $s")
    }

  private val inferCache = mutable.Map[Expr, Expr]()
  def infer(e: Expr): Expr = inferCache.getOrElseUpdate(e, e match {
    case Var(_) =>
      throw new IllegalArgumentException
    case Sort(level) =>
      Sort(Level.Succ(level))
    case Const(name, levels) =>
      val decl = env(name)
      require(
        decl.univParams.size == levels.size,
        s"incorrect number of universe parameters: $e, expected ${decl.univParams}"
      )
      decl.ty.instantiate(decl.univParams.zip(levels).toMap)
    case LocalConst(of, _) =>
      of.ty
    case App(a, b) =>
      whnf(infer(a)) match {
        case Pi(domain, body) =>
          requireDefEq(domain.ty, infer(b))
          body.instantiate(b)
        case a_ =>
          throw new IllegalArgumentException(s"not a function: $a_")
      }
    case Lam(domain, body) =>
      inferUniverseOfType(domain.ty)
      val lc = LocalConst(domain)
      Pi(domain, infer(body.instantiate(lc)).abstr(lc))
    case Pi(domain, body) =>
      val lc = LocalConst(domain)
      Sort(NLevel.simplify(Level.IMax(inferUniverseOfType(domain.ty), inferUniverseOfType(body.instantiate(lc)))))
    case Let(domain, value, body) =>
      inferUniverseOfType(domain.ty)
      requireDefEq(domain.ty, infer(value))
      infer(body.instantiate(value))
  })
}