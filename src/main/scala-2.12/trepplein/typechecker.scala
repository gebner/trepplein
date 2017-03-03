package trepplein

import scala.collection.mutable

class TypeChecker(env: PreEnvironment) {
  def isDefEq(a: Level, b: Level): Boolean = NLevel.isEq(a, b)

  def isDefEq(dom1: Binding, dom2: Binding): Boolean =
    //    dom1.info == dom2.info && TODO
    isDefEq(dom1.ty, dom2.ty)

  private def checkProofIrrelevantEq(e1: Expr, e2: Expr): Boolean =
    (whnf(infer(infer(e1))), whnf(infer(infer(e2)))) match {
      case (Sort(l1), Sort(l2)) if NLevel.isZero(l1) && NLevel.isZero(l2) =>
        true
      case (_, _) =>
        false
    }

  private val defEqCache = mutable.Map[(Expr, Expr), Boolean]()
  def isDefEq(e1: Expr, e2: Expr): Boolean =
    e1.eq(e2) || defEqCache.getOrElseUpdate((e1, e2), ((whnf(e1), whnf(e2)) match {
      case (Sort(l1), Sort(l2)) =>
        isDefEq(l1, l2)
      case (Const(c1, ls1), Const(c2, ls2)) =>
        require(c1 == c2)
        require(ls1.size == ls2.size)
        c1 == c2 && ls1.size == ls2.size && (ls1, ls2).zipped.forall(isDefEq)
      case (LocalConst(_, i1), LocalConst(_, i2)) =>
        i1 == i2
      case (App(a1, b1), App(a2, b2)) =>
        isDefEq(a1, a2) && isDefEq(b1, b2)
      case (Lam(dom1, b1), Lam(dom2, b2)) =>
        val lc = LocalConst(dom1)
        isDefEq(dom1, dom2) && isDefEq(b1.instantiate(lc), b2.instantiate(lc))
      case (e1_ @ Lam(dom1, _), e2_) =>
        isDefEq(e1_, Lam(dom1, App(e2_, Var(0))))
      case (e1_, e2_ @ Lam(dom2, _)) =>
        isDefEq(Lam(dom2, App(e1_, Var(0))), e2_)
      case (Pi(dom1, b1), Pi(dom2, b2)) =>
        val lc = LocalConst(dom1)
        isDefEq(dom1, dom2) && isDefEq(b1.instantiate(lc), b2.instantiate(lc))
      case (_, _) =>
        false
    }) || checkProofIrrelevantEq(e1, e2))

  private def whnfK(major: Expr, elim: Elim): Expr = {
    elim.kIntro match {
      case Some(i) =>
        whnf(infer(major)) match {
          case majorTy @ Apps(Const(_, univParams), as) =>
            val synthIntro = Apps(Const(i, univParams), as.take(elim.numParams))
            if (isDefEq(infer(synthIntro), majorTy)) {
              synthIntro
            } else {
              major
            }
        }
      case None => major
    }
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
            val e_ = (for {
              major <- as.drop(elim.major).headOption
              Apps(Const(introC, _), introArgs) <- Some(whnfK(major, elim))
              Intro(_, _, indTy, _, compRule) <- env.get(introC)
              _ = require(indTy.name == elim.ind.name, "inductive type does not match")
            } yield whnf(
              Apps(
                compRule.instantiate(elim.univParams.zip(levels).toMap),
                as.take(elim.numParams + 1 + elim.numMinors) ++ introArgs.drop(elim.numParams) ++ as.drop(elim.major + 1)
              )
            )).getOrElse(e)
            require(isDefEq(infer(e), infer(e_)))
            e_
          case Some(_) => e
        }
      case _: Var | _: LocalConst | _: Lam | _: Pi => e
    }
  })

  def requireDefEq(a: Expr, b: Expr): Unit = require(isDefEq(a, b), s"\n$a =def\n$b")

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
      require(whnf(infer(domain.ty)).isInstanceOf[Sort])
      val lc = LocalConst(domain)
      Pi(domain, infer(body.instantiate(lc)).abstr(lc))
    case Pi(domain, body) =>
      val lc = LocalConst(domain)
      (whnf(infer(domain.ty)), whnf(infer(body.instantiate(lc)))) match {
        case (Sort(l1), Sort(l2)) =>
          Sort(NLevel.simplify(Level.IMax(l1, l2)))
      }
    case Let(domain, value, body) =>
      require(infer(domain.ty).isInstanceOf[Sort])
      requireDefEq(domain.ty, infer(value))
      infer(body.instantiate(value))
  })
}