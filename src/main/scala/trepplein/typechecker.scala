package trepplein

import scala.collection.mutable

class TypeChecker(val env: PreEnvironment, val unsafeUnchecked: Boolean = false) {
  def shouldCheck: Boolean = !unsafeUnchecked

  object NormalizedPis {
    def unapply(e: Expr): Some[(List[LocalConst], Expr)] =
      whnf(e) match {
        case Pis(lcs1, f) if lcs1.nonEmpty =>
          val NormalizedPis(lcs2, g) = f
          Some((lcs1 ::: lcs2, g))
        case f => Some((Nil, f))
      }

    def instantiate(e: Expr, ts: List[Expr], ctx: List[Expr] = Nil): Expr =
      (e, ts) match {
        case (Pi(_, body), t :: ts_) =>
          instantiate(body, ts_, t :: ctx)
        case (_, _ :: _) =>
          instantiate(whnf(e).ensuring(_.isInstanceOf[Pi]), ts, ctx)
        case (_, Nil) => e.instantiate(0, ctx.toVector)
      }
  }

  private val levelDefEqCache = mutable.Map[(Level, Level), Boolean]()
  def isDefEq(a: Level, b: Level): Boolean =
    levelDefEqCache.getOrElseUpdate((a, b), a === b)

  def isProp(s: Expr): Boolean = whnf(s) match {
    case Sort(l) => l.isZero
    case _ => false
  }
  def isProposition(ty: Expr): Boolean = isProp(infer(ty))
  def isProof(p: Expr): Boolean = isProposition(infer(p))

  private def isProofIrrelevantEq(e1: Expr, e2: Expr): Boolean =
    isProof(e1) && isProof(e2)

  type DefEqRes = Option[(Expr, Expr)]
  private def reqDefEq(cond: Boolean, e1: Expr, e2: Expr) =
    if (cond) None else Some((e1, e2))

  def isDefEq(e1: Expr, e2: Expr): Boolean = checkDefEq(e1, e2).isEmpty

  def defHeight(fn: Expr, as: List[Expr]): Int =
    fn match {
      case Const(n, _) =>
        env.get(n) match {
          case Some(defn: Definition) => defn.height + 1
          case Some(_) => 1
          case None => 0
        }
      case _ => 0
    }

  private def reduceOneStep(e1: Expr, e2: Expr)(implicit transparency: Transparency): Option[(Expr, Expr)] = {
    val Apps(fn1, as1) = e1
    val Apps(fn2, as2) = e2

    def red1 = reduceOneStep(fn1, as1).map(_ -> e2)
    def red2 = reduceOneStep(fn2, as2).map(e1 -> _)

    if (defHeight(fn1, as1) > defHeight(fn2, as2))
      red1 orElse red2
    else
      red2 orElse red1
  }

  private def checkDefEqCore(e1_0: Expr, e2_0: Expr): DefEqRes = {
    val transparency = Transparency(reduce = false)
    val e1 @ Apps(fn1, as1) = whnfCore(e1_0)(transparency)
    val e2 @ Apps(fn2, as2) = whnfCore(e2_0)(transparency)
    def checkArgs: DefEqRes =
      reqDefEq(as1.size == as2.size, e1, e2) orElse
        (as1, as2).zipped.view.flatMap { case (a1, a2) => checkDefEq(a1, a2) }.headOption
    ((fn1, fn2) match {
      case (Sort(l1), Sort(l2)) =>
        return reqDefEq(isDefEq(l1, l2) && as1.isEmpty && as2.isEmpty, e1, e2)
      case (Const(c1, ls1), Const(c2, ls2)) if c1 == c2 && (ls1, ls2).zipped.forall(isDefEq) =>
        checkArgs
      case (LocalConst(_, i1), LocalConst(_, i2)) if i1 == i2 =>
        checkArgs
      case (Lam(dom, b1), Lam(_, b2)) =>
        require(as1.isEmpty && as2.isEmpty)
        val lc = LocalConst(dom)
        return checkDefEqCore(b1.instantiate(lc), b2.instantiate(lc))
      case (Lam(dom1, _), _) =>
        require(as1.isEmpty)
        return checkDefEqCore(e1, Lam(dom1, App(e2, Var(0))))
      case (_, Lam(dom2, _)) =>
        require(as2.isEmpty)
        return checkDefEqCore(Lam(dom2, App(e1, Var(0))), e2)
      case (Pi(dom1, b1), Pi(dom2, b2)) =>
        val lc = LocalConst(dom1)
        require(as1.isEmpty && as2.isEmpty)
        return checkDefEq(dom1.ty, dom2.ty) orElse checkDefEqCore(b1.instantiate(lc), b2.instantiate(lc))
      case (_, _) =>
        Some((e1, e2))
    }) match {
      case None => None
      case d @ Some(_) =>
        reduceOneStep(e1, e2)(Transparency.all) match {
          case Some((e1_, e2_)) =>
            checkDefEqCore(e1_, e2_)
          case None => d
        }
    }
  }

  private val defEqCache = mutable.Map[(Expr, Expr), DefEqRes]()
  // requires that e1 and e2 have the same type, or are types
  def checkDefEq(e1: Expr, e2: Expr): DefEqRes =
    if (e1.eq(e2) || e1 == e2) None else defEqCache.getOrElseUpdate((e1, e2), {
      if (isProofIrrelevantEq(e1, e2)) None else checkDefEqCore(e1, e2)
    })

  case class Transparency(reduce: Boolean) {
    def canReduceConstants: Boolean = reduce
  }
  object Transparency {
    val all = Transparency(reduce = true)
  }

  def reduceOneStep(e: Expr)(implicit transparency: Transparency): Option[Expr] =
    e match { case Apps(fn, as) => reduceOneStep(fn, as) }
  private val reductionRuleCache = new ReductionRuleCache {
    private val instantiationCache = mutable.Map[(ReductionRule, Map[Level.Param, Level]), Expr]()
    override def instantiation(rr: ReductionRule, subst: Map[Level.Param, Level], v: => Expr): Expr =
      instantiationCache.getOrElseUpdate((rr, subst), v)
  }
  def reduceOneStep(fn: Expr, as0: List[Expr])(implicit transparency: Transparency): Option[Expr] =
    fn match {
      case _ if !transparency.reduce => None
      case Const(n, _) =>
        val major = env.reductions.major(n)
        val as = for ((a, i) <- as0.zipWithIndex)
          yield if (major(i)) whnf(a) else a
        env.reductions.apply(Apps(fn, as))(reductionRuleCache) match {
          case Some((result, constraints)) if constraints.forall { case (a, b) => isDefEq(a, b) } =>
            Some(result)
          case _ => None
        }
      case _ => None
    }

  private val whnfCache = mutable.Map[Expr, Expr]()
  def whnf(e: Expr): Expr = whnfCache.getOrElseUpdate(e, whnfCore(e)(Transparency.all))
  def whnfCore(e: Expr)(implicit transparency: Transparency = Transparency.all): Expr = {
    val Apps(fn, as) = e
    fn match {
      case Sort(l) => Sort(l.simplify)
      case Lam(_, _) if as.nonEmpty =>
        def go(fn: Expr, ctx: List[Expr], as: List[Expr]): Expr =
          (fn, as) match {
            case (Lam(_, fn_), a :: as_) => go(fn_, a :: ctx, as_)
            case _ => Apps(fn.instantiate(0, ctx.toVector), as)
          }
        whnfCore(go(fn, Nil, as))
      case Let(_, value, body) =>
        // TODO: zeta
        whnfCore(Apps(body.instantiate(value), as))
      case Const(_, _) if transparency.canReduceConstants =>
        reduceOneStep(fn, as) match {
          case Some(e_) => whnfCore(e_)
          case None => e
        }
      case _ => e
    }
  }

  def checkType(e: Expr, ty: Expr): Unit = {
    val inferredTy = infer(e)
    for ((t_, i_) <- checkDefEq(ty, inferredTy))
      throw new IllegalArgumentException(s"wrong type: $e : $ty\ninferred type: $inferredTy\n$t_ !=def $i_")
  }
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
    case Apps(fn, as) if as.nonEmpty =>
      def go(fnt: Expr, as: List[Expr], ctx: List[Expr]): Expr =
        (fnt, as) match {
          case (_, Nil) => fnt.instantiate(0, ctx.toVector)
          case (Pi(dom, body), a :: as_) =>
            if (shouldCheck) checkType(a, dom.ty.instantiate(0, ctx.toVector))
            go(body, as_, a :: ctx)
          case (_, _ :: _) =>
            whnf(fnt.instantiate(0, ctx.toVector)) match {
              case fnt_ @ Pi(_, _) => go(fnt_, as, Nil)
              case _ =>
                throw new IllegalArgumentException(s"not a function type: $fnt")
            }
        }
      go(infer(fn), as, Nil)
    case Lam(_, _) =>
      def go(e: Expr, ctx: List[LocalConst]): Expr = e match {
        case Lam(dom, body) =>
          val dom_ = dom.instantiate(0, ctx.toVector)
          if (shouldCheck) inferUniverseOfType(dom_.ty)
          Pi(dom, go(body, LocalConst(dom_) :: ctx))
        case _ =>
          val ctxVec = ctx.toVector
          infer(e.instantiate(0, ctxVec)).abstr(0, ctxVec)
      }
      go(e, Nil)
    case Pis(domains, body) if domains.nonEmpty =>
      Sort(domains.map(d => inferUniverseOfType(d.of.ty)).
        foldRight(inferUniverseOfType(body))(Level.IMax).simplify)
    case Let(domain, value, body) =>
      if (shouldCheck) inferUniverseOfType(domain.ty)
      if (shouldCheck) checkType(value, domain.ty)
      infer(body.instantiate(value))
  })
}