package trepplein

import scala.collection.mutable

class TypeChecker(env: PreEnvironment) {
  private val levelDefEqCache = mutable.Map[(Level, Level), Boolean]()
  def isDefEq(a: Level, b: Level): Boolean =
    levelDefEqCache.getOrElseUpdate((a, b), a === b)

  def checkDefEq(dom1: Binding, dom2: Binding): DefEqRes =
    checkDefEq(dom1.ty, dom2.ty)

  def isProp(s: Expr): Boolean = whnf(s) match {
    case Sort(l) => l.isZero
    case _ => false
  }
  def isProposition(ty: Expr): Boolean = isProp(infer(ty))
  def isProof(p: Expr): Boolean = isProposition(infer(p))

  private def isProofIrrelevantEq(e1: Expr, e2: Expr): Boolean =
    try {
      isProof(e1) && isProof(e2) && checkDefEq(infer(e1), infer(e2)).isEmpty
    } catch { case _: Throwable => false }

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

  private def reduceOneStep(e1: Expr, e2: Expr): Option[(Expr, Expr)] = {
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
    val e1 @ Apps(fn1, as1) = whnfCore(e1_0)(Transparency.None)
    val e2 @ Apps(fn2, as2) = whnfCore(e2_0)(Transparency.None)
    if (e1 == e2) return None
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
      case (Lam(dom1, b1), Lam(dom2, b2)) =>
        require(as1.isEmpty && as2.isEmpty)
        val lc = LocalConst(dom1)
        return checkDefEq(dom1, dom2) orElse checkDefEq(b1.instantiate(lc), b2.instantiate(lc))
      case (Lam(dom1, _), _) =>
        require(as1.isEmpty)
        return checkDefEqCore(e1, Lam(dom1, App(e2, Var(0))))
      case (_, Lam(dom2, _)) =>
        require(as2.isEmpty)
        return checkDefEqCore(Lam(dom2, App(e1, Var(0))), e2)
      case (Pi(dom1, b1), Pi(dom2, b2)) =>
        val lc = LocalConst(dom1)
        return reqDefEq(as1.isEmpty && as2.isEmpty, e1, e2) orElse checkDefEq(dom1, dom2) orElse checkDefEq(b1.instantiate(lc), b2.instantiate(lc))
      case (_, _) =>
        Some((e1, e2))
    }) match {
      case None => None
      case d @ Some(_) =>
        reduceOneStep(e1, e2) match {
          case Some((e1_, e2_)) =>
            checkDefEqCore(e1_, e2_)
          case None => d
        }
    }
  }

  private val defEqCache = mutable.Map[(Expr, Expr), DefEqRes]()
  def checkDefEq(e1: Expr, e2: Expr): DefEqRes =
    if (e1.eq(e2)) None else defEqCache.getOrElseUpdate((e1, e2), {
      checkDefEqCore(e1, e2).filter(_ => !isProofIrrelevantEq(e1, e2))
    })

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
          case _ => whnf(major)
        }
      case None => whnf(major)
    }

  sealed trait Transparency
  object Transparency {
    case object None extends Transparency
    case object All extends Transparency
  }

  def reduceOneStep(e: Expr): Option[Expr] =
    e match { case Apps(fn, as) => reduceOneStep(fn, as) }
  def reduceOneStep(fn: Expr, as: List[Expr]): Option[Expr] = fn match {
    case Const(name, levels) =>
      env.get(name) match {
        case Some(defn: Definition) =>
          Some(Apps(defn.value.instantiate(defn.univParams.zip(levels).toMap), as))
        case Some(elim: Elim) =>
          for {
            major <- as.drop(elim.major).headOption
            Apps(Const(introC, _), introArgs) <- Some(whnfK(major, elim))
            Intro(_, _, indTy, _, compRule) <- env.get(introC)
            if indTy.name == elim.ind.name
          } yield Apps(
            compRule.instantiate(elim.univParams.zip(levels).toMap),
            as.take(elim.numParams + 1 + elim.numMinors) ++ introArgs.drop(elim.numParams) ++ as.drop(elim.major + 1)
          )
        case Some(QuotLift) if as.size >= 6 =>
          whnf(as(5)) match {
            case Apps(Const(quotMk, _), mkArgs) if env.get(quotMk).contains(QuotMk) =>
              Some(Apps(App(as(3), mkArgs(2)), as.drop(6)))
            case _ =>
              None
          }
        case _ => None
      }
    case _ => None
  }

  private val whnfCache = mutable.Map[Expr, Expr]()
  def whnf(e: Expr): Expr = whnfCache.getOrElseUpdate(e, whnfCore(e)(Transparency.All))
  def whnfCore(e: Expr)(implicit transparency: Transparency = Transparency.All): Expr = {
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
      case Const(_, _) if transparency == Transparency.All =>
        reduceOneStep(fn, as) match {
          case Some(e_) => whnfCore(e_)
          case None => e
        }
      case _ => e
    }
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
            requireDefEq(dom.ty.instantiate(0, ctx.toVector), infer(a))
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
          inferUniverseOfType(dom_.ty)
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
      inferUniverseOfType(domain.ty)
      requireDefEq(domain.ty, infer(value))
      infer(body.instantiate(value))
  })
}