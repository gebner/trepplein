package trepplein

import trepplein.Level.{ IMax, Max, _ }

import scala.annotation.tailrec

sealed abstract class Level {
  def instantiate(subst: Map[Param, Level]): Level =
    this match {
      case Zero => Zero
      case Succ(level) => Succ(level.instantiate(subst))
      case Max(a, b) => Max(a.instantiate(subst), b.instantiate(subst))
      case IMax(a, b) => IMax(a.instantiate(subst), b.instantiate(subst))
      case p: Param => subst.getOrElse(p, p)
    }

  def univParams: Set[Param] =
    this match {
      case Zero => Set()
      case Succ(level) => level.univParams
      case Max(a, b) => a.univParams union b.univParams
      case IMax(a, b) => a.univParams union b.univParams
      case param: Param => Set(param)
    }
}

object Level {
  case object Zero extends Level
  case class Succ(level: Level) extends Level
  case class Max(a: Level, b: Level) extends Level
  case class IMax(a: Level, b: Level) extends Level
  case class Param(param: Name) extends Level

  implicit def ofNat(n: Int): Level = Offset(n, Zero)

  object Offset {
    def unapply(level: Level): Some[(Int, Level)] = {
      @tailrec
      def decompose(i: Int, level: Level): (Int, Level) =
        level match {
          case Succ(l) => decompose(i + 1, l)
          case _ => (i, level)
        }
      Some(decompose(0, level))
    }

    @tailrec
    def apply(i: Int, level: Level): Level =
      if (i == 0) level else apply(i - 1, Succ(level))
  }
}

object NLevel {
  trait Fun
  case class IMax(a: Max, b: Max) extends Fun
  case class Param(name: Name) extends Fun

  case class Max(n: Int = 0, ls: Map[Fun, Int] = Map()) {
    def max(a: Fun, off: Int): Max =
      copy(n = math.max(n, off), ls = ls + (a -> math.max(ls.getOrElse(a, 0), off)))

    def max(m: Int): Max = copy(n = math.max(m, n))

    def max(m: Max, off0: Int): Max =
      m.ls.foldLeft(this.max(m.n + off0)) { case (acc, (a, off)) => acc.max(a, off0 + off) }
    def max(m: Max): Max = max(m, 0)

    def isNonZero: Boolean = n > 0
    def isZero: Boolean = n == 0 && ls.isEmpty

    def flatMap(f: Fun => Max): Max =
      ls.foldLeft(Max(n)) { case (acc, (a, off)) => acc.max(f(a), off) }
  }
  object Max {
    implicit def apply(f: Fun): Max = Max().max(f, 0)
  }

  def subst(p: Param, by: Max, m: Max): Max = m.flatMap(subst(p, by, _))
  def subst(p: Param, by: Max, f: Fun): Max =
    f match {
      case IMax(a, b) => IMax(subst(p, by, a), subst(p, by, b))
      case `p` => by
      case _ => f
    }

  def simplify(m: Max): Max = m.flatMap(simplify)
  def simplify(fun: Fun): Max =
    fun match {
      case IMax(a, b) =>
        simplify(b) match {
          case b_ if b_.isZero => Max()
          case b_ if b_.isNonZero => simplify(a).max(simplify(b))
          case b_ =>
            simplify(a) match {
              case a_ if a_.isZero => b_
              case a_ => IMax(a_, b_)
            }
        }
      case p: Param => p
    }

  def toMax(level: Level): Max = toMax(level, 0, Max())
  def toMax(level: Level, off: Int, acc: Max): Max =
    level match {
      case Level.Zero =>
        acc.max(off)
      case Level.Succ(a) =>
        toMax(a, off + 1, acc)
      case Level.Max(a, b) =>
        toMax(b, off, toMax(a, off, acc))
      case Level.IMax(a, b) =>
        acc.max(IMax(toMax(a), toMax(b)), off)
      case Level.Param(param) =>
        acc.max(Param(param), off)
    }

  def toLevel(m: Max): Level = {
    val ls = m.ls.map { case (f, o) => Level.Offset(o, toLevel(f)) }
    if (m.ls.exists(_._2 >= m.n))
      ls.reduce(Level.Max)
    else
      ls.fold(Level.Offset(m.n, Level.Zero))(Level.Max)
  }
  def toLevel(f: Fun): Level =
    f match {
      case IMax(a, b) => Level.IMax(toLevel(a), toLevel(b))
      case Param(name) => Level.Param(name)
    }

  def getStuckReason(m: Max): Option[Param] = m.ls.view.flatMap(x => getStuckReason(x._1)).headOption
  def getStuckReason(f: Fun): Option[Param] =
    f match {
      case IMax(_, b) =>
        b.ls.view.collect {
          case (p: Param, 0) => p
        }.headOption.orElse(getStuckReason(b))
      case _ => None
    }

  def isEq(l1: Level, l2: Level): Boolean = l1 == l2 || isEq(toMax(l1), toMax(l2))
  def isEq(l1_ : Max, l2_ : Max): Boolean = {
    val l1 = simplify(l1_)
    val l2 = simplify(l2_)
    if (l1 == l2) return true
    getStuckReason(l1).orElse(getStuckReason(l2)) match {
      case Some(split) =>
        Seq(Max(), Max().max(split, 1)).forall { v =>
          isEq(subst(split, v, l1), subst(split, v, l2))
        }
      case None =>
        false
    }
  }

  def isNonZero(l: Level): Boolean = simplify(toMax(l)).isNonZero
  def isZero(l: Level): Boolean = simplify(toMax(l)).isZero
  def simplify(l: Level): Level = toLevel(simplify(toMax(l)))
}
