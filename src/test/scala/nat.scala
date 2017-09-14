package trepplein

import org.specs2.mutable._

class NatTest extends Specification {
  val nat = Const("nat", Vector())
  val natZero = Const(Name("nat", "zero"), Vector())
  val natSucc = Const(Name("nat", "succ"), Vector())

  val natAdd = Const(Name("nat", "add"), Vector())
  def addDef = {
    val x = LocalConst(Binding("x", nat, BinderInfo.Default))
    val y = LocalConst(Binding("y", nat, BinderInfo.Default))
    Lam(x, Apps(
      Const(Name("nat", "rec"), Vector(1)),
      Lam(y, nat), x, Lam(y, natSucc)))
  }

  val eqDef = {
    val u = Level.Param("u")
    val alpha = LocalConst(Binding("A", Sort(u), BinderInfo.Default))
    val x = LocalConst(Binding("x", alpha, BinderInfo.Default))
    val y = LocalConst(Binding("y", alpha, BinderInfo.Default))
    IndMod(InductiveType("eq", Vector(u), Pi(alpha, alpha -->: alpha -->: Sort.Prop)), 2,
      Vector(Name("eq", "refl") -> Pis(alpha, x)(Apps(Const("eq", Vector(u)), alpha, x, x))))
  }

  def env_ =
    Environment.default
      .addNow(eqDef)
      .addNow(IndMod(
        InductiveType(nat.name, Vector(), Sort(1)),
        0, Vector(natZero.name -> nat, natSucc.name -> (nat -->: nat))))
      .addNow(DefMod(Definition(natAdd.name, Vector(), nat -->: nat -->: nat, addDef)))

  def numeral(n: Int): Expr =
    if (n == 0) Const(Name("nat", "zero"), Vector())
    else App(Const(Name("nat", "succ"), Vector()), numeral(n - 1))

  def tc = new TypeChecker(env_)

  "add" in {
    val t = Apps(natAdd, numeral(2), numeral(4))
    tc.checkDefEq(tc.infer(t), nat) must beLike { case IsDefEq => ok }
    tc.checkDefEq(t, numeral(6)) must beLike { case IsDefEq => ok }
    tc.checkDefEq(t, numeral(7)) must beLike { case NotDefEq(_, _) => ok }
  }

  "infer zeta" in {
    val x = LocalConst(Binding("x", nat, BinderInfo.Default))
    val b = Let(x, numeral(0), Apps(Const("eq.refl", Vector(1)), nat, x))
    b.hasLocals must_== false
    val ty = tc.infer(b)
    ty.hasLocals must_== false
  }
}