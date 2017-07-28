package trepplein

object Quot {
  val name = Name("quot")
  val univParams = Vector(Level.Param(Name("u")))
  val A = LocalConst(Binding(Name("A"), Sort(univParams(0)), BinderInfo.Implicit))
  val R = LocalConst(Binding(Name("R"), A -->: A -->: Sort.Prop, BinderInfo.Default))
  val ty = Pis(A, R)(Sort(univParams(0)))
  val decl = Axiom(name, univParams, ty, builtin = true)
}
object QuotMk {
  val name = Name.Str(Quot.name, "mk")
  val univParams = Quot.univParams

  val A = Quot.A
  val R = Quot.R
  val ty = Pis(A, R)(A -->: Apps(Const(Quot.name, univParams), A, R))
  val decl = Axiom(name, univParams, ty, builtin = true)
}
object QuotLift {
  val name = Name.Str(Quot.name, "lift")
  val univParams = Quot.univParams :+ Level.Param(Name("v"))

  val A = Quot.A
  val R: LocalConst = LocalConst(Quot.R.of.copy(info = BinderInfo.Implicit))
  val B = LocalConst(Binding(Name("B"), Sort(univParams(1)), BinderInfo.Implicit))
  val f = LocalConst(Binding(Name("f"), A -->: B, BinderInfo.Default))
  val Seq(a, b) = Seq("a", "b").map(n => LocalConst(Binding(Name(n), A, BinderInfo.Default)))
  val ty = Pis(A, R, B, f)(
    Pis(a, b)(Apps(R, a, b) -->: Apps(Const(Name("eq"), Vector(univParams(1))), B, App(f, a), App(f, b))) -->:
      Apps(Const(Quot.name, Vector(univParams(0))), A, R) -->: B
  )
  val decl = Axiom(name, univParams, ty, builtin = true)
}
object QuotInd {
  val name = Name.Str(Quot.name, "ind")
  val univParams = Quot.univParams

  val A = Quot.A
  val R: LocalConst = LocalConst(Quot.R.of.copy(info = BinderInfo.Implicit))
  val B = LocalConst(Binding(Name("B"), Apps(Const(Quot.name, Vector(univParams(0))), A, R) -->: Sort.Prop, BinderInfo.Implicit))
  val a = LocalConst(Binding(Name("a"), A, BinderInfo.Default))
  val q = LocalConst(Binding(
    Name("q"),
    Apps(Const(Quot.name, Vector(univParams(0))), A, R), BinderInfo.Default
  ))
  val ty = Pis(A, R, B)(
    Pi(a, Apps(B, Apps(Const(QuotMk.name, Vector(univParams(0))), A, R, a))) -->:
      Pi(q, Apps(B, q))
  )
  val decl = Axiom(name, univParams, ty, builtin = true)
}

case object QuotMod extends Modification {
  def name: Name = Quot.name
  def compile(env: PreEnvironment) = new CompiledModification {
    val decls = Seq(Quot.decl, QuotMk.decl, QuotInd.decl, QuotLift.decl)

    override def check(): Unit = {
      // TODO: propext, eq
      decls.foldLeft(env)((env, decl) => env.addNow(decl.asAxiom))
    }

    val rules: Seq[ReductionRule] = {
      import QuotLift._
      val h = LocalConst(Binding(
        Name("h"),
        Apps(Const(Name("eq"), Vector(univParams(1))), B, App(f, a), App(f, b)), BinderInfo.Default
      ))
      Seq(
        ReductionRule(
          Vector(A, R, B, f, a, h),
          Apps(Const(QuotLift.name, univParams), A, R, B, f, h,
            Apps(Const(QuotMk.name, Vector(univParams(0))), A, R, a)),
          Apps(f, a),
          List()
        )
      )
    }
  }
}
