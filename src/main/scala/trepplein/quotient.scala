package trepplein

case object Quot extends Builtin {
  val name = Name("quot")
  val univParams = Vector(Level.Param(Name("u")))
  val A = LocalConst(Binding(Name("A"), Sort(univParams(0)), BinderInfo.Implicit))
  val R = LocalConst(Binding(Name("R"), A -->: A -->: Sort.Prop, BinderInfo.Default))
  val ty = Pis(A, R)(Sort(univParams(0)))
}
case object QuotMk extends Builtin {
  val name = Name.Str(Quot.name, "mk")
  val univParams = Quot.univParams

  val A = Quot.A
  val R = Quot.R
  val ty = Pis(A, R)(A -->: Apps(Const(Quot.name, univParams), A, R))
}
case object QuotLift extends Builtin {
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
}
case object QuotInd extends Builtin {
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
}

case object QuotMod extends Modification {
  def name = Quot.name
  override def declsFor(env: PreEnvironment) = Seq(Quot, QuotMk, QuotInd, QuotLift)
  override def check(env: PreEnvironment): Unit = {
    // TODO: propext, eq
    declsFor(env).foldLeft(env)((env, decl) => env.addNow(decl.asAxiom))
  }
}
