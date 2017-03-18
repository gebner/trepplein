package trepplein

import trepplein.BinderInfo._
import trepplein.Level._
import Doc._

sealed trait Notation
case class Infix(op: String) extends Notation
case class Prefix(op: String) extends Notation
case class Postfix(op: String) extends Notation

class PrettyPrinter(
    usedNames: Set[Name] = Set(),
    typeChecker: Option[TypeChecker] = None,
    notations: Map[Name, Notation] = Map(),
    hideProofs: Boolean = false,
    nestDepth: Int = 2
) {
  val MaxPrio = 1024

  def nest(doc: Doc): Doc = doc.group.nest(nestDepth)
  case class Parenable(prio: Int, doc: Doc) {
    def parens(newPrio: Int): Doc =
      if (newPrio > prio) "(" <> doc <> ")" else doc
  }

  def showImplicits: Boolean = typeChecker.nonEmpty

  def pp(n: Name): Doc = n.toString

  def pp(level: Level): Parenable =
    level match {
      case Offset(n, Zero) => Parenable(MaxPrio, n.toString)
      case Offset(n, l) if n > 0 =>
        Parenable(0, pp(l).parens(1) <> "+" <> n.toString)
      case Max(a, b) => Parenable(0, "max" <+> pp(a).parens(1) </> pp(b).parens(1))
      case IMax(a, b) => Parenable(0, "imax" <+> pp(a).parens(1) </> pp(b).parens(1))
      case Param(param) => Parenable(MaxPrio, pp(param))
    }

  def withFreshName(suggestion: Name): (Name, PrettyPrinter) =
    if (suggestion == Name.Anon) withFreshName(Name("a")) else {
      val fresh = (suggestion #:: Stream.from(0).map(Name.Num(suggestion, _): Name)).filterNot(usedNames).head
      (fresh, new PrettyPrinter(usedNames + fresh, typeChecker))
    }

  def withFreshLC(suggestion: LocalConst): (LocalConst, PrettyPrinter) = {
    val (fresh, this_) = withFreshName(suggestion.of.prettyName)
    (suggestion.copy(of = suggestion.of.copy(prettyName = fresh)), this_)
  }

  def pp(binding: Binding): Doc = {
    def bare = pp(binding.prettyName) <+> ":" </> pp(binding.ty).parens(1).group
    nest(binding.info match {
      case Default => bare
      case Implicit => "{" <> bare <> "}"
      case StrictImplicit => "{{" <> bare <> "}}"
      case InstImplicit => "[" <> bare <> "]"
    })
  }

  def isImplicit(fn: Expr): Boolean =
    typeChecker match {
      case Some(tc) =>
        try {
          tc.whnf(tc.infer(fn)) match {
            case Pi(dom, _) =>
              dom.info != BinderInfo.Default
            case _ => false
          }
        } catch { case _: Throwable => false }
      case _ => false
    }

  def pp(us: Traversable[Level]): Doc =
    ("{" <> stack(us.map(pp).map(_.parens(0))) <> "}").group

  def pp(e: Expr): Parenable =
    e match {
      case _ if hideProofs && typeChecker.exists(_.isProof(e)) => Parenable(MaxPrio, "_")
      case Var(idx) => Parenable(MaxPrio, s"#$idx")
      case Sort(level) if level.isZero => Parenable(MaxPrio, "Prop")
      case Sort(Succ(level)) => Parenable(MaxPrio, "Type" <+> pp(level).parens(MaxPrio))
      case Sort(level) => Parenable(MaxPrio, "Sort" <+> pp(level).parens(MaxPrio))
      case Const(name, _) if typeChecker.exists(_.env.get(name).nonEmpty) =>
        Parenable(MaxPrio, pp(name))
      case Const(name, levels) =>
        val univParams: Doc = if (levels.isEmpty) "" else ".{" <> pp(levels) <> "}"
        Parenable(MaxPrio, "@" <> pp(name) <> univParams)
      case LocalConst(of, _) => Parenable(MaxPrio, pp(of.prettyName))
      case Lam(domain, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        Parenable(0, ("λ" <+> pp(lc.of) <> "," </>
          this_.pp(body.instantiate(lc)).parens(0)).group)
      case Pi(domain, body) if !body.hasVars && domain.info == BinderInfo.Default =>
        Parenable(24, (pp(domain.ty).parens(25) <+> "→" </> pp(body).parens(24)).group)
      case Pi(domain, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        Parenable(0, ("∀" <+> pp(lc.of) <> "," </>
          this_.pp(body.instantiate(lc)).parens(0)).group)
      case Let(domain, value, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        Parenable(0, (nest("let" <+> pp(lc.of) <+> ":=" </> pp(value).parens(0).group <+> "in") </>
          this_.pp(body.instantiate(lc)).parens(0)).group)
      case App(_, _) =>
        def go(e: Expr): Doc =
          e match {
            case App(fn, _) if isImplicit(fn) => go(fn)
            case App(fn, a) => go(fn) </> pp(a).parens(MaxPrio).group
            case fn => pp(fn).parens(MaxPrio - 1).group
          }
        Parenable(MaxPrio - 1, nest(go(e)))
    }

  def pp(decl: Declaration): Doc =
    decl match {
      case Definition(name, univParams, ty, value, _) =>
        val ups: Doc = if (univParams.isEmpty) "" else " " <> pp(univParams)
        val isProp = typeChecker.exists(_.isProposition(ty))
        val cmd = if (isProp) "lemma" else "def"
        val ppVal: Doc = if (isProp && hideProofs) "_" else pp(value).parens(0).group
        cmd <> ups <+> nest(pp(name) <+> ":" </> pp(ty).parens(0).group <+> ":=") </> ppVal <> line
      case Axiom(name, univParams, ty) =>
        val ups: Doc = if (univParams.isEmpty) "" else " " <> pp(univParams)
        "axiom" <> ups <+> nest(pp(name) <+> ":" </> pp(ty).parens(0).group) <> line
      case _: Builtin =>
        "@[builtin]" <+> pp(decl.asAxiom)
    }
}

object pretty {
  def apply(e: Expr): String = new PrettyPrinter().pp(e).doc.group.render(lineWidth = 80)
}