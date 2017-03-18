package trepplein

import trepplein.BinderInfo._
import trepplein.Level._
import Doc._

class PrettyPrinter(
    usedNames: Set[Name] = Set(),
    typeChecker: Option[TypeChecker] = None,
    nestDepth: Int = 2
) {
  val MaxPrio = 1024

  def nest(doc: Doc): Doc = Nest(nestDepth, Group(doc))
  case class Parenable(prio: Int, doc: Doc) {
    def parens(newPrio: Int): Doc =
      if (newPrio > prio) "(" <> doc <> ")" else doc
  }

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
    def bare = pp(binding.prettyName) <+> ":" </> pp(binding.ty).parens(1)
    binding.info match {
      case Default => bare
      case Implicit => "{" <> bare <> "}"
      case StrictImplicit => "{{" <> bare <> "}}"
      case InstImplicit => "[" <> bare <> "]"
    }
  }

  def pp(e: Expr): Parenable =
    e match {
      case Var(idx) => Parenable(MaxPrio, s"#$idx")
      case Sort(level) => Parenable(MaxPrio, "Sort" <+> pp(level).parens(MaxPrio))
      case Const(name, Vector()) => Parenable(MaxPrio, "@" <> pp(name))
      case Const(name, levels) =>
        Parenable(MaxPrio, Group("@" <> pp(name) <> ".{" <> stack(levels.map(pp).map(_.parens(0))) <> "}"))
      case LocalConst(of, _) => Parenable(MaxPrio, pp(of.prettyName))
      case Lam(domain, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        Parenable(0, "fun" <+> nest(pp(lc.of.prettyName) <+> ":" </> pp(lc.of.ty).parens(1)) <> "," </>
          this_.pp(body.instantiate(lc)).parens(0))
      case Pi(domain, body) if !body.hasVars && domain.info == BinderInfo.Default =>
        Parenable(24, pp(domain.ty).parens(25) <+> "->" </> pp(body).parens(24))
      case Pi(domain, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        Parenable(0, "Pi" <+> nest(pp(lc.of.prettyName) <+> ":" </> pp(lc.of.ty).parens(1)) <> "," </>
          this_.pp(body.instantiate(lc)).parens(0))
      case Let(domain, value, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        Parenable(0, "let" <+> nest(pp(lc.of.prettyName) <+> ":=" </> pp(value).parens(0) <+> "in") </>
          this_.pp(body.instantiate(lc)).parens(0))
      case Apps(fn, as) if as.nonEmpty =>
        Parenable(MaxPrio - 1, nest(pp(fn).parens(MaxPrio) </> stack(as.map(pp).map(_.parens(MaxPrio)))))
    }
}

object pretty {
  def apply(e: Expr): String = new PrettyPrinter().pp(e).doc.render(lineWidth = 80)
}