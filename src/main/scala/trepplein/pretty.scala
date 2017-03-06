package trepplein

import trepplein.BinderInfo.{ Default, Implicit, InstImplicit, StrictImplicit }
import trepplein.Level._

class PrettyPrinter(usedNames: Set[Name], typeChecker: Option[TypeChecker] = None) {
  def pp(n: Name): String = n.toString

  def pp(level: Level): String =
    level match {
      case Offset(n, Zero) => n.toString
      case Offset(n, l) if n > 0 => s"(${pp(l)}+$n)"
      case Max(a, b) => s"(max ${pp(a)} ${pp(b)})"
      case IMax(a, b) => s"(imax ${pp(a)} ${pp(b)})"
      case Param(param) => pp(param)
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

  def pp(binding: Binding): String = {
    def bare = s"${pp(binding.prettyName)} : ${pp(binding.ty)}"
    binding.info match {
      case Default => bare
      case Implicit => s"{$bare}"
      case StrictImplicit => s"{{$bare}}"
      case InstImplicit => s"[$bare]"
    }
  }

  def pp(e: Expr): String =
    e match {
      case Var(idx) => s"#$idx"
      case Sort(level) => s"Sort ${pp(level)}"
      case Const(name, Vector()) => s"@${pp(name)}"
      case Const(name, levels) => s"@${pp(name)}.{${levels.map(pp).mkString(" ")}}"
      case LocalConst(of, _) => s"${of.prettyName}"
      case Lam(domain, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        s"(fun ${pp(lc.of.prettyName)} : ${pp(lc.of.ty)}, ${this_.pp(body.instantiate(lc))})"
      case Pi(domain, body) if !body.hasVars && domain.info == BinderInfo.Default =>
        s"(${pp(domain.ty)} -> ${pp(body)})"
      case Pi(domain, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        s"(Pi ${pp(lc.of)}, ${this_.pp(body.instantiate(lc))})"
      case Let(domain, value, body) =>
        val (lc, this_) = withFreshLC(LocalConst(domain))
        s"(let ${pp(lc.of)} := ${pp(value)} in ${this_.pp(body.instantiate(lc))})"
      case Apps(fn, as) =>
        s"($fn ${as.map(pp).mkString(" ")})"
    }
}

object pretty {
  def apply(e: Expr): String = new PrettyPrinter(Set()).pp(e)
}