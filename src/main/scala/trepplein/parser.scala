package trepplein

import scala.collection.mutable

class TextExportParser {
  val name: mutable.Map[Int, Name] = mutable.Map[Int, Name]()
  val level: mutable.Map[Int, Level] = mutable.Map[Int, Level]()
  val expr: mutable.Map[Int, Expr] = mutable.Map[Int, Expr]()

  name(0) = Name.Anon
  level(0) = Level.Zero

  def univParams(is: Seq[String]): Vector[Level.Param] =
    is.view.map(_.toInt).map(name).map(Level.Param).toVector

  def parseBinderInfo(tok: String): BinderInfo =
    tok match {
      case "#BD" => BinderInfo.Default
      case "#BI" => BinderInfo.Implicit
      case "#BC" => BinderInfo.InstImplicit
      case "#BS" => BinderInfo.StrictImplicit
    }
  def parseBinding(b: String, n: String, t: String): Binding =
    Binding(name(n.toInt), expr(t.toInt), parseBinderInfo(b))

  def parseTermDef(toks: Array[String]): Unit =
    toks match {
      case Array(i, "#NS", par, rest @ _*) => name(i.toInt) = Name.Str(name(par.toInt), rest.mkString(" "))
      case Array(i, "#NI", par, num) => name(i.toInt) = Name.Num(name(par.toInt), num.toLong)

      case Array(i, "#US", l) => level(i.toInt) = Level.Succ(level(l.toInt))
      case Array(i, "#UM", l1, l2) => level(i.toInt) = Level.Max(level(l1.toInt), level(l2.toInt))
      case Array(i, "#UIM", l1, l2) => level(i.toInt) = Level.IMax(level(l1.toInt), level(l2.toInt))
      case Array(i, "#UP", n) => level(i.toInt) = Level.Param(name(n.toInt))

      case Array(i, "#EV", n) => expr(i.toInt) = Var(n.toInt)
      case Array(i, "#ES", l) => expr(i.toInt) = Sort(level(l.toInt))
      case Array(i, "#EC", n, ls @ _*) => expr(i.toInt) = Const(name(n.toInt), ls.map(_.toInt).map(level).toVector)
      case Array(i, "#EA", e1, e2) => expr(i.toInt) = App(expr(e1.toInt), expr(e2.toInt))
      case Array(i, "#EL", b, n, t, e) => expr(i.toInt) = Lam(parseBinding(b, n, t), expr(e.toInt))
      case Array(i, "#EP", b, n, t, e) => expr(i.toInt) = Pi(parseBinding(b, n, t), expr(e.toInt))
      case Array(i, "#EZ", n, t, v, b) => expr(i.toInt) = Let(Binding(name(n.toInt), expr(t.toInt), BinderInfo.Default), expr(v.toInt), expr(b.toInt))

      case Array("#INFIX", _*) => // TODO
      case Array("#POSTFIX", _*) => // TODO
      case Array("#PREFIX", _*) => // TODO
    }

  def parseLine(line: String): Option[Modification] =
    line.split(' ') match {
      case Array("#AX", n, t, ps @ _*) =>
        Some(AxiomMod(Axiom(name(n.toInt), univParams(ps), expr(t.toInt))))
      case Array("#DEF", n, t, v, ps @ _*) =>
        Some(DefMod(Definition(name(n.toInt), univParams(ps), expr(t.toInt), expr(v.toInt))))
      case Array("#IND", numParams, n, t, numIntros, rest @ _*) =>
        val (intros, ps) = rest.splitAt(2 * numIntros.toInt)
        Some(IndMod(
          InductiveType(name(n.toInt), univParams(ps), expr(t.toInt)),
          numParams.toInt, intros.grouped(2).map { case Seq(in, it) => (name(in.toInt), expr(it.toInt)) }.toVector
        ))
      case Array("#QUOT") =>
        Some(QuotMod)
      case toks =>
        parseTermDef(toks)
        None
    }
}

object TextExportParser {
  def parse(lines: Stream[String]): Stream[Modification] = {
    val parser = new TextExportParser
    lines.flatMap(parser.parseLine)
  }

  def parseFile(fn: String): Stream[Modification] =
    parse(io.Source.fromFile(fn).getLines().toStream)
}
