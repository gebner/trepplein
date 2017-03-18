package trepplein
import Doc._

import scala.language.implicitConversions

sealed trait Doc {
  def <>(that: Doc): Doc = Concat(this, that)
  def <+>(that: Doc): Doc = this <> Text(" ") <> that
  def </>(that: Doc): Doc = this <> Line <> that
  def nest(i: Int): Doc = Nest(i, this)
  def group: Doc = Group(this)

  private val flatSize: Int = this match {
    case Concat(a, b) => a.flatSize + b.flatSize
    case Nest(_, d) => d.flatSize
    case Text(t) => t.length
    case Line => 1
    case Group(a) => a.flatSize
  }
  private val containsLine: Boolean = this match {
    case Line => true
    case Concat(a, b) => a.containsLine || b.containsLine
    case Nest(_, d) => d.containsLine
    case Text(_) => false
    case Group(a) => a.containsLine
  }
  private val distToFirstLine: Int = this match {
    case Line => 0
    case Concat(a, b) => a.distToLine(b.distToFirstLine)
    case Nest(_, d) => d.distToFirstLine
    case Text(t) => t.length
    case Group(a) => a.distToFirstLine
  }
  private def distToLine(afterwards: Int): Int =
    if (containsLine) distToFirstLine else distToFirstLine + afterwards

  def render(lineWidth: Int): String = {
    val out = new StringBuilder
    var endOfLine = out.size + lineWidth
    def go(d: Doc, nest: Int, flatMode: Boolean, distToNextLine: Int): Unit =
      d match {
        case Concat(a, b) =>
          go(a, nest, flatMode, b.distToLine(distToNextLine))
          go(b, nest, flatMode, distToNextLine)
        case Nest(i, a) =>
          go(a, nest + i, flatMode, distToNextLine)
        case Text(t) =>
          out ++= t
        case Line if !flatMode =>
          out += '\n'
          endOfLine = out.size + lineWidth
          for (_ <- 0 until nest) out += ' '
        case Line if flatMode =>
          out += ' '
        case Group(a) =>
          go(a, nest, flatMode || out.size + a.flatSize + distToNextLine <= endOfLine, distToNextLine)
      }
    go(this, nest = 0, flatMode = false, distToNextLine = 0)
    out.result()
  }

}

object Doc {
  private case class Concat(a: Doc, b: Doc) extends Doc
  private case class Nest(i: Int, d: Doc) extends Doc
  private case class Text(t: String) extends Doc
  private case object Line extends Doc
  private case class Group(a: Doc) extends Doc

  def line: Doc = Line
  implicit def text(t: String): Doc = Text(t)

  def sep(docs: Traversable[Doc], by: Doc): Doc =
    docs.reduceLeftOption(_ <> by <> _).getOrElse(Text(""))

  def spread(cols: Traversable[Doc]): Doc = sep(cols, Text(" "))
  def stack(lines: Traversable[Doc]): Doc = sep(lines, Line)
}