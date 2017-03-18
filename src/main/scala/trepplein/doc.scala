package trepplein
import Doc._

import scala.language.implicitConversions

sealed trait Doc {
  def <>(that: Doc) = Concat(this, that)
  def <+>(that: Doc): Doc = this <> Text(" ") <> that
  def </>(that: Doc): Doc = this <> Line <> that

  val flatSize: Int = this match {
    case Concat(a, b) => a.flatSize + b.flatSize
    case Nest(_, d) => d.flatSize
    case Text(t) => t.length
    case Line => 1
    case Group(a) => a.flatSize
  }
  def fitsFlat(len: Int): Boolean = flatSize <= len

  def render(lineWidth: Int): String = {
    val out = new StringBuilder
    var endOfLine = out.size + lineWidth
    def go(d: Doc, nest: Int, flatMode: Boolean): Unit =
      d match {
        case Concat(a, b) =>
          go(a, nest, flatMode)
          go(b, nest, flatMode)
        case Nest(i, a) =>
          go(a, nest + i, flatMode)
        case Text(t) =>
          out ++= t
        case Line if !flatMode =>
          out += '\n'
          endOfLine = out.size + lineWidth
          for (_ <- 0 until nest) out += ' '
        case Line if flatMode =>
          out += ' '
        case Group(a) =>
          go(a, nest, flatMode || a.fitsFlat(endOfLine - out.size))
      }
    go(this, 0, flatMode = false)
    out.result()
  }

}

object Doc {
  case class Concat(a: Doc, b: Doc) extends Doc
  case class Nest(i: Int, d: Doc) extends Doc
  case class Text(t: String) extends Doc
  case object Line extends Doc
  case class Group(a: Doc) extends Doc

  implicit def fromString(t: String): Text = Text(t)

  def sep(docs: Traversable[Doc], by: Doc): Doc =
    docs.reduceLeftOption(_ <> by <> _).getOrElse(Text(""))

  def spread(cols: Traversable[Doc]): Doc = sep(cols, Text(" "))
  def stack(lines: Traversable[Doc]): Doc = sep(lines, Line)
}