package trepplein

import java.io.{ BufferedInputStream, FileInputStream }
import java.nio.ByteBuffer
import java.util.Arrays

import org.parboiled2.ParserInput.{ ByteArrayBasedParserInput, DefaultParserInput }
import org.parboiled2._

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.{ Failure, Success }

sealed trait ExportFileCommand
case class ExportedModification(modification: Modification) extends ExportFileCommand
case class ExportedNotation(notation: Notation) extends ExportFileCommand

private class TextExportParser {
  val name: mutable.ArrayBuffer[Name] = mutable.ArrayBuffer[Name]()
  val level: mutable.ArrayBuffer[Level] = mutable.ArrayBuffer[Level]()
  val expr: mutable.ArrayBuffer[Expr] = mutable.ArrayBuffer[Expr]()

  name += Name.Anon
  level += Level.Zero

  @tailrec final def write[T](b: mutable.ArrayBuffer[T], i: Int, t: T, default: => T): Unit =
    b.size match {
      case `i` => b += t
      case s if s < i =>
        b += default
        write(b, i, t, default)
      case s if s > i =>
        b(i) = t
    }
}

private class LineParser(val textExportParser: TextExportParser, val input: ParserInput) extends Parser {
  import textExportParser._

  def digit: Rule0 = rule { test('0' <= cursorChar && cursorChar <= '9') ~ ANY }
  def long: Rule1[Long] = rule { capture(oneOrMore(digit)) ~> ((x: String) => x.toLong) }

  @tailrec private def parseIntCore(from: Int, to: Int, acc: Int): Int =
    if (from == to) acc else parseIntCore(from + 1, to, 10 * acc + (input.charAt(from) - '0'))
  def int: Rule1[Int] = rule {
    push(cursor) ~ oneOrMore(digit) ~ push(cursor) ~>
      ((from: Int, to: Int) => parseIntCore(from, to, 0))
  }

  def rest: Rule1[String] = rule { capture(zeroOrMore(CharPredicate.from(_ != '\n'))) }

  def restNums: Rule1[Seq[Int]] = rule { zeroOrMore(" " ~ int) }

  def binderInfo: Rule1[BinderInfo] =
    rule {
      "#BD" ~ push(BinderInfo.Default) |
        "#BI" ~ push(BinderInfo.Implicit) |
        "#BC" ~ push(BinderInfo.InstImplicit) |
        "#BS" ~ push(BinderInfo.StrictImplicit)
    }

  def nameRef: Rule1[Name] = rule { int ~> name }
  def levelRef: Rule1[Level] = rule { int ~> level }
  def exprRef: Rule1[Expr] = rule { int ~> expr }

  def nameDef: Rule1[Name] =
    rule {
      "#NS " ~ nameRef ~ " " ~ rest ~> Name.Str |
        "#NI " ~ nameRef ~ " " ~ long ~> Name.Num
    }

  def levelDef: Rule1[Level] =
    rule {
      "#US " ~ levelRef ~> Level.Succ |
        "#UM " ~ levelRef ~ " " ~ levelRef ~> (Level.Max(_, _)) |
        "#UIM " ~ levelRef ~ " " ~ levelRef ~> Level.IMax |
        "#UP " ~ nameRef ~> Level.Param
    }

  def exprDef: Rule1[Expr] =
    rule {
      "#EV " ~ int ~> Var |
        "#ES " ~ levelRef ~> ((l: Level) => Sort(l)) |
        "#EC " ~ nameRef ~ restNums ~> ((n, ls) => Const(n, ls.map(level).toVector)) |
        "#EA " ~ exprRef ~ " " ~ exprRef ~> App |
        "#EL " ~ binderInfo ~ " " ~ nameRef ~ " " ~ exprRef ~ " " ~ exprRef ~> ((b, n, t, e) => Lam(Binding(n, t, b), e)) |
        "#EP " ~ binderInfo ~ " " ~ nameRef ~ " " ~ exprRef ~ " " ~ exprRef ~> ((b, n, t, e) => Pi(Binding(n, t, b), e)) |
        "#EZ " ~ nameRef ~ " " ~ exprRef ~ " " ~ exprRef ~ " " ~ exprRef ~> ((n: Name, t: Expr, v: Expr, b: Expr) => Let(Binding(n, t, BinderInfo.Default), v, b))
    }

  def notationDef: Rule1[Notation] =
    rule {
      "#INFIX " ~ nameRef ~ " " ~ int ~ " " ~ rest ~> ((n: Name, p: Int, text: String) => Infix(n, p, text)) |
        "#POSTFIX " ~ nameRef ~ " " ~ int ~ " " ~ rest ~> ((n: Name, p: Int, text: String) => Postfix(n, p, text)) |
        "#PREFIX " ~ nameRef ~ " " ~ int ~ " " ~ rest ~> ((n: Name, p: Int, text: String) => Prefix(n, p, text))
    }

  def univParams: Rule1[Vector[Level.Param]] = rule { restNums ~> ((ps: Seq[Int]) => ps.view.map(name).map(Level.Param).toVector) }

  def modification: Rule1[Modification] =
    rule {
      "#AX " ~ nameRef ~ " " ~ exprRef ~ univParams ~> ((n, t, ps) => AxiomMod(n, ps, t)) |
        "#DEF " ~ nameRef ~ " " ~ exprRef ~ " " ~ exprRef ~ univParams ~> ((n, t, v, ps) => DefMod(n, ps, t, v)) |
        "#QUOT" ~ push(QuotMod) |
        "#IND " ~ int ~ " " ~ nameRef ~ " " ~ exprRef ~ " " ~ int ~ restNums ~> parseInd _
    }

  def parseInd(numParams: Int, n: Name, t: Expr, numIntros: Int, rest: Seq[Int]): IndMod = {
    val (intros, ps) = rest.splitAt(2 * numIntros)
    IndMod(
      n, ps.view.map(name).map(Level.Param).toVector, t,
      numParams, intros.grouped(2).map { case Seq(in, it) => (name(in), expr(it)) }.toVector)
  }

  def lineContent: Rule1[Option[ExportFileCommand]] =
    rule {
      int ~ " " ~ (nameDef ~> { (i: Int, n: Name) => write(name, i, n, Name.Anon); None } |
        exprDef ~> { (i: Int, e: Expr) => write(expr, i, e, Sort(0)); None } |
        levelDef ~> { (i: Int, l: Level) => write(level, i, l, Level.Zero); None }) |
        notationDef ~> ((x: Notation) => Some(ExportedNotation(x))) |
        modification ~> ((x: Modification) => Some(ExportedModification(x)))
    }

  def lineWithoutNL: Rule1[Option[ExportFileCommand]] = rule { lineContent ~ EOI }

  def lines: Rule1[Seq[ExportFileCommand]] = rule {
    ((lineContent ~ "\n").* ~> ((cmds: Seq[Option[ExportFileCommand]]) => cmds.flatten)) ~ EOI
  }
}

object TextExportParser {
  @tailrec
  private def reverseIndexOf(chunk: Array[Byte], needle: Byte, from: Int): Int =
    if (chunk(from) == needle) from
    else if (from == 0) -1
    else reverseIndexOf(chunk, needle, from - 1)

  private class Chunk(bytes: Array[Byte], endIndex: Int) extends DefaultParserInput {
    val length: Int = endIndex
    def charAt(ix: Int): Char = (bytes(ix) & 0xFF).toChar
    def sliceString(start: Int, end: Int) =
      new String(bytes, start, math.max(end - start, 0), UTF8)
    def sliceCharArray(start: Int, end: Int): Array[Char] =
      UTF8.decode(ByteBuffer.wrap(java.util.Arrays.copyOfRange(bytes, start, end))).array()
  }

  def parseFile(fn: String): Stream[ExportFileCommand] = {
    val in = new FileInputStream(fn)
    def bufSize = 8 << 10
    def readChunksCore(buf: Array[Byte], begin: Int): Stream[Chunk] = {
      val len = in.read(buf, begin, buf.length - begin)
      if (len <= 0) Stream.empty else {
        val nl = reverseIndexOf(buf, '\n', begin + len - 1)
        if (nl == -1) {
          // no newline found in the whole chunk,
          // this should only happen at the end but let's try again to make sure
          new Chunk(buf, len) #:: readChunks()
        } else {
          val nextBuf = new Array[Byte](bufSize)
          val reuse = (begin + len) - (nl + 1)
          System.arraycopy(buf, nl + 1, nextBuf, 0, reuse)
          new Chunk(buf, nl + 1) #:: readChunksCore(nextBuf, reuse)
        }
      }
    }
    def readChunks(): Stream[Chunk] = readChunksCore(new Array[Byte](bufSize), 0)
    val parser = new TextExportParser
    readChunks().flatMap { chunk =>
      val lineParser = new LineParser(parser, chunk)
      lineParser.lines.run() match {
        case Success(mods) =>
          mods
        case Failure(error: ParseError) =>
          throw new IllegalArgumentException(lineParser.formatError(error))
        case Failure(ex) => throw ex
      }
    }
  }
}
