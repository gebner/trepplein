package trepplein

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.concurrent.ExecutionContext.Implicits.global

class LibraryPrinter(env: PreEnvironment, notations: Map[Name, Notation],
    out: String => Unit,
    hideProofs: Boolean = true, lineWidth: Int = 80,
    printDependencies: Boolean = true) {
  private val declsPrinted = mutable.Map[Name, Unit]()
  def printDecl(name: Name): Unit = declsPrinted.getOrElseUpdate(name, {
    val tc = new TypeChecker(env, unsafeUnchecked = true)
    val pp = new PrettyPrinter(typeChecker = Some(tc), notations = notations, hideProofs = hideProofs)

    val decl = env(name)
    if (printDependencies) {
      decl.ty.constants.foreach(printDecl)
      decl match {
        case decl: Definition if !hideProofs || !tc.isProposition(decl.ty) =>
          decl.value.constants.foreach(printDecl)
        case _ =>
      }
    }

    out((pp.pp(decl) <> Doc.line).render(lineWidth))
  })

  private val axiomsChecked = mutable.Map[Name, Unit]()
  def checkAxioms(name: Name): Unit = axiomsChecked.getOrElseUpdate(name, env(name) match {
    case Definition(_, _, ty, value, _) =>
      ty.constants.foreach(checkAxioms)
      value.constants.foreach(checkAxioms)
    case Axiom(_, _, _) =>
      printDecl(name)
    // TODO: inductive, quotient
    case decl =>
      decl.ty.constants.foreach(checkAxioms)
  })

  def handleArg(name: Name): Unit = {
    checkAxioms(name)
    printDecl(name)
  }
}

object main {
  def main(args: Array[String]): Unit =
    args match {
      case Array(fn) =>
        val exportedCommands = TextExportParser.parseFile(fn)

        val preEnv = exportedCommands.collect { case ExportedModification(mod) => mod }
          .foldLeft[PreEnvironment](Environment.default)(_.add(_))

        val notations = Map() ++ exportedCommands.
          collect { case ExportedNotation(not) => not.fn -> not }.
          reverse // the beautiful unicode notation is exported first

        val printer = new LibraryPrinter(preEnv, notations, print, hideProofs = true)
        preEnv.declarations.keys.foreach(printer.handleArg)

        Await.result(preEnv.force, Duration.Inf) match {
          case Left(exs) =>
            for (ex <- exs) println(ex)
            sys.exit(1)
          case Right(env) =>
            println(s"-- successfully checked ${env.declarations.size} declarations")
        }
      case _ =>
        println("Usage: trepplein export.out")
        sys.exit(1)
    }
}