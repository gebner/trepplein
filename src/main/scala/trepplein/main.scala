package trepplein

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.concurrent.ExecutionContext.Implicits.global

class LibraryPrinter(env: PreEnvironment, out: String => Unit,
    hideProofs: Boolean = true, lineWidth: Int = 80,
    printDependencies: Boolean = false) {
  private val declsPrinted = mutable.Map[Name, Unit]()
  def printDecl(name: Name): Unit = declsPrinted.getOrElseUpdate(name, {
    val tc = new TypeChecker(env, unsafeUnchecked = true)
    val pp = new PrettyPrinter(typeChecker = Some(tc), hideProofs = hideProofs)

    val decl = env(name)
    if (printDependencies) {
      decl.ty.constants.foreach(printDecl)
      decl match {
        case decl: Definition if !tc.isProposition(decl.ty) =>
          decl.value.constants.foreach(printDecl)
        case _ =>
      }
    }

    out((pp.pp(decl) <> Doc.Line).render(lineWidth))
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
      case Array(fn, thms @ _*) =>
        val preEnv = TextExportParser.parseFile(fn)
          .foldLeft[PreEnvironment](Environment.default)(_.add(_))

        val printer = new LibraryPrinter(preEnv, print)
        thms.foreach(printer.handleArg(_))

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