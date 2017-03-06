package trepplein
import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits._
import scala.concurrent.duration.Duration

object main {
  def main(args: Array[String]): Unit =
    args match {
      case Array(fn) =>
        Await.result(
          TextExportParser.parseFile(fn)
          .foldLeft[PreEnvironment](Environment.default)(_.add(_)).force,
          Duration.Inf
        ) match {
          case Left(exs) =>
            for (ex <- exs) println(ex.getMessage)
            sys.exit(1)
          case Right(env) =>
            println(s"checked ${env.declarations.size} declarations")
        }
      case _ =>
        println("Usage: trepplein export.out")
        sys.exit(1)
    }
}