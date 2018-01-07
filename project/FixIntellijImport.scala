import sbt.AutoPlugin
import sbt.Keys._

// https://github.com/sbt/sbt/issues/3432#issuecomment-353423909
object FixIntellijImport extends AutoPlugin {
  override def trigger = allRequirements
  override def projectSettings = Seq(
    updateConfiguration in updateSbtClassifiers :=
      (updateConfiguration in updateSbtClassifiers).value.withMissingOk(true)
  )
}
