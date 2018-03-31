package plv.colorado.edu.quantmchecker.summarylang

import javax.lang.model.element.ExecutableElement

import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
object MethodSumUtils {
  /**
    *
    * @param summary       a method summary
    * @param invokedMethod a method invocation
    * @return Either the index of formal argument that is described by the summary,
    *         or the class field that is described by the summary
    */
  def whichVar(summary: MethodSummary, invokedMethod: ExecutableElement): Either[Integer, String] = {
    val formalArgs = invokedMethod.getParameters.asScala.map(v => v.getSimpleName.toString)
    val varName = summary match {
      case MethodSummaryI(v, _) => v
      case MethodSummaryV(v, _) => v
      case _ => ""
    }
    if (formalArgs.contains(varName)) {
      Left(formalArgs.indexOf(varName))
    } else {
      Right(varName)
    }
  }
}
