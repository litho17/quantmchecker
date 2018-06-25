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
    * @return index of the target variable and the access path (-1 represents "this")
    *         E.g. this.f -> (-1, ".f"); o.g -> (2, ".g")
    */
  def whichVar(summary: MSum, invokedMethod: ExecutableElement): (Integer, String) = {
    val formalArgs = invokedMethod.getParameters.asScala.map(v => v.getSimpleName.toString)
    val varName = summary match {
      case MSumI(v, _) => v
      case MSumV(v, _) => v
      case _ => ""
    }
    val dotIdx = varName.indexOf(".")
    val (target, accessPath) = {
      if (dotIdx != -1) (varName.substring(0, dotIdx), varName.substring(dotIdx, varName.length))
      else (varName, "")
    }
    val idx = {
      if (target == "this") -1
      else formalArgs.indexOf(target)
    }
    (idx, accessPath)
  }
}
