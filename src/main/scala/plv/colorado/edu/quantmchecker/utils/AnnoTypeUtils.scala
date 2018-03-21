package plv.colorado.edu.quantmchecker.utils

import javax.lang.model.element.AnnotationMirror

import org.checkerframework.javacutil.AnnotationUtils

import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
object AnnoTypeUtils {
  def extractValues(anno: AnnotationMirror): List[String] = {
    val valMap = anno.getElementValues
    if (valMap.isEmpty)
      List()
    else
      AnnotationUtils.getElementValueArray(anno, "value", classOf[String], true).asScala.toList
  }
}
