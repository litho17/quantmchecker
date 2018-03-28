package plv.colorado.edu

import javax.lang.model.element.AnnotationMirror

import com.sun.source.tree.{CompilationUnitTree, Tree}
import com.sun.source.util.SourcePositions
import org.checkerframework.javacutil.AnnotationUtils

import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
object AnnoTypeUtils {
  def extractValues(anno: AnnotationMirror): List[String] = {
    val valMap = anno.getElementValues
    if (valMap.isEmpty) {
      List()
    } else {
      // TODO: hardcoded "value"
      AnnotationUtils.getElementValueArray(anno, "value", classOf[String], true).asScala.toList
    }
  }

  def getLineNumber(node: Tree, positions: SourcePositions, root: CompilationUnitTree): Long = {
    root.getLineMap.getLineNumber(positions.getStartPosition(root, node))
  }
}
