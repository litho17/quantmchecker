package plv.colorado.edu.quantmchecker

import com.sun.source.tree.{MethodInvocationTree, NewClassTree}
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import plv.colorado.edu.quantmchecker.utils.AnnoTypeUtils

import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
class QuantmVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[QuantmAnnotatedTypeFactory](checker) {
  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    // println(node.getArguments)
    super.visitMethodInvocation(node, p)
  }

  override def visitNewClass(node: NewClassTree, p: Void): Void = {
    atypeFactory.getAnnotatedType(node.getIdentifier).getAnnotations.asScala.foreach {
      annot => println(AnnoTypeUtils.extractValues(annot))
    }
    super.visitNewClass(node, p)
  }
}
