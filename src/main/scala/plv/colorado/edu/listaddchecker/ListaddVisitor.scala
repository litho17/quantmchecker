package plv.colorado.edu.listaddchecker

import com.sun.source.tree.MethodInvocationTree
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker, BaseTypeVisitor}

/**
  * @author Tianhan Lu
  */
class ListaddVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[BaseAnnotatedTypeFactory](checker) {
  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    // println(root.getSourceFile)
    super.visitMethodInvocation(node, p)
  }
}
