package plv.colorado.edu.emptychecker

import com.sun.source.tree.MethodInvocationTree
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker, BaseTypeVisitor}

/**
  * @author Tianhan Lu
  */
class EmptyVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[BaseAnnotatedTypeFactory](checker) {
  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    println(node.getArguments)
    super.visitMethodInvocation(node, p)
  }
}
