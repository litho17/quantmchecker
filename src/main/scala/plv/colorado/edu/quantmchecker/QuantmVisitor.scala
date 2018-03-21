package plv.colorado.edu.quantmchecker

import com.sun.source.tree.MethodInvocationTree
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}

/**
  * @author Tianhan Lu
  */
class QuantmVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[QuantmAnnotatedTypeFactory](checker) {
  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    println(node.getArguments)
    super.visitMethodInvocation(node, p)
  }
}
