package plv.colorado.edu.quantmchecker

import javax.lang.model.`type`.TypeMirror
import javax.lang.model.element.{AnnotationMirror, Element, ExecutableElement}

import com.sun.source.tree.{AssignmentTree, MemberSelectTree}
import org.checkerframework.dataflow.analysis.{TransferInput, TransferResult}
import org.checkerframework.dataflow.cfg.node.AssignmentContext.MethodReturnContext
import org.checkerframework.dataflow.cfg.node.{AssignmentNode, ReturnNode, VariableDeclarationNode}
import org.checkerframework.framework.`type`.AnnotatedTypeMirror.AnnotatedExecutableType
import org.checkerframework.framework.flow.{CFAbstractAnalysis, CFStore, CFTransfer, CFValue}
import org.checkerframework.javacutil.{AnnotationBuilder, ElementUtils, TreeUtils}
import plv.colorado.edu.quantmchecker.qual.{Inv, InvBot, InvTop}

import scala.collection.JavaConverters._
/**
  * @author Tianhan Lu
  */
// Flow sensitive type inference rules
class QuantmTransfer(analysis: CFAbstractAnalysis[CFValue, CFStore, CFTransfer]) extends CFTransfer(analysis) {
  private val aTypeFactory = analysis.getTypeFactory
  private val elements = analysis.getEnv.getElementUtils
  protected val INVBOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])
  protected val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  protected val INVTOP: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvTop])

  override def visitReturn(n: ReturnNode, p: TransferInput[CFValue, CFStore]): TransferResult[CFValue, CFStore] = {
    val result = super.visitReturn(n, p)
    n.getResult.getAssignmentContext match {
      case mcxt: MethodReturnContext =>
        val method = mcxt.getElementForType.asInstanceOf[ExecutableElement]
        val retTyp = aTypeFactory.getAnnotatedType(n.getTree.getExpression)
        val toAdd = retTyp.getAnnotationInHierarchy(aTypeFactory.getQualifierHierarchy.getTopAnnotations.asScala.head)
        val methodTyp: AnnotatedExecutableType = aTypeFactory.getAnnotatedType(TreeUtils.enclosingMethod(aTypeFactory.getPath(n.getTree)))
        // methodTyp.addAnnotations(List(toAdd).asJava)
        // TreeUtils.elementFromUse(n.getTree.getExpression)
        // typeFactory.addComputedTypeAnnotations(method, retTyp) // Nothing happens here
        // val methodAnnotations = typeFactory.getDeclAnnotations(method)
        // methodAnnotations.add(toAdd)
        // val retTyp = mcxt.getContextTree
      case _ =>
    }
    result
  }

  override def visitVariableDeclaration(n: VariableDeclarationNode, p: TransferInput[CFValue, CFStore]): TransferResult[CFValue, CFStore] = {
    val result = super.visitVariableDeclaration(n, p)
    val tree = n.getTree
    val lhsAnno = aTypeFactory.getAnnotatedType(tree).getAnnotations
    tree.getInitializer match {
      case rhs: MemberSelectTree =>
        val receiver = TreeUtils.getReceiverTree(rhs)
        val receiverDecl: Element = TreeUtils.elementFromUse(receiver)
        val fieldOrMehod = rhs.getIdentifier
        if (receiverDecl != null) {
          // println(tree, if (tree.getInitializer != null) tree.getInitializer.getKind, ElementUtils.enclosingClass(receiverDecl))
          val receiverTyp: TypeMirror = aTypeFactory.getAnnotatedType(receiverDecl).getUnderlyingType
          val fields = ElementUtils.getAllFieldsIn(ElementUtils.enclosingClass(receiverDecl), elements)
          fields.asScala.foreach {
            f =>
              val fldAnno = aTypeFactory.getAnnotatedType(f).getAnnotations
              // println(f, fldAnno, elements.getAllAnnotationMirrors(f), aTypeFactory.declarationFromElement(f))
              if (f.getSimpleName == fieldOrMehod) {
                // println(fldAnno)
              }
          }
        }
      case _ =>
    }
    super.visitVariableDeclaration(n, p)
  }

  override def visitAssignment(n: AssignmentNode, in: TransferInput[CFValue, CFStore]): TransferResult[CFValue, CFStore] = {
    val result = super.visitAssignment(n, in)
    n.getTree match {
      case tree: AssignmentTree =>
      case _ =>
    }
    result
  }

  // val receiver = FlowExpressions.internalReprOf(analysis.getTypeFactory, n.getExpression)
  // result.getRegularStore.insertValue(receiver, lhsAnno.asScala.head)
  /**
    * Nothing happens here, because only support these five types
    * FlowExpressions.FieldAccess
    * FlowExpressions.ThisReference
    * FlowExpressions.LocalVariable
    * FlowExpressions.MethodCall
    * FlowExpressions.ArrayAccess
    */
  // PrintStuff.printRedString(result.getRegularStore.getValue(receiver).getAnnotations)
  // PrintStuff.printGreenString(CFAAbstractStore.canInsertReceiver)
  // val newResultValue = analysis.createSingleAnnotationValue(lhsAnno.asScala.head, result.getResultValue.getUnderlyingType)
  // return new RegularTransferResult[CFValue, CFStore](newResultValue, result.getRegularStore)
}
