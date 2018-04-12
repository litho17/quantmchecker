package plv.colorado.edu.quantmchecker

import javax.lang.model.element.AnnotationMirror

import com.sun.source.tree.{AssignmentTree, NewClassTree}
import org.checkerframework.dataflow.analysis.{FlowExpressions, TransferInput, TransferResult}
import org.checkerframework.dataflow.cfg.node.AssignmentNode
import org.checkerframework.framework.flow.{CFAbstractAnalysis, CFStore, CFTransfer, CFValue}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils}
import plv.colorado.edu.quantmchecker.qual.{Inv, InvBot, InvBounded, InvTop}

import scala.collection.JavaConverters._
/**
  * @author Tianhan Lu
  */
// Flow sensitive type inference rules
class QuantmTransfer(analysis: CFAbstractAnalysis[CFValue, CFStore, CFTransfer]) extends CFTransfer(analysis) {
  private val typeFactory = analysis.getTypeFactory
  private val elements = analysis.getEnv.getElementUtils
  protected val INVBOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])
  protected val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  protected val INVBOUNDED: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBounded])
  protected val INVTOP: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvTop])

  override def visitAssignment(n: AssignmentNode, in: TransferInput[CFValue, CFStore]): TransferResult[CFValue, CFStore] = {
    val result = super.visitAssignment(n, in)
    n.getTree match {
      case tree: AssignmentTree =>
        val lhsTyp = typeFactory.getAnnotatedType(tree.getVariable)
        val lhsAnno = lhsTyp.getAnnotations
        tree.getExpression match {
          case t: NewClassTree =>
            val rhsTyp = typeFactory.getAnnotatedType(t)
            val rhsAnno = rhsTyp.getAnnotations
            if (rhsAnno == null
              || rhsAnno.isEmpty
              || AnnotationUtils.areSameIgnoringValues(rhsAnno.asScala.head, INVTOP)) {
              if (lhsAnno != null && !lhsAnno.isEmpty && AnnotationUtils.areSameIgnoringValues(lhsAnno.asScala.head, INV)) {
                // PrintStuff.printRedString(n, rhsAnno, lhsAnno, AnnotationUtils.areSameIgnoringValues(rhsAnno.asScala.head, INVTOP))
                val receiver = FlowExpressions.internalReprOf(analysis.getTypeFactory, n.getExpression)
                result.getRegularStore.insertValue(receiver, lhsAnno.asScala.head)
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
            }
          case _ =>
        }
      case _ =>
    }
    result
  }
}
