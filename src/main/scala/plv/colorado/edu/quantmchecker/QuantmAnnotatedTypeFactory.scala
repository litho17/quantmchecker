package plv.colorado.edu.quantmchecker

import javax.lang.model.element.AnnotationMirror

import com.sun.source.tree._
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.QualifierHierarchy
import org.checkerframework.framework.flow.{CFAbstractAnalysis, CFStore, CFTransfer, CFValue}
import org.checkerframework.framework.util.{GraphQualifierHierarchy, MultiGraphQualifierHierarchy}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils}
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.qual.{Inv, InvBot, InvUnk}
import plv.colorado.edu.quantmchecker.verification.{SmtlibUtils, Z3Solver}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
class QuantmAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  private val DEBUG: Boolean = false
  protected val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  protected val INVUNK: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvUnk])
  protected val INVBOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])

  // disable flow inference
  // super(checker, false);
  this.postInit()
  if (DEBUG) {
    println(getQualifierHierarchy.toString)
    // getTypeHierarchy();
  }

  override def createFlowTransferFunction(analysis: CFAbstractAnalysis[CFValue, CFStore, CFTransfer]): CFTransfer = {
    new QuantmTransfer(analysis)
  }

  // Learned from KeyForAnnotatedTypeFactory.java
  override def createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy = new QuantmQualifierHierarchy(factory)

  /**
    *
    * @param rcvr ???
    * @return annotation of the receiver of a method invocation
    */
  def getTypeAnnotation(rcvr: Tree): AnnotationMirror = {
    this.getQualifierHierarchy()
      .findAnnotationInHierarchy(
        getAnnotatedType(rcvr).getAnnotations(),
        this.getQualifierHierarchy().getTopAnnotations().iterator().next())
  }

  /**
    *
    * @param node        a variable declaration AST node
    * @param targetAnnot target annotation type to collect from the variable
    * @return a set of collected annotations
    */
  def getAnnotFromVariableTree(node: VariableTree, targetAnnot: AnnotationMirror): HashMap[String, String] = {
    val varName = node.getName.toString
    val annotations = {
      node.getModifiers.getAnnotations.asScala.foldLeft(new HashSet[AnnotationMirror]) {
        (acc, t) =>
          acc ++ this.getAnnotatedType(trees.getElement(this.getPath(node))).getAnnotations.asScala
      }
    }
    val listInvAnnotations = annotations.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, targetAnnot))
    // val annotations: List[String] = AnnoTypeUtils.extractValues(TreeUtils.annotationFromAnnotationTree(node))
    if (listInvAnnotations.nonEmpty) {
      val invs: List[String] = Utils.extractArrayValues(listInvAnnotations.head, "value")
      invs.foldLeft(new HashMap[String, String]) {
        (acc, inv) =>
          SmtlibUtils.startsWithToken(inv, varName).foldLeft(acc) {
            (acc2, t) => acc2 + (t -> inv)
          }
      }
    } else {
      new HashMap[String, String]
    }
  }

  /**
    *
    * @param classTree a class definition
    * @return a typing context collected from class field declarations: variable -> its type annotation
    */
  def getFieldTypCxt(classTree: ClassTree): HashMap[String, String] = {
    classTree.getMembers.asScala.foldLeft(new HashMap[String, String]) {
      (acc, member) =>
        member match {
          case member: VariableTree =>
            // Get annotations on class fields
            this.getAnnotFromVariableTree(member, INV).foldLeft(acc) {
              case (acc2, (v, typ)) => acc2 + (v -> typ)
            }
          case _ => acc
        }
    }
  }

  /**
    *
    * @param methodTree a method
    * @return a typing context collected from local variable declarations: variable -> its type annotation
    */
  def getLocalTypCxt(methodTree: MethodTree): HashMap[String, String] = {
    if (methodTree.getBody != null) {
      val stmts = methodTree.getBody.getStatements.asScala.foldLeft(new HashSet[StatementTree]) {
        (acc, stmt) => acc ++ flattenStmt(stmt)
      } ++ methodTree.getParameters.asScala

      stmts.foldLeft(new HashMap[String, String]) {
        (acc, stmt) =>
          stmt match {
            case stmt: VariableTree =>
              // Local invariants should only be on variable declarations
              // Otherwise, invariants are simply ignored
              this.getAnnotFromVariableTree(stmt, INV).foldLeft(acc) {
                case (acc2, (v, typ)) => acc2 + (v -> typ)
              }
            case x@_ =>
              if (x.toString.contains("@Inv(")) Utils.logging("Missed an invariant!\n" + x.toString)
              acc
          }
      }
    } else {
      new HashMap[String, String]
    }
  }

  /**
    *
    * @param node a statement tree
    * @return collect a set of all leave statements
    *         Note: All other StatementTrees are ignored
    */
  def flattenStmt(node: StatementTree): HashSet[StatementTree] = {
    node match {
      case stmt: BlockTree =>
        stmt.getStatements.asScala.foldLeft(new HashSet[StatementTree])((acc, s) => acc ++ flattenStmt(s))
      case stmt: DoWhileLoopTree => flattenStmt(stmt.getStatement)
      case stmt: EnhancedForLoopTree => flattenStmt(stmt.getStatement)
      case stmt: ForLoopTree =>
        stmt.getInitializer.asScala.foldLeft(flattenStmt(stmt.getStatement)) {
          (acc, s) => acc ++ flattenStmt(s)
        }
      case stmt: WhileLoopTree => flattenStmt(stmt.getStatement)
      case stmt: LabeledStatementTree => flattenStmt(stmt.getStatement)
      case stmt: IfTree => flattenStmt(stmt.getThenStatement) ++ flattenStmt(stmt.getElseStatement)
      case stmt: SwitchTree =>
        stmt.getCases.asScala.foldLeft(new HashSet[StatementTree]) {
          (acc, caseTree) => caseTree.getStatements.asScala.foldLeft(acc)((acc2, s) => acc2 ++ flattenStmt(s))
        }
      case stmt: ExpressionStatementTree => HashSet[StatementTree](stmt)
      case stmt: ReturnTree => HashSet[StatementTree](stmt)
      case stmt: VariableTree => HashSet[StatementTree](stmt)
      case stmt: TryTree => flattenStmt(stmt.getBlock) ++ flattenStmt(stmt.getFinallyBlock)
      case stmt: SynchronizedTree => flattenStmt(stmt.getBlock)
      case _ => new HashSet[StatementTree]
    }
  }

  final private class QuantmQualifierHierarchy(val factory: MultiGraphQualifierHierarchy.MultiGraphFactory) extends GraphQualifierHierarchy(factory, INVBOT) {
    override def isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean = {
      val isSubInvUnk = AnnotationUtils.areSameIgnoringValues(subAnno, INVUNK)
      val isSuperInvUnk = AnnotationUtils.areSameIgnoringValues(superAnno, INVUNK)
      val isSubInv = AnnotationUtils.areSameIgnoringValues(subAnno, INV)
      val isSuperInv = AnnotationUtils.areSameIgnoringValues(superAnno, INV)

      val newSubAnno = if (isSubInv) INV else if (isSubInvUnk) INVUNK else subAnno
      val newSuperAnno = if (isSuperInv) INV else if (isSuperInvUnk) INVUNK else superAnno

      // Check subtyping for invariants
      if (isSubInv && isSuperInv) {
        val lhsValues = Utils.extractArrayValues(superAnno, "value")
        val rhsValues = Utils.extractArrayValues(subAnno, "value")
        try {
          val pairs = lhsValues.zip(rhsValues) // TODO: "true" for unannotated types
          pairs.forall {
            case (left, right) =>
              val query = SmtlibUtils.genImplyQuery(right, left)
              // println(query)
              Z3Solver.check(Z3Solver.parseSMTLIB2String(query))
          }
        } catch {
          case e: Exception => return false
        }
      }

      // Check subtyping for base types
      super.isSubtype(newSubAnno, newSuperAnno)
    }
  }

}
