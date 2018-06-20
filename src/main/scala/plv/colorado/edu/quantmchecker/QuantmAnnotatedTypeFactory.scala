package plv.colorado.edu.quantmchecker

import javax.lang.model.element.AnnotationMirror

import com.sun.source.tree._
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.QualifierHierarchy
import org.checkerframework.framework.flow.{CFAbstractAnalysis, CFStore, CFTransfer, CFValue}
import org.checkerframework.framework.util.{GraphQualifierHierarchy, MultiGraphQualifierHierarchy}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, TreeUtils}
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.qual.{Inv, InvBot, InvTop, InvUnk}
import plv.colorado.edu.quantmchecker.verification.{SmtUtils, Z3Solver}

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
  protected val INVTOP: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvTop])

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
    * @param rcvr tree representation of a variable
    * @return annotation of the receiver of a method invocation
    */
  def getTypeAnnotation(rcvr: Tree): AnnotationMirror = {
    this.getQualifierHierarchy
      .findAnnotationInHierarchy(
        getAnnotatedType(rcvr).getAnnotations,
        this.getQualifierHierarchy.getTopAnnotations.iterator().next())
  }

  @deprecated
  def getExprAnnotations(node: ExpressionTree): Option[AnnotationMirror] = {
    if (node == null) {
      None
    } else {
      /*val vtree = TreeUtils.enclosingVariable(atypeFactory.getPath(node))
      if (vtree == null)
        return List.empty
      val element = TreeUtils.elementFromDeclaration(vtree)*/
      val element = TreeUtils.elementFromUse(node)
      if (element == null) {
        None
      } else {
        // elements.getAllAnnotationMirrors(element).asScala.toList
        val annotations = this.getAnnotatedType(element).getAnnotations
        Some(this.getQualifierHierarchy.findAnnotationInHierarchy(annotations, this.getQualifierHierarchy.getTopAnnotations.asScala.head))
        //element.getAnnotationMirrors.asScala.toList
      }
    }
  }

  /**
    *
    * @param annotation type annotation of a variable
    * @return a set of collected annotations: self/self.f.g -> its type annotation
    */
  def getVarAnnoMap(annotation: AnnotationMirror): HashMap[String, String] = {
    if (annotation != null) {
      Utils.extractArrayValues(annotation, "value").foldLeft(new HashMap[String, String]) {
        (acc, inv) =>
          SmtUtils.startsWithToken(inv, SmtUtils.SELF).foldLeft(acc) { // E.g. self or self.f.g
            (acc2, t) =>
              val tokens = SmtUtils.parseSmtlibToToken(inv)
              val invp = {
                if (tokens.length == 1) {
                  val token = tokens.head.toString()
                  if (token == SmtUtils.SELF) {
                    assert(false, "Invariant cannot be self")
                    SmtUtils.TRUE
                  } else if (token != SmtUtils.TRUE && token != SmtUtils.FALSE) { // E.g. @Inv("x|n|c") Iterator it;
                    // Automatically tranform invariant (e.g. x|n|c -> = self x|n|c)
                    SmtUtils.mkEq(SmtUtils.SELF, inv)
                  } else inv
                } else {
                  inv
                }
              }
              acc2 + (t -> invp)
          }
      }
    } else {
      new HashMap[String, String]
    }
  }

  /**
    *
    * @param node        tree representation of a variable
    * @return a set of collected annotations: self/self.f.g -> its type annotation
    */
  def getVarAnnoMap(node: Tree): HashMap[String, String] = {
    /*
    val annotations = {
      node.getModifiers.getAnnotations.asScala.foldLeft(new HashSet[AnnotationMirror]) {
        (acc, t) =>
          acc ++ this.getAnnotatedType(trees.getElement(this.getPath(node))).getAnnotations.asScala
      }
    }
    val listInvAnnotations = annotations.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, targetAnnot))
    val annotations: List[String] = AnnoTypeUtils.extractValues(TreeUtils.annotationFromAnnotationTree(node))
    */
    getVarAnnoMap(getTypeAnnotation(node))
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
            this.getVarAnnoMap(member).foldLeft(acc) { // E.g. self.f -> v.f
              case (acc2, (v, typ)) => acc2 + (v.replace(SmtUtils.SELF, member.getName.toString) -> typ)
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
              this.getVarAnnoMap(stmt).foldLeft(acc) { // E.g. self.f -> v.f
                case (acc2, (v, typ)) => acc2 + (v.replace(SmtUtils.SELF, stmt.getName.toString) -> typ)
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
        val subMap = getVarAnnoMap(subAnno) // E.g. self -> inv1; self.f -> inv2
        val superMap = getVarAnnoMap(superAnno) // E.g. self -> inv3; self.g -> inv4
        val keySet = subMap.keySet.union(superMap.keySet)
        if (keySet != subMap.keySet || keySet != superMap.keySet)
          return false
        keySet.forall { // TODO: "true" for unannotated types
          v =>
            val p = subMap.getOrElse(v, SmtUtils.TRUE)
            val q = superMap.getOrElse(v, SmtUtils.TRUE)
            val query = SmtUtils.mkImply(p, q)
            Z3Solver.check(Z3Solver.parseSMTLIB2String(query))
        }
      }

      // Check subtyping for base types
      super.isSubtype(newSubAnno, newSuperAnno)
    }
  }

}
