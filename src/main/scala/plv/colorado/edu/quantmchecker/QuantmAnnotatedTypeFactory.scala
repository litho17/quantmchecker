package plv.colorado.edu.quantmchecker

import java.util
import javax.lang.model.element.{AnnotationMirror, TypeElement}

import com.sun.source.tree._
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.QualifierHierarchy
import org.checkerframework.framework.flow.{CFAbstractAnalysis, CFStore, CFTransfer, CFValue}
import org.checkerframework.framework.util.{GraphQualifierHierarchy, MultiGraphQualifierHierarchy}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, TreeUtils}
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.qual._
import plv.colorado.edu.quantmchecker.verification.{SmtUtils, Z3Solver}

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
class QuantmAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  private val DEBUG: Boolean = false
  protected val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  protected val INC: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inc])
  protected val INVUNK: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvUnk])
  protected val INVKWN: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvKwn])
  protected val INVBOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])
  protected val INVTOP: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvTop])

  var fieldLists: HashSet[VariableTree] = HashSet.empty
  var localLists: HashSet[VariableTree] = HashSet.empty

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
    * @param v   variable name
    * @param inv invariant
    * @return if the invariant is dependent on variable v
    */
  def isDependentOn(v: String, inv: String): Boolean = SmtUtils.containsToken(inv, v)

  /**
    *
    * @param annotations
    * @return
    */
  def getTypeAnnotation(annotations: util.Collection[AnnotationMirror]): AnnotationMirror = {
    this.getQualifierHierarchy
      .findAnnotationInHierarchy(annotations, this.getQualifierHierarchy.getTopAnnotations.iterator().next())
  }

  /**
    *
    * @param rcvr tree representation of a variable
    * @return annotation of the receiver of a method invocation
    */
  def getTypeAnnotation(rcvr: Tree): AnnotationMirror = getTypeAnnotation(getAnnotatedType(rcvr).getAnnotations)

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
    * @param invTyp     a specific type of annotation
    * @return a set of collected annotations: self/self.f.g -> ...self...
    */
  def getVarAnnoMap(annotation: AnnotationMirror, invTyp: AnnotationMirror = INV): HashMap[String, String] = {
    val map = if (annotation != null && AnnotationUtils.areSameIgnoringValues(annotation, invTyp)) {
      Utils.extractArrayValues(annotation, "value").foldLeft(new HashMap[String, String]) {
        (acc, inv) =>
          // Make sure that key and values in the map are all in valid format (i.e. trimmed and no parenthesis)
          val invValidFormat = SmtUtils.rmParen(inv.trim)
          val keys = SmtUtils.startsWithToken(invValidFormat, SmtUtils.SELF)
          if (keys.nonEmpty) { // E.g. self or self.f.g
            keys.foldLeft(acc) { (acc2, t) => acc2 + (t -> invValidFormat) }
          } else { // E.g. x|c|n -> = self x|c|n
            acc + (SmtUtils.SELF -> SmtUtils.invToSMTLIB2(invValidFormat))
          }
      }
    } else {
      new HashMap[String, String]
    }
    assert(map.forall { case (v, t) => v.startsWith(SmtUtils.SELF) })
    map
  }

  /**
    *
    * @param node tree representation of a variable
    * @return a set of collected annotations: self/self.f.g -> ...self...
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

  def isListVar(v: VariableTree): Boolean = {
    types.asElement(TreeUtils.typeOf(v)) match {
      case te: TypeElement =>
        val tree: ClassTree = trees.getTree(te)
        Utils.COLLECTION_ADD.exists {
          case (klass, method) => if (klass == te.getQualifiedName.toString) true else false
        }
      case _ => false
    }
  }

  /**
    *
    * @param classTree a class definition
    * @return a typing context collected from class field declarations: v/v.f.g -> ...self...
    *         Make sure that key and values in the map are all in valid format (i.e. trimmed and no parenthesis)
    */
  def getFieldTypCxt(classTree: ClassTree): HashMap[String, String] = {
    val map = classTree.getMembers.asScala.foldLeft(new HashMap[String, String]) {
      (acc, member) =>
        member match {
          case member: VariableTree =>
            if (isListVar(member)) fieldLists = fieldLists + member
            // Get annotations on class fields
            this.getVarAnnoMap(member).foldLeft(acc) { // E.g. self.f -> v.f
              case (acc2, (v, typ)) =>
                acc2 + (SmtUtils.substitute(v, List(SmtUtils.SELF), List(member.getName.toString), true) -> typ)
            }
          case _ => acc
        }
    }
    assert(map.forall { case (v, t) => !v.startsWith(SmtUtils.SELF) })
    map
  }

  /**
    *
    * @param methodTree a method
    * @return a typing context collected from local variable declarations: v/v.f.g -> ...self...
    *         Make sure that key and values in the map are all in valid format (i.e. trimmed and no parenthesis)
    */
  def getLocalTypCxt(methodTree: MethodTree): HashMap[String, String] = {
    val map = if (methodTree.getBody != null) {
      val stmts = methodTree.getBody.getStatements.asScala.foldLeft(new HashSet[StatementTree]) {
        (acc, stmt) => acc ++ Utils.flattenStmt(stmt)
      } // ++ methodTree.getParameters.asScala

      stmts.foldLeft(new HashMap[String, String]) {
        (acc, stmt) =>
          stmt match {
            case stmt: VariableTree =>
              if (isListVar(stmt)) localLists = localLists + stmt
              // Local invariants should only be on variable declarations
              // Otherwise, invariants are simply ignored
              this.getVarAnnoMap(stmt).foldLeft(acc) { // E.g. self.f -> v.f
                case (acc2, (v, typ)) => acc2 +
                  (SmtUtils.substitute(v, List(SmtUtils.SELF), List(stmt.getName.toString), true) -> typ)
              }
            case x@_ =>
              if (x.toString.contains("@Inv(")) Utils.logging("Missed an invariant!\n" + x.toString)
              acc
          }
      }
    } else {
      new HashMap[String, String]
    }
    assert(map.forall { case (v, t) => !v.startsWith(SmtUtils.SELF) })
    map
  }

  final private class QuantmQualifierHierarchy(val factory: MultiGraphQualifierHierarchy.MultiGraphFactory) extends GraphQualifierHierarchy(factory, INVBOT) {
    override def isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean = {
      val isSubInvUnk = AnnotationUtils.areSameIgnoringValues(subAnno, INVUNK)
      val isSuperInvUnk = AnnotationUtils.areSameIgnoringValues(superAnno, INVUNK)
      val isSubInv = AnnotationUtils.areSameIgnoringValues(subAnno, INV)
      val isSuperInv = AnnotationUtils.areSameIgnoringValues(superAnno, INV)
      val isSubInc = AnnotationUtils.areSameIgnoringValues(subAnno, INC)
      val isSuperInc = AnnotationUtils.areSameIgnoringValues(superAnno, INC)
      val isSubInvKwn = AnnotationUtils.areSameIgnoringValues(subAnno, INVKWN)
      val isSuperInvKwn = AnnotationUtils.areSameIgnoringValues(superAnno, INVKWN)

      val newSubAnno = {
        if (isSubInv) INV
        else if (isSubInvUnk) INVTOP // INVUNK
        else if (isSubInc) INVTOP // INC
        else if (isSubInvKwn) INVTOP // INVKWN
        else subAnno
      }
      val newSuperAnno = {
        if (isSuperInv) INV
        else if (isSuperInvUnk) INVTOP // INVUNK
        else if (isSuperInc) INVTOP // INC
        else if (isSuperInvKwn) INVTOP // INVKWN
        else superAnno
      }

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
