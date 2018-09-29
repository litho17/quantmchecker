package plv.colorado.edu.quantmchecker

import java.util

import com.sun.source.tree._
import javax.lang.model.element.AnnotationMirror
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.QualifierHierarchy
import org.checkerframework.framework.flow.{CFAbstractAnalysis, CFStore, CFTransfer, CFValue}
import org.checkerframework.framework.util.{GraphQualifierHierarchy, MultiGraphQualifierHierarchy}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, TreeUtils}
import plv.colorado.edu.quantmchecker.qual._
import plv.colorado.edu.quantmchecker.verification.SmtUtils
import plv.colorado.edu.{TypCxt, Utils, VarTyp}

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
class QuantmAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  private val DEBUG: Boolean = false
  val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  val INC: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inc])
  val INVUNK: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvUnk])
  val INVKWN: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvKwn])
  val INVBOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])
  val INVTOP: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvTop])
  val INPUT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Input])
  val SUMMARY: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Summary])

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

  def getTypeAnnotation(annotations: util.Collection[AnnotationMirror]): AnnotationMirror = {
    this.getQualifierHierarchy
      .findAnnotationInHierarchy(annotations, this.getQualifierHierarchy.getTopAnnotations.iterator().next())
  }

  /**
    *
    * @param rcvr tree representation of a variable
    * @return annotation of the receiver of a method invocation
    */
  def getTypeAnnotation(rcvr: Tree): AnnotationMirror = {
    val annotations: util.Collection[_ <: AnnotationMirror] = rcvr match {
      case s: VariableTree =>
        // I don't understand why the following does not work
        // TreeUtils.elementFromDeclaration(s).getAnnotationMirrors
        // atypeFactory.getDeclAnnotations(TreeUtils.elementFromDeclaration(s))
        TreeUtils.elementFromDeclaration(s).asType().getAnnotationMirrors
      case _ => getAnnotatedType(rcvr).getAnnotations
    }
    val filter: util.Collection[AnnotationMirror] = annotations.asScala
      .filter(p => AnnotationUtils.areSameIgnoringValues(p, INV) || AnnotationUtils.areSameIgnoringValues(p, INPUT))
      .map(anno => anno.asInstanceOf[AnnotationMirror]).asJavaCollection
    getTypeAnnotation(filter)
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

  private def getVarAnnoMap(annoMirror: AnnotationMirror): (String, Boolean) = {
    if (annoMirror == null) return (SmtUtils.TRUE, false)
    val isInput = {
      if (AnnotationUtils.areSameIgnoringValues(annoMirror, INV)) false
      else if (AnnotationUtils.areSameIgnoringValues(annoMirror, INPUT)) true
      else false
    }
    // Make sure that key and values in the map are all in valid format (i.e. trimmed and no parenthesis)
    val annotations =
      Utils.extractArrayValues(annoMirror, "value").map(s => SmtUtils.rmParen(s.trim)).toSet
    // Only use the first element in the annotation string array as the type refinement
    (annotations.head, isInput)
  }

  def getVarAnnoMap(node: Tree): VarTyp = {
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
    val annotations = getTypeAnnotation(node) // TODO: Null if variable is array type
    val res = getVarAnnoMap(annotations)
    node match {
      case v: VariableTree => VarTyp(TreeUtils.elementFromDeclaration(v), res._1, res._2)
      case _ => ???
    }
  }

  def getFieldTypCxt(classTree: ClassTree): TypCxt = {
    if (classTree == null) return TypCxt(new HashSet[VarTyp])
    val typs = classTree.getMembers.asScala.foldLeft(new HashSet[VarTyp]) {
      (acc, member) =>
        member match {
          case member: VariableTree =>
            // Get annotations on class fields
            // We consider class fields as inputs (e.g. this.f is an input variable to a member method)
            val varTyp = this.getVarAnnoMap(member)
            acc + VarTyp(varTyp.varElement, varTyp.anno, true)
          case _ => acc
        }
    }
    TypCxt(typs)
  }

  def getLocalTypCxt(methodTree: MethodTree, includeParameters: Boolean): TypCxt = {
    if (methodTree == null || methodTree.getBody == null) return TypCxt(new HashSet[VarTyp])
    val stmts = {
      val ret = methodTree.getBody.getStatements.asScala.foldLeft(new HashSet[StatementTree]) {
        (acc, stmt) => acc ++ Utils.flattenStmt(stmt)
      }
      if (includeParameters) ret ++ methodTree.getParameters.asScala
      else ret
    }

    val typs = stmts.foldLeft(new HashSet[VarTyp]) {
      (acc, stmt) =>
        stmt match {
          case stmt: VariableTree => acc + this.getVarAnnoMap(stmt)
          case x@_ =>
            if (x.toString.contains("@Inv(")) Utils.logging("Missed an invariant!\n" + x.toString)
            acc
        }
    }
    TypCxt(typs)
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
      val isSubInput = AnnotationUtils.areSameIgnoringValues(subAnno, INPUT)
      val isSuperInput = AnnotationUtils.areSameIgnoringValues(superAnno, INPUT)

      val newSubAnno = {
        if (isSubInv) INV
        else if (isSubInvUnk) INVTOP // @InvUnk
        else if (isSubInc) INVTOP // @Inc
        else if (isSubInvKwn) INVTOP // @InvKwn
        else if (isSubInput) INVTOP // @Input
        else subAnno
      }
      val newSuperAnno = {
        if (isSuperInv) INV
        else if (isSuperInvUnk) INVTOP // @InvUnk
        else if (isSuperInc) INVTOP // @Inc
        else if (isSuperInvKwn) INVTOP // @InvKwn
        else if (isSuperInput) INVTOP // @Input
        else superAnno
      }

      // Check subtyping for base types
      super.isSubtype(newSubAnno, newSuperAnno)
    }
  }

}