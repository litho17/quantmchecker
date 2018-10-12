package plv.colorado.edu.quantmchecker

import java.util

import com.sun.source.tree._
import javax.lang.model.element.{AnnotationMirror, VariableElement}
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.QualifierHierarchy
import org.checkerframework.framework.flow.{CFAbstractAnalysis, CFStore, CFTransfer, CFValue}
import org.checkerframework.framework.util.{GraphQualifierHierarchy, MultiGraphQualifierHierarchy}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, TreeUtils}
import plv.colorado.edu.quantmchecker.qual._
import plv.colorado.edu.quantmchecker.verification.SmtUtils
import plv.colorado.edu.{TypCxt, Utils, VarProp, VarTyp}

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
class QuantmAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  private val DEBUG: Boolean = false
  val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  val ITER: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Iter])
  val INVUNK: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvUnk])
  val BOUND: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Bound])
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
    * @param set a set of type annotations that we care
    * @return annotation of the receiver of a method invocation
    */
  def getTypeAnnotation(rcvr: Tree, set: Set[AnnotationMirror]): AnnotationMirror = {
    val annotations: util.Collection[_ <: AnnotationMirror] = rcvr match {
      case s: VariableTree =>
        // I don't understand why the following does not work
        // TreeUtils.elementFromDeclaration(s).getAnnotationMirrors
        // atypeFactory.getDeclAnnotations(TreeUtils.elementFromDeclaration(s))
        TreeUtils.elementFromDeclaration(s).asType().getAnnotationMirrors
      case _ => getAnnotatedType(rcvr).getAnnotations
    }
    val filter: util.Collection[AnnotationMirror] = annotations.asScala
      .filter(p => set.exists(anno => AnnotationUtils.areSameIgnoringValues(p, anno)))
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

  private def getVarAnnoMap(annoMirror: AnnotationMirror): (String, VarProp) = {
    if (annoMirror == null) return (SmtUtils.TRUE, VarProp(false, false, false, false, false))
    val isInv = {
      if (AnnotationUtils.areSameIgnoringValues(annoMirror, INV)) true
      else false
    }
    val isInput = {
      if (AnnotationUtils.areSameIgnoringValues(annoMirror, INPUT)) true
      else false
    }
    val isBound = {
      if (AnnotationUtils.areSameIgnoringValues(annoMirror, BOUND)) true
      else false
    }
    val isIter = {
      if (AnnotationUtils.areSameIgnoringValues(annoMirror, ITER)) true
      else false
    }
    val isUnk = {
      if (AnnotationUtils.areSameIgnoringValues(annoMirror, INVUNK)) true
      else false
    }
    // Make sure that key and values in the map are all in valid format (i.e. trimmed and no parenthesis)
    val annotations =
      Utils.extractArrayValues(annoMirror, "value").map(s => SmtUtils.rmParen(s.trim)).toSet
    // Only use the first element in the annotation string array as the type refinement
    (annotations.head, VarProp(isInv, isInput, isBound, isIter, isUnk))
  }

  def getVarAnnoMap(node: Tree): (VariableElement, String, VarProp) = {
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
    val annoTyps = HashSet[AnnotationMirror](ITER, INPUT, BOUND, INV, INVUNK)
    val annotations = getTypeAnnotation(node, annoTyps) // TODO: Null if variable is array type
    val res = getVarAnnoMap(annotations)
    node match {
      case v: VariableTree => (TreeUtils.elementFromDeclaration(v), res._1, res._2)
      case _ => ???
    }
    // variable element, annotation, isInput, isBound, isIter
  }

  def getFieldTypCxt(classTree: ClassTree): TypCxt = {
    if (classTree == null) return TypCxt(new HashSet[VarTyp])
    val typs = classTree.getMembers.asScala.foldLeft(new HashSet[VarTyp]) {
      (acc, member) =>
        member match {
          case member: VariableTree =>
            // Get annotations on class fields
            // We consider class fields as inputs, but NOT bounds
            val res = getVarAnnoMap(member)
            acc + VarTyp(res._1, res._2, res._3, true, false)
          case _ => acc
        }
    }
    TypCxt(typs)
  }

  def getLocalTypCxt(methodTree: MethodTree, includeParameters: Boolean): TypCxt = {
    if (methodTree == null || methodTree.getBody == null) return TypCxt(new HashSet[VarTyp])
    val parameterDecl: Set[VariableTree] = methodTree.getParameters.asScala.toSet
    val stmts = {
      parameterDecl ++ methodTree.getBody.getStatements.asScala.foldLeft(new HashSet[StatementTree]) {
        (acc, stmt) => acc ++ Utils.flattenStmt(stmt)
      }
    }

    val typs = stmts.foldLeft(new HashSet[VarTyp]) {
      (acc, stmt) =>
        stmt match {
          case stmt: VariableTree =>
            val res = getVarAnnoMap(stmt)
            val isParameter = parameterDecl.contains(stmt)
            if (includeParameters)
              acc + VarTyp(res._1, res._2, res._3, false, isParameter)
            else {
              if (isParameter) acc
              else acc + VarTyp(res._1, res._2, res._3, false, isParameter)
            }
          case x@_ =>
            if (x.toString.contains("@Inv")) Utils.logging("Missed an invariant!\n" + x.toString)
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
      val isSubIter = AnnotationUtils.areSameIgnoringValues(subAnno, ITER)
      val isSuperIter = AnnotationUtils.areSameIgnoringValues(superAnno, ITER)
      val isSubBound = AnnotationUtils.areSameIgnoringValues(subAnno, BOUND)
      val isSuperBound = AnnotationUtils.areSameIgnoringValues(superAnno, BOUND)
      val isSubInput = AnnotationUtils.areSameIgnoringValues(subAnno, INPUT)
      val isSuperInput = AnnotationUtils.areSameIgnoringValues(superAnno, INPUT)

      val newSubAnno = {
        if (isSubInv) INV
        else if (isSubInvUnk) INVTOP // @InvUnk
        else if (isSubIter) INVTOP // @Iter
        else if (isSubBound) INVTOP // @Bound
        else if (isSubInput) INVTOP // @Input
        else subAnno
      }
      val newSuperAnno = {
        if (isSuperInv) INV
        else if (isSuperInvUnk) INVTOP // @InvUnk
        else if (isSuperIter) INVTOP // @Iter
        else if (isSuperBound) INVTOP // @Bound
        else if (isSuperInput) INVTOP // @Input
        else superAnno
      }

      // Check subtyping for base types
      super.isSubtype(newSubAnno, newSuperAnno)
    }
  }

}