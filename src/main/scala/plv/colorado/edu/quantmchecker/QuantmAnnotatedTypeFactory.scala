package plv.colorado.edu.quantmchecker

import javax.lang.model.element.AnnotationMirror

import com.sun.source.tree.Tree
import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.QualifierHierarchy
import org.checkerframework.framework.util.{GraphQualifierHierarchy, MultiGraphQualifierHierarchy}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils}
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.qual.{Inv, InvBot, InvBounded}

/**
  * @author Tianhan Lu
  */
class QuantmAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  private val DEBUG: Boolean = false
  protected val INV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
  protected val INVBOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])
  protected val INVBOUNDED: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBounded])

  // disable flow inference
  // super(checker, false);
  this.postInit()
  if (DEBUG) {
    println(getQualifierHierarchy.toString)
    // getTypeHierarchy();
  }

  // Learned from KeyForAnnotatedTypeFactory.java
  override def createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy = new QuantmQualifierHierarchy(factory)

  /**
    *
    * @param rcvr
    * @return annotation of the receiver of a method invocation
    */
  def getTypeAnnotation(rcvr: Tree): AnnotationMirror = {
    this.getQualifierHierarchy()
      .findAnnotationInHierarchy(
        getAnnotatedType(rcvr).getAnnotations(),
        this.getQualifierHierarchy().getTopAnnotations().iterator().next())
  }

  final private class QuantmQualifierHierarchy(val factory: MultiGraphQualifierHierarchy.MultiGraphFactory) extends GraphQualifierHierarchy(factory, INVBOT) {
    override def isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean = {
      if (AnnotationUtils.areSameIgnoringValues(superAnno, INV) && AnnotationUtils.areSameIgnoringValues(subAnno, INV)) {
        val lhsValues = Utils.extractValues(superAnno)
        val rhsValues = Utils.extractValues(subAnno)
        // return rhsValues.containsAll(lhsValues);
        return false
      }
      // Ignore annotation values to ensure that annotation is in supertype map.
      val newSuperAnno = if (AnnotationUtils.areSameIgnoringValues(superAnno, INV)) INV else superAnno
      val newSubAnno = if (AnnotationUtils.areSameIgnoringValues(subAnno, INV)) INV else subAnno
      if (DEBUG && !super.isSubtype(newSubAnno, newSuperAnno)) {
        println(subAnno, newSubAnno)
        println(superAnno, newSuperAnno)
      }
      super.isSubtype(newSubAnno, newSuperAnno)
    }
  }
}
