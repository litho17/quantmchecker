package plv.colorado.edu.quantmchecker

import javax.lang.model.element.AnnotationMirror

import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.QualifierHierarchy
import org.checkerframework.framework.util.{GraphQualifierHierarchy, MultiGraphQualifierHierarchy}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils}
import plv.colorado.edu.quantmchecker.qual.{InvBot, ListInv}
import plv.colorado.edu.quantmchecker.utils.AnnoTypeUtils

/**
  * @author Tianhan Lu
  */
class QuantmAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  private val DEBUG: Boolean = false
  protected val LISTINV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[ListInv])
  protected val INVBOT: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[InvBot])

  // disable flow inference
  // super(checker, false);
  this.postInit()
  if (DEBUG) {
    println(getQualifierHierarchy.toString)
    // getTypeHierarchy();
  }

  // Learned from KeyForAnnotatedTypeFactory.java
  override def createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy = new QuantmQualifierHierarchy(factory)

  final private class QuantmQualifierHierarchy(val factory: MultiGraphQualifierHierarchy.MultiGraphFactory) extends GraphQualifierHierarchy(factory, INVBOT) {
    override def isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean = {
      if (AnnotationUtils.areSameIgnoringValues(superAnno, LISTINV) && AnnotationUtils.areSameIgnoringValues(subAnno, LISTINV)) {
        val lhsValues = AnnoTypeUtils.extractValues(superAnno)
        val rhsValues = AnnoTypeUtils.extractValues(subAnno)
        // return rhsValues.containsAll(lhsValues);
        return false
      }
      // Ignore annotation values to ensure that annotation is in supertype map.
      val newSuperAnno = if (AnnotationUtils.areSameIgnoringValues(superAnno, LISTINV)) LISTINV else superAnno
      val newSubAnno = if (AnnotationUtils.areSameIgnoringValues(subAnno, LISTINV)) LISTINV else subAnno
      super.isSubtype(newSubAnno, newSuperAnno)
    }
  }
}
