package plv.colorado.edu.quantmchecker

import javax.lang.model.element.AnnotationMirror

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
  protected val LISTINV: AnnotationMirror = AnnotationBuilder.fromClass(elements, classOf[Inv])
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

  final private class QuantmQualifierHierarchy(val factory: MultiGraphQualifierHierarchy.MultiGraphFactory) extends GraphQualifierHierarchy(factory, INVBOT) {
    override def isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean = {
      /*val subSameList = AnnotationUtils.areSameIgnoringValues(subAnno, LISTINV)
      val superSameList = AnnotationUtils.areSameIgnoringValues(superAnno, LISTINV)

      (subSameList, superSameList) match {
        case (true, true) =>
          val lhsValues = Utils.extractValues(superAnno)
          val rhsValues = Utils.extractValues(subAnno)
          lhsValues == rhsValues
        case (true, false) =>
          val newSubAnno = if (AnnotationUtils.areSameIgnoringValues(subAnno, LISTINV)) LISTINV else subAnno
          if (superAnno == INVBOUNDED)
            true
          else
            super.isSubtype(newSubAnno, superAnno)
        case (false, true) =>
          val newSuperAnno = if (AnnotationUtils.areSameIgnoringValues(superAnno, LISTINV)) LISTINV else superAnno
          super.isSubtype(subAnno, newSuperAnno)
        case (false, false) => super.isSubtype(subAnno, superAnno)
      }*/

      if (AnnotationUtils.areSameIgnoringValues(superAnno, LISTINV) && AnnotationUtils.areSameIgnoringValues(subAnno, LISTINV)) {
        val lhsValues = Utils.extractValues(superAnno)
        val rhsValues = Utils.extractValues(subAnno)
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
