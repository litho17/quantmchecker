package plv.colorado.edu.quantmchecker

import java.util
import javax.lang.model.element.AnnotationMirror

import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}
import org.checkerframework.framework.`type`.QualifierHierarchy
import org.checkerframework.framework.util.{GraphQualifierHierarchy, MultiGraphQualifierHierarchy}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils}
import plv.colorado.edu.quantmchecker.qual.{InvBot, ListInv}

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

  override // Learned from KeyForAnnotatedTypeFactory.java
  def createQualifierHierarchy(factory: MultiGraphQualifierHierarchy.MultiGraphFactory): QualifierHierarchy = new QuantmQualifierHierarchy(factory)

  final private class QuantmQualifierHierarchy(val factory: MultiGraphQualifierHierarchy.MultiGraphFactory) extends GraphQualifierHierarchy(factory, INVBOT) {
    private def extractValues(anno: AnnotationMirror): util.List[String] = {
      val valMap = anno.getElementValues
      var res: util.List[String] = null
      if (valMap.isEmpty) res = new util.ArrayList[String]
      else res = AnnotationUtils.getElementValueArray(anno, "value", classOf[String], true)
      res
    }

    override def isSubtype(subAnno: AnnotationMirror, superAnno: AnnotationMirror): Boolean = {
      if (AnnotationUtils.areSameIgnoringValues(superAnno, LISTINV) && AnnotationUtils.areSameIgnoringValues(subAnno, LISTINV)) {
        val lhsValues: util.List[String] = extractValues(superAnno)
        val rhsValues: util.List[String] = extractValues(subAnno)
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
