package plv.colorado.edu.emptychecker

import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}

/**
  * @author Tianhan Lu
  */
class EmptyAnnotatedTypeFactory(checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  this.postInit()
}
