package plv.colorado.edu.listaddchecker

import org.checkerframework.common.basetype.{BaseAnnotatedTypeFactory, BaseTypeChecker}

/**
  * @author Tianhan Lu
  */
class ListaddAnnotatedTypeFactory (checker: BaseTypeChecker) extends BaseAnnotatedTypeFactory(checker) {
  this.postInit()
}
