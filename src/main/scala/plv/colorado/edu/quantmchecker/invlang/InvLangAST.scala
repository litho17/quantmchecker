package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
sealed trait InvLangAST

sealed trait InvRight extends InvLangAST
case class InvRight1(limit: LimitAST) extends InvRight
case class InvRight2(limit: LimitAST, extra: InvLangAST) extends InvRight

case object ExtraAST extends InvLangAST
case object LeAST extends InvLangAST
case object EqAST extends InvLangAST

case class RemainderAST(variable: String, coefficient: Int) extends InvLangAST
case class ListAST(variable: String) extends InvLangAST
case class LimitAST(variable: String) extends InvLangAST

sealed trait InvLeft extends InvLangAST
case class InvLeft1(remainder: RemainderAST, invRight: InvLangAST, invLeft: InvLangAST) extends InvLangAST
case class InvLeft2(remainder: RemainderAST, list: ListAST) extends InvLangAST

case class Inv(invLeft: InvLangAST, compare: InvLangAST, invRight: InvLangAST) extends InvLangAST