package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
sealed trait InvLangToken

case object LEFTPARENTHESIS extends InvLangToken
case object RIGHTPARENTHESIS extends InvLangToken

case class IDENTIFIER(variable: String) extends InvLangToken
case class COEFFICIENT(coeff: Integer) extends InvLangToken


case object LIST extends InvLangToken
case object LIMIT extends InvLangToken
case object REMAINDER extends InvLangToken
case object EXTRA extends InvLangToken

sealed trait OPERATOR
case object EQ extends InvLangToken with OPERATOR
case object LE extends InvLangToken with OPERATOR
case object ADD extends InvLangToken with OPERATOR
case object MUL extends InvLangToken with OPERATOR