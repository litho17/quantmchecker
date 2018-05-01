package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
sealed trait InvLangToken

sealed trait OPERATOR
case object EQ extends InvLangToken with OPERATOR
case object ADD extends InvLangToken with OPERATOR
case object SUB extends InvLangToken with OPERATOR
case object DIV extends InvLangToken with OPERATOR

// case object SELF extends InvLangToken
case object DOT extends InvLangToken

case class IDENTIFIER(variable: String) extends InvLangToken
case class NUMBER(number: Integer) extends InvLangToken