package plv.colorado.edu.quantmchecker.invlang

import scala.util.parsing.combinator.RegexParsers

/**
  * @author Tianhan Lu
  */
object InvLangLexer extends RegexParsers {
  override def skipWhitespace = true

  override val whiteSpace = "[ \t\r\f]+".r

  private val idRegex = "[a-zA-Z_][a-zA-Z0-9_]*"
  // Reference: https://stackoverflow.com/questions/24564872/how-do-i-match-the-contents-of-parenthesis-in-a-scala-regular-expression

  def identifier: Parser[IDENTIFIER] = {
    idRegex.r ^^ { str => IDENTIFIER(str) }
  }

  def number: Parser[NUMBER] = {
    "[0-9]+".r ^^ { str => NUMBER(str.toInt) }
  }

  def eq = "=" ^^ (_ => EQ)

  def add = "+" ^^ (_ => ADD)

  def sub = "-" ^^ (_ => SUB)

  def dot = "." ^^ (_ => DOT)

  def div = "/" ^^ (_ => DIV)

  // def self = "<self>" ^^ (_ => SELF)

  def tokens: Parser[Seq[InvLangToken]] = {
    phrase(rep1(number | identifier | eq | add | sub | dot | div))
  }

  def apply(code: String): Either[InvLangLexerError, Seq[InvLangToken]] = {
    parse(tokens, code) match {
      case NoSuccess(msg, next) => println(msg); Left(InvLangLexerError(msg))
      case Success(result, next) => Right(result)
    }
  }

  /**
    * Reference: https://enear.github.io/2016/03/31/parser-combinators/
    */
}
