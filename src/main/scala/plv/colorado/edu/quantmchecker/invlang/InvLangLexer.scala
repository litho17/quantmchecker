package plv.colorado.edu.quantmchecker.invlang

import scala.util.parsing.combinator.RegexParsers

/**
  * @author Tianhan Lu
  */
object InvLangLexer extends RegexParsers {
  override def skipWhitespace = true
  override val whiteSpace = "[ \t\r\f]+".r

  private val idRegex = "[a-zA-Z_][a-zA-Z0-9_]*"
  private val predParenthesis = "(?<=\\()"
  private val succParenthesis = "(?=\\))"
  // Reference: https://stackoverflow.com/questions/24564872/how-do-i-match-the-contents-of-parenthesis-in-a-scala-regular-expression

  def identifier: Parser[IDENTIFIER] = {
    idRegex.r ^^ { str => IDENTIFIER(str) }
  }

  def coefficient: Parser[COEFFICIENT] = {
    "[0-9]+".r ^^ { str => COEFFICIENT(str.toInt) }
  }

  def leftparen = "(" ^^ (_ => LEFTPARENTHESIS)
  def rightparen = ")" ^^ (_ => RIGHTPARENTHESIS)
  def limit = "LIMIT" ^^ (_ => LIMIT)
  def remainder = "REM" ^^ (_ => REMAINDER)
  def list = "LIST" ^^ (_ => LIST)
  def extra = "_extra" ^^ (_ => EXTRA)
  def eq = "=" ^^ (_ => EQ)
  def le = "<=" ^^ (_ => LE)
  def add = "+" ^^ (_ => ADD)
  // def mul = "\\*" ^^ (_ => MUL)
  def mul = "*" ^^ (_ => MUL)

  def tokens: Parser[Seq[InvLangToken]] = {
    phrase(rep1(limit | remainder | list | extra | identifier | le | eq | add | mul | coefficient | leftparen | rightparen))
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
