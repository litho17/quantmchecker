package plv.colorado.edu.quantmchecker.invlang

import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.input.{NoPosition, Reader}

/**
  * @author Tianhan Lu
  */
object InvLangParser extends PackratParsers {
  override type Elem = InvLangToken

  class InvLangReader(tokens: Seq[InvLangToken]) extends Reader[InvLangToken] {
    override def first: InvLangToken = tokens.head

    override def atEnd: Boolean = tokens.isEmpty

    override def pos = NoPosition

    override def rest: Reader[InvLangToken] = new InvLangReader(tokens.tail)
  }

  private def identifier: Parser[IDENTIFIER] = {
    accept("identifier", { case id@IDENTIFIER(name) => id })
  }

  /*private def number: Parser[NUMBER] = {
    accept("number", { case coeff@NUMBER(num) => coeff })
  }*/

  def linecounter: Parser[LineCounterAST] = {
    identifier ^^ {
      case IDENTIFIER(id) => LineCounterAST(id)
    }
  }

  def remainder: Parser[RemainderAST] = {
    identifier ~ rep(DOT ~ identifier) ^^ {
      case id ~ members => RemainderAST(id.variable, members.map {
        x => x._2.variable
      })
    }
  }

  def self: Parser[SelfAST] = {
    identifier ~ rep(DOT ~ identifier) ~ DIV ^^ {
      case id ~ members ~ _ => SelfAST(id.variable, members.map {
        x => x._2.variable
      })
    }
  }

  def invariant: Parser[InvLangAST] = {
    rep(ADD ~ self) ~ EQ ~ rep(SUB ~ remainder) ~ rep(ADD ~ linecounter) ~ rep(SUB ~ linecounter) ^^ {
      case self ~ _ ~ remainder ~ posLine ~ negLine =>
        val remainders = remainder.map { x => x._2 }
        val selfs = self.map { x => x._2 }
        val posLines = posLine.map { x => x._2.id }
        val negLines = negLine.map { x => x._2.id }
        Invariant(remainders, selfs, posLines, negLines)
    }
  }

  def apply(tokens: Seq[InvLangToken]): Either[InvLangParserError, InvLangAST] = {
    val reader = new InvLangReader(tokens)
    invariant(reader) match {
      case NoSuccess(msg, next) => println(msg); Left(InvLangParserError(msg))
      case Success(result, next) => Right(result)
    }
  }
}
