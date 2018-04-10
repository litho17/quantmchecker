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

  private def number: Parser[NUMBER] = {
    accept("number", { case coeff@NUMBER(num) => coeff })
  }

  def remainder: Parser[RemainderAST] = {
    identifier ^^ {
      case IDENTIFIER(variable) => RemainderAST(variable)
    }
  }

  def linecounter: Parser[LinecounterAST] = {
    number ^^ {
      case NUMBER(number) => LinecounterAST(number)
    }
  }

  def self: Parser[SelfAST] = {
    SELF ~ rep(DOT ~ identifier) ^^ {
      case _ ~ fields => SelfAST(fields.map {
        x => x._2.variable
      })
    }
  }

  def invariant: Parser[InvLangAST] = {
    opt(remainder) ~ ADD ~ self ~ EQ ~ rep(ADD ~ linecounter) ~ rep(SUB ~ linecounter) ^^ {
      case remainder ~ self ~ _ ~ posLine ~ negLine =>
        remainder._1 match {
          case Some(remainderAST) => Invariant(remainderAST.variable, self.id, posLine.map { x => x._2.number }, negLine.map { x => x._2.number })
          case None => InvNoRem(self.id, posLine.map { x => x._2.number }, negLine.map { x => x._2.number })
        }
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
