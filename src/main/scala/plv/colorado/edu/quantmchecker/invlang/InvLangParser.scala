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
    accept("identifier", { case id @ IDENTIFIER(name) => id })
  }

  private def coefficient: Parser[COEFFICIENT] = {
    accept("coefficient", { case coeff @ COEFFICIENT(num) => coeff })
  }

  def invariant: Parser[InvLangAST] = {
    val le = invLeft ~ LE ~ invRight ^^ {
      case left ~ _ ~ right => Inv(left, LeAST, right)
    }
    val eq = invLeft ~ EQ ~ invRight ^^ {
      case left ~ _ ~ right => Inv(left, EqAST, right)
    }
    le | eq
  }

  def remainder: Parser[RemainderAST] = {
    (REMAINDER ~ LEFTPARENTHESIS ~ identifier ~ RIGHTPARENTHESIS ~ MUL ~ coefficient) ^^ {
      case _ ~ _ ~ IDENTIFIER(id) ~ _ ~ _ ~ COEFFICIENT(coeff) => RemainderAST(id, coeff)
    }
  }

  def list: Parser[ListAST] = {
    (LIST ~ LEFTPARENTHESIS ~ identifier ~ RIGHTPARENTHESIS) ^^ {
      case _ ~ _ ~ IDENTIFIER(id) ~ _ => ListAST(id)
    }
  }

  def limit: Parser[LimitAST] = {
    (LIMIT ~ LEFTPARENTHESIS ~ identifier ~ RIGHTPARENTHESIS) ^^ {
      case _ ~ _ ~ IDENTIFIER(id) ~ _ => LimitAST(id)
    }
  }

  /*private def invleft: Parser[InvLeft] = {
    accept("invleft", { case invleft @ InvLeft1(remainder, invRight, invLeft) => coeff })
  }*/

  def invLeft: Parser[InvLangAST] = {
    val invLeft1 = remainder ~ MUL ~ invRight ~ ADD ~ invLeft ^^ {
      case remainder ~ _ ~ invRight ~ _ ~ invLeft => InvLeft1(remainder, invRight, invLeft)
    }
    val invLeft2 = remainder ~ ADD ~ list ^^ {
      case remainder ~ _ ~ list => InvLeft2(remainder, list)
    }
    invLeft1 | invLeft2
  }

  def invRight: Parser[InvRight] = {
    val invRight1 = limit ^^ {
      case limit => InvRight1(limit)
    }
    val invRight2 = limit ~ ADD ~ EXTRA ^^ {
      case limit ~ _ ~ _ => InvRight2(limit, ExtraAST)
    }
    /*val invRight3 = LEFTPARENTHESIS ~ invRight ~ RIGHTPARENTHESIS ^^ {
      case _ ~ invright ~ _ =>invright
    }*/
    invRight1 | invRight2
  }

  def apply(tokens: Seq[InvLangToken]): Either[InvLangParserError, InvLangAST] = {
    val reader = new InvLangReader(tokens)
    invariant(reader) match {
      case NoSuccess(msg, next) => println(msg); Left(InvLangParserError(msg))
      case Success(result, next) => Right(result)
    }
  }
}
