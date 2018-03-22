package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
trait InvLangCompilerError
case class InvLangLexerError(msg: String) extends InvLangCompilerError
case class InvLangParserError(msg: String) extends InvLangCompilerError
