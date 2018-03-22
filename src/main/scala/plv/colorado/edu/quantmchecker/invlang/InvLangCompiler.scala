package plv.colorado.edu.quantmchecker.invlang

/**
  * @author Tianhan Lu
  */
object InvLangCompiler {
  def apply(code: String): Either[InvLangCompilerError, InvLangAST] = {
    for {
      tokens <- InvLangLexer(code).right
      ast <- InvLangParser(tokens).right
    } yield ast
  }
}
