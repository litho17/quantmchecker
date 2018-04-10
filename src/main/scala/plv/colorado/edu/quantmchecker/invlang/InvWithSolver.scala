package plv.colorado.edu.quantmchecker.invlang

import com.sun.source.tree.Tree
import plv.colorado.edu.quantmchecker.utils.PrintStuff
import z3.scala.{Z3AST, Z3Context, Z3Symbol}

/**
  * @author Tianhan Lu
  */
object InvWithSolver {
  private val DEBUG = true

  val z3 = new Z3Context("MODEL" -> true)
  val solver = z3.mkSolver

  def isValidAfterUpdate(inv: InvLangAST, remainder: Int, self: Int, line: Int, node: Tree): Boolean = {
    val result = isValidAfterUpdate(inv, remainder, self, line)
    if (DEBUG && !result)
      PrintStuff.printRedString(line, node)
    result
  }

  /**
    *
    * @param inv       the invariant
    * @param remainder the increment of remainder
    * @param self      the increment of self
    * @param line      the line number that is currently visiting
    * @return if the invariant holds before visiting current line,
    *         returns if the invariant still holds after executing current line
    */
  def isValidAfterUpdate(inv: InvLangAST, remainder: Int, self: Int, line: Int): Boolean = {
    val startTime = System.nanoTime()
    val DEBUG = false

    trait OPERATOR
    object ADD extends OPERATOR
    object SUB extends OPERATOR

    solver.reset()

    def mkInt(i: Int): Z3AST = z3.mkInt(i, z3.mkIntSort())

    /**
      *
      * @param constraint a constraint
      * @return if the constraint is SAT
      */
    def check(constraint: Z3AST): Boolean = {
      solver.assertCnstr(constraint)
      solver.check() match {
        case Some(v) =>
          if (DEBUG && v) println(solver.getModel())
          v
        case None => false
      }
    }

    /**
      *
      * @param variables a list of Z3 ast nodes
      * @param op the operator
      * @return a linear constraint that connects all ast nodes with the specified operator
      */
    def listToPred(variables: List[Z3AST], op: OPERATOR): Z3AST = {
      variables.foldLeft(mkInt(0): Z3AST) {
        (acc, variable) =>
          op match {
            case ADD => z3.mkAdd(acc, variable)
            case SUB => z3.mkSub(acc, variable)
          }
      }
    }

    val (posLine: List[Int], negLine: List[Int]) = inv match {
      case Invariant(_remainder, _self, _posLine, _negLine) => (_posLine, _negLine)
      case InvNoRem(_self, _posLine, _negLine) => (_posLine, _negLine)
      case _ => (List.empty, List.empty)
    }

    val selfSym: Z3Symbol = z3.mkSymbol("self")
    val posSym: List[Z3Symbol] = posLine.map { l => z3.mkSymbol("l" + l.toString) }
    val negSym: List[Z3Symbol] = negLine.map { l => z3.mkSymbol("l" + l.toString) }
    val symbols: List[Z3Symbol] = selfSym :: posSym ::: negSym

    val oldSelf = z3.mkIntConst(selfSym)
    val pos: List[Z3AST] = posSym.map { l => z3.mkIntConst(l) }
    val neg: List[Z3AST] = negSym.map { l => z3.mkIntConst(l) }
    val rhs: Z3AST = z3.simplifyAst(z3.mkAdd(listToPred(pos, ADD), listToPred(neg, SUB)))

    val newSelf: Z3AST = z3.mkAdd(oldSelf, mkInt(self))
    val newPos: List[Z3AST] = if (posLine.contains(line)) {
      val idx = posLine.indexOf(line)
      pos.updated(idx, z3.mkAdd(pos(idx), mkInt(1)))
    } else pos
    val newNeg: List[Z3AST] = if (negLine.contains(line)) {
      val idx = negLine.indexOf(line)
      neg.updated(idx, z3.mkAdd(neg(idx), mkInt(1)))
    } else neg
    val newRhs: Z3AST = z3.simplifyAst(z3.mkAdd(listToPred(newPos, ADD), listToPred(newNeg, SUB)))

    val (p, q, newSyms) = inv match {
      case Invariant(_, _, _, _) =>
        val remainderSym = z3.mkSymbol("rem")
        val oldRemainder = z3.mkIntConst(remainderSym)
        val newRemainder = z3.mkAdd(oldRemainder, mkInt(remainder))

        val P = z3.mkEq(z3.mkAdd(oldRemainder, oldSelf), rhs)
        val Q = z3.mkEq(z3.mkAdd(newRemainder, newSelf), newRhs)
        (P, Q, remainderSym :: symbols)
      case InvNoRem(_, _, _) =>
        val P = z3.mkEq(oldSelf, rhs)
        val Q = z3.mkEq(newSelf, newRhs)
        (P, Q, symbols)
      case _ => (z3.mkTrue(), z3.mkTrue(), symbols)
    }

    // val imply = z3.mkImplies(p, q)
    /**
      * TODO: It seems that, if we don't assert p and q also must hold,
      * then the solver will say SAT, because if p is false, then p=>q will always be SAT
      */
    val constraints = z3.mkAnd(p, q) // z3.mkAnd(p, imply) is same as p /\ q
    val forall = z3.mkForall(0, Seq.empty, newSyms.map(sym => (sym, z3.mkIntSort())), constraints)
    // z3.benchmarkToSMTLIBString("name", "logic", "status", "attributes", List.empty, imply)
    if (DEBUG) {
      println("P: " + p)
      println("Q: " + q)
      println(forall)
    }
    val result = check(forall)
    val estimatedTime = System.nanoTime - startTime

    println("Time elapsed: " + ("%.2f" format estimatedTime.toDouble/1000000) + "ms" + " [line:" + line + "][" + inv + "]")
    result
  }
}
