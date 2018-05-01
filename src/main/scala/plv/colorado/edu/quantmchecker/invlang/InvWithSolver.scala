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

  /**
    *
    * @param inv       an invariant
    * @param remainder the remainder to update and how much to increment
    * @param self      the self to update and how much to increment
    * @param label     label of the line that is currently visiting
    * @param node      the AST node (only for debug)
    * @return if the invariant holds before visiting current line,
    *         returns if the invariant still holds after executing current line
    */
  def isValidAfterUpdate(inv: InvLangAST,
                         remainder: (String, Int),
                         self: (String, Int),
                         label: String,
                         node: Tree): Boolean = {
    val result = isValidAfterUpdate(inv, remainder, self, label)
    if (DEBUG && !result)
      PrintStuff.printRedString("Invariant invalidated!", "label: " + label, "code: " + node)
    result
  }

  def isValidAfterUpdate(inv: InvLangAST,
                         remainder: (String, Int),
                         self: (String, Int),
                         label: String): Boolean = {
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
      * @param op        the operator
      * @return a linear constraint that connects all ast nodes with the specified operator
      */
    def listToPredicate(variables: List[Z3AST], op: OPERATOR): Z3AST = {
      variables.foldLeft(mkInt(0): Z3AST) {
        (acc, variable) =>
          op match {
            case ADD => z3.mkAdd(acc, variable)
            case SUB => z3.mkSub(acc, variable)
          }
      }
    }

    def genLhs(selfs: List[Z3AST]): Z3AST = {
      z3.simplifyAst(listToPredicate(selfs, ADD))
    }

    def genRhs(remainders: List[Z3AST], pos: List[Z3AST], neg: List[Z3AST]): Z3AST = {
      z3.simplifyAst(z3.mkAdd(listToPredicate(remainders, SUB), z3.mkAdd(listToPredicate(pos, ADD), listToPredicate(neg, SUB))))
    }

    val (remainders: List[String], selfs: List[String]) = InvUtils.extractInv(inv)
    val (posLine: List[String], negLine: List[String]) = inv match {
      case Invariant(_, _, _posLine, _negLine) => (_posLine, _negLine)
      case _ => (List.empty, List.empty)
    }

    val selfSym: List[Z3Symbol] = selfs.map { s => z3.mkSymbol(s) }
    val remSym: List[Z3Symbol] = remainders.map { r => z3.mkSymbol(r) }
    val posSym: List[Z3Symbol] = posLine.map { l => z3.mkSymbol(l.toString) }
    val negSym: List[Z3Symbol] = negLine.map { l => z3.mkSymbol(l.toString) }
    val symbols: List[Z3Symbol] = selfSym ::: remSym ::: posSym ::: negSym

    val oldSelf: List[Z3AST] = selfSym.map { s => z3.mkIntConst(s) }
    val oldRem: List[Z3AST] = remSym.map { r => z3.mkIntConst(r) }
    val pos: List[Z3AST] = posSym.map { l => z3.mkIntConst(l) }
    val neg: List[Z3AST] = negSym.map { l => z3.mkIntConst(l) }
    val oldLhs: Z3AST = genLhs(oldSelf)
    val oldRhs: Z3AST = genRhs(oldRem, pos, neg)

    val newSelf = if (selfs.contains(self._1)) {
      val idx = selfs.indexOf(self._1)
      oldSelf.updated(idx, z3.mkAdd(oldSelf(idx), mkInt(self._2)))
    } else oldSelf
    val newRem = if (remainders.contains(remainder._1)) {
      val idx = remainders.indexOf(remainder._1)
      oldRem.updated(idx, z3.mkAdd(oldRem(idx), mkInt(remainder._2)))
    } else oldRem
    val newPos: List[Z3AST] = if (posLine.contains(label)) {
      val idx = posLine.indexOf(label)
      pos.updated(idx, z3.mkAdd(pos(idx), mkInt(1)))
    } else pos
    val newNeg: List[Z3AST] = if (negLine.contains(label)) {
      val idx = negLine.indexOf(label)
      neg.updated(idx, z3.mkAdd(neg(idx), mkInt(1)))
    } else neg
    val newLhs: Z3AST = genLhs(newSelf)
    val newRhs: Z3AST = genRhs(newRem, newPos, newNeg)

    val (p, q) = inv match {
      case Invariant(_, _, _, _) =>
        val P = z3.mkEq(oldLhs, oldRhs)
        val Q = z3.mkEq(newLhs, newRhs)
        (P, Q)
      case _ => (z3.mkTrue(), z3.mkTrue())
    }

    // val imply = z3.mkImplies(p, q)
    /**
      * TODO: It seems that, if we don't assert p and q also must hold,
      * then the solver will say SAT, because if p is false, then p=>q will always be SAT
      */
    val constraints = z3.mkAnd(p, q) // z3.mkAnd(p, imply) is same as p /\ q
    val forall = z3.mkForall(0, Seq.empty, symbols.map(sym => (sym, z3.mkIntSort())), constraints)
    // z3.benchmarkToSMTLIBString("name", "logic", "status", "attributes", List.empty, imply)
    if (DEBUG) {
      println("P: " + p)
      println("Q: " + q)
      println(forall)
    }
    val result = check(forall)
    val estimatedTime = System.nanoTime - startTime

    println("Time elapsed: " + ("%.2f" format estimatedTime.toDouble / 1000000) + "ms" + " [label:" + label + "][" + inv + "]")
    result
  }
}
