package plv.colorado.edu.quantmchecker.verification

import com.microsoft.z3.AST
import com.sun.source.tree._
import plv.colorado.edu.Utils

import scala.collection.JavaConverters._

/**
  * @author Tianhan Lu
  */
class CFRelation(tree: StatementTree, solver: Z3Solver) {
  val DEFAULT_LOOP_BOUND = 1000

  val constraints: List[AST] = treeToCons(tree)

  private def genEqCons(stmts: Set[Tree]): List[AST] = {
    if (stmts.nonEmpty) {
      val headHashcode = Utils.hashCode(stmts.head)
      val head = solver.getNatVar(headHashcode)
      stmts.tail.foldLeft(List[AST]()) {
        (acc, stmt) => // head = s1, head = s2, ...
          val eq = solver.mkEq(head, solver.getNatVar(Utils.hashCode(stmt)))
          eq :: acc
      }
    } else List.empty
  }

  def treeToCons(tree: CaseTree): List[AST] = genEqCons(tree.getStatements.asScala.toSet + tree)

  def treeToCons(tree: CatchTree): List[AST] = genEqCons(tree.getBlock.getStatements.asScala.toSet + tree)

  /**
    *
    * @param tree a statement tree (AST node)
    * @return a set of String constraints that describe the control flow relations inside the target AST node
    */
  def treeToCons(tree: StatementTree): List[AST] = {
    if (tree == null)
      return List[AST]()

    def genLoopCons(loop: StatementTree, body: StatementTree): List[AST] = {
      if (loop.isInstanceOf[DoWhileLoopTree] || loop.isInstanceOf[EnhancedForLoopTree] || loop.isInstanceOf[WhileLoopTree]) { // block >= this
        val bodyVar = solver.getNatVar(Utils.hashCode(body))
        val loopVar = solver.getNatVar(Utils.hashCode(loop))
        val ge = solver.mkGe(bodyVar, loopVar)
        ge :: treeToCons(body)
      } else
        List[AST]()
    }

    val thisHashcode = Utils.hashCode(tree)
    val me = solver.getNatVar(thisHashcode)
    tree match {
      case stmt: BlockTree =>
        stmt.getStatements.asScala.foldLeft(genEqCons(stmt.getStatements.asScala.toSet + stmt)) {
          (acc, s) => acc ::: treeToCons(s)
        }
      case stmt: DoWhileLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: EnhancedForLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: WhileLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: ForLoopTree => // this = init1 = init2 = ...; block >= this
        val initCons = genEqCons(stmt.getInitializer.asScala.toSet + tree)
        val body = solver.getNatVar(Utils.hashCode(stmt.getStatement))
        val ge = solver.mkGe(body, me)
        ge :: initCons ::: treeToCons(stmt.getStatement)
      case stmt: LabeledStatementTree => // this = body; this = label
        val body = solver.getNatVar(Utils.hashCode(stmt.getStatement))
        val label = solver.getNatVar(stmt.getLabel.toString)
        val eq1 = solver.mkEq(me, body)
        val eq2 = solver.mkEq(me, label)
        eq1 :: eq2 :: treeToCons(stmt.getStatement)
      case stmt: IfTree => // this = then + else
        val thenVar = solver.getNatVar(Utils.hashCode(stmt.getThenStatement))
        val eq =
          if (stmt.getElseStatement != null) {
            val elseVar = solver.getNatVar(Utils.hashCode(stmt.getElseStatement))
            solver.mkEq(me, solver.mkAdd(thenVar, elseVar))
          } else solver.mkEq(me, thenVar)
        eq :: treeToCons(stmt.getThenStatement) ::: treeToCons(stmt.getElseStatement)
      case stmt: SwitchTree => // this = case1 + case2 + ...
        val cases = {
          val cases = stmt.getCases.asScala
          assert(cases.nonEmpty)
          if (cases.size == 1) solver.getNatVar(Utils.hashCode(cases.head))
          else solver.mkAdd(cases.map(casetree => solver.getNatVar(Utils.hashCode(casetree))).toArray: _*)
        }
        val eq = solver.mkEq(me, cases)
        stmt.getCases.asScala.foldLeft(List[AST](eq)) {
          (acc, casetree) => acc ::: treeToCons(casetree)
        }
      case stmt: ExpressionStatementTree => List[AST]()
      case stmt: ReturnTree => List[AST]()
      case stmt: VariableTree => List[AST]()
      case stmt: TryTree => // this = try; this = finally; this = catch1 + catch2 + ...
        val tryVar = solver.getNatVar(Utils.hashCode(stmt.getBlock))
        val eq1 = solver.mkEq(me, tryVar)
        val eq2 =
          if (stmt.getFinallyBlock != null) {
            val finallyVar = solver.getNatVar(Utils.hashCode(stmt.getFinallyBlock))
            solver.mkEq(me, finallyVar)
          } else solver.ctx.mkTrue()
        val eq3 = {
          val catches = stmt.getCatches.asScala
          if (catches.isEmpty) solver.ctx.mkTrue()
          else if (catches.size == 1) solver.mkEq(me, solver.getNatVar(Utils.hashCode(catches.head)))
          else solver.mkEq(me, solver.mkAdd(catches.map(catchtree => solver.getNatVar(Utils.hashCode(catchtree))).toArray: _*))
        }
        stmt.getCatches.asScala.foldLeft(List[AST](eq1, eq2, eq3)) {
          (acc, catchtree) => acc ::: treeToCons(catchtree)
        } ++ treeToCons(stmt.getBlock) ++ treeToCons(stmt.getFinallyBlock)
      case stmt: SynchronizedTree => treeToCons(stmt.getBlock)
      case _ => List[AST]()
    }
  }
}
