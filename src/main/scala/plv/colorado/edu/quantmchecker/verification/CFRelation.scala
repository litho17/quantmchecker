package plv.colorado.edu.quantmchecker.verification

import com.microsoft.z3.AST
import com.sun.source.tree._
import plv.colorado.edu.Utils

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
class CFRelation(tree: StatementTree, solver: Z3Solver) {
  val DEFAULT_LOOP_BOUND = 1000

  val constraints: Set[AST] = treeToCons(tree)

  private def genEqCons(stmts: List[_ <: Tree]): Set[AST] = {
    if (stmts.nonEmpty) {
      val headHashcode = Utils.hashCode(stmts.head)
      val head = solver.getNatVar(headHashcode)
      stmts.tail.foldLeft(new HashSet[AST]) {
        (acc, stmt) => // head = s1, head = s2, ...
          val eq = solver.mkEq(head, solver.getNatVar(Utils.hashCode(stmt)))
          acc + eq
      }
    } else new HashSet[AST]
  }

  private def treeToCons(tree: CaseTree): Set[AST] = {
    val eq = genEqCons(tree.getStatements.asScala.toList :+ tree)
    tree.getStatements.asScala.foldLeft(eq) { (acc, s) => acc ++ treeToCons(s) }
  }

  private def treeToCons(tree: CatchTree): Set[AST] = {
    val eq = genEqCons(tree.getBlock.getStatements.asScala.toList :+ tree.getParameter)
    treeToCons(tree.getBlock) ++ eq
  }

  /**
    *
    * @param tree a statement tree (AST node)
    * @return a set of String constraints that describe the control flow relations inside the target AST node
    */
  private def treeToCons(tree: StatementTree): Set[AST] = {
    if (tree == null) return new HashSet[AST]

    def genLoopCons(loop: StatementTree, body: StatementTree): Set[AST] = {
      if (loop.isInstanceOf[DoWhileLoopTree] || loop.isInstanceOf[EnhancedForLoopTree] || loop.isInstanceOf[WhileLoopTree]) {
        // val bodyVar = solver.getNatVar(Utils.hashCode(body))
        // val loopVar = solver.getNatVar(Utils.hashCode(loop))
        // val ge = solver.mkGe(bodyVar, loopVar)
        // ge :: treeToCons(body)
        treeToCons(body)
      } else new HashSet[AST]
    }

    val thisHashcode = Utils.hashCode(tree)
    val me = solver.getNatVar(thisHashcode)
    tree match {
      case stmt: BlockTree =>
        stmt.getStatements.asScala.foldLeft(genEqCons(stmt.getStatements.asScala.toList :+ stmt)) {
          (acc, s) => acc ++ treeToCons(s)
        }
      case stmt: DoWhileLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: EnhancedForLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: WhileLoopTree => genLoopCons(stmt, stmt.getStatement)
      case stmt: ForLoopTree => // this = init1 = init2 = ...
        val initCons = genEqCons(stmt.getInitializer.asScala.toList :+ tree)
        val body = solver.getNatVar(Utils.hashCode(stmt.getStatement))
        val update = solver.getNatVar(Utils.hashCode(stmt.getUpdate))
        val eq = solver.mkEq(body, update) // body = update
        // val ge = solver.mkGe(body, me)
        initCons ++ treeToCons(stmt.getStatement) + eq
      case stmt: LabeledStatementTree => // this = body; this = label
        val body = solver.getNatVar(Utils.hashCode(stmt.getStatement))
        val label = solver.getNatVar(stmt.getLabel.toString)
        val eq1 = solver.mkEq(me, body)
        val eq2 = solver.mkEq(me, label)
        treeToCons(stmt.getStatement) + eq1 + eq2
      case stmt: IfTree => // this = then + else
        val thenVar = solver.getNatVar(Utils.hashCode(stmt.getThenStatement))
        val eq =
          if (stmt.getElseStatement != null) {
            val elseVar = solver.getNatVar(Utils.hashCode(stmt.getElseStatement))
            solver.mkEq(me, solver.mkAdd(thenVar, elseVar))
          } else solver.mkEq(me, thenVar)
        treeToCons(stmt.getThenStatement) ++ treeToCons(stmt.getElseStatement) + eq
      case stmt: SwitchTree => // this = case1 + case2 + ...
        val cases = {
          val cases = stmt.getCases.asScala
          assert(cases.nonEmpty)
          if (cases.size == 1) solver.getNatVar(Utils.hashCode(cases.head))
          else solver.mkAdd(cases.map(casetree => solver.getNatVar(Utils.hashCode(casetree))).toArray: _*)
        }
        val eq = solver.mkEq(me, cases)
        stmt.getCases.asScala.foldLeft(HashSet[AST](eq)) { (acc, casetree) => acc ++ treeToCons(casetree) }
      case stmt: ExpressionStatementTree => new HashSet[AST]
      case stmt: ReturnTree => new HashSet[AST]
      case stmt: VariableTree => new HashSet[AST]
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
        stmt.getCatches.asScala.foldLeft(HashSet[AST](eq1, eq2, eq3)) {
          (acc, catchtree) => acc ++ treeToCons(catchtree)
        } ++ treeToCons(stmt.getBlock) ++ treeToCons(stmt.getFinallyBlock)
      case stmt: SynchronizedTree => treeToCons(stmt.getBlock)
      case _ => new HashSet[AST]
    }
  }
}
