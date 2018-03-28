package plv.colorado.edu.quantmchecker

import javax.lang.model.element.AnnotationMirror

import com.sun.source.tree._
import org.checkerframework.common.basetype.{BaseTypeChecker, BaseTypeVisitor}
import org.checkerframework.javacutil.{AnnotationBuilder, AnnotationUtils, TreeUtils}
import plv.colorado.edu.AnnoTypeUtils
import plv.colorado.edu.quantmchecker.invlang.{Inv, InvLangAST, InvLangCompiler, InvNoRem}
import plv.colorado.edu.quantmchecker.qual.ListInv

import scala.collection.JavaConverters._
import scala.collection.immutable.{HashMap, HashSet}

/**
  * @author Tianhan Lu
  */
class QuantmVisitor(checker: BaseTypeChecker) extends BaseTypeVisitor[QuantmAnnotatedTypeFactory](checker) {
  private val DEBUG = false
  protected val LISTINV = AnnotationBuilder.fromClass(elements, classOf[ListInv])

  @deprecated
  override def visitMethodInvocation(node: MethodInvocationTree, p: Void): Void = {
    // val invokedMethod = atypeFactory.methodFromUse(node).first
    // val typeargs = atypeFactory.methodFromUse(node).second
    // TreeUtils.elementFromTree(node)

    // val enclosingMethod: MethodTree = TreeUtils.enclosingMethod(atypeFactory.getPath(node))
    // println(elements.getAllAnnotationMirrors(TreeUtils.elementFromDeclaration(enclosingMethod)))

    super.visitMethodInvocation(node, p)
  }

  /**
    *
    * @param classTree a class definition
    *                  Note: I have to process the source code files by myself, instead of
    *                  relying on Checker framework's visitor pattern, because I have
    *                  to know what the invariants are before type checking every statement
    */
  override def processClassTree(classTree: ClassTree): Unit = {
    val classFieldInvariants = gatherClassFieldInvariants(classTree)
    if (DEBUG) println(classFieldInvariants)

    classTree.getMembers.asScala.foreach {
      case member: MethodTree =>
        // if (DEBUG) println("Visting method: ", root.getSourceFile.getName, classTree.getSimpleName, member.getName)
        val localInvariants = gatherLocalInvariants(member)
        if (DEBUG) println(localInvariants)
      case member: VariableTree => // Handled by gatherClassFieldInvariants()
      case member: ClassTree => // Ignore inner classes for the moment
      case x@_ => println("Unhandled Tree kind in processClassTree(): ", x, x.getKind)
    }
    super.processClassTree(classTree)
  }

  /**
    *
    * @param classTree a class definition
    * @return a map from a line number to an invariant that might be changed by that line
    */
  private def gatherClassFieldInvariants(classTree: ClassTree): HashMap[Int, InvLangAST] = {
    classTree.getMembers.asScala.foldLeft(new HashMap[Int, InvLangAST]) {
      (acc, member) =>
        member match {
          case member: VariableTree => // Only care about variable declarations in a class
            /**
              * Get annotations on class fields
              */
            getAnnotationFromVariableTree(member) match {
              case Some(inv) => mapInvToLine(inv, acc)
              case None => acc
            }
          case _ => acc
        }
    }
  }

  /**
    *
    * @param node a method
    * @return all invariants that are declared in the method
    */
  private def gatherLocalInvariants(node: MethodTree): HashMap[Int, InvLangAST] = {
    if (node.getBody != null) {
      val stmts = node.getBody.getStatements.asScala.foldLeft(new HashSet[StatementTree]) {
        (acc, stmt) => acc ++ flattenStatement(stmt)
      }
      stmts.foldLeft(new HashMap[Int, InvLangAST]) {
        (acc, stmt) =>
          stmt match {
            // case stmt: ExpressionStatementTree => println(stmt); acc
            case stmt: VariableTree =>
              getAnnotationFromVariableTree(stmt) match {
                case Some(inv) => mapInvToLine(inv, acc)
                case None => acc
              }
            case _ => acc
          }
      }
    } else {
      new HashMap[Int, InvLangAST]
    }
  }

  private def visitMethod(node: MethodTree): Unit = {
    if (node.getBody != null) {
      /**
        * 1. Collect all invariants (from method bodies as well as from class fields)
        * 2. For every statement, check if any related invariant is preserved
        * 3. For every loop, check if any related invariant is preserved throughout the loop body
        * 4. For every branch, check if any related invariant is preserved throughout the branch body
        *
        * TODO
        * 1. Override the methods that currently report type failures --- which is isSubType()
        * 2. Write annotations with ScalaZ3 and read them
        * 3. Connect upper bounds with callbacks' arguments via: method's return value is same size as method's argument
        * 4. INPUTINPUT is a special variable that represents input. On the line that decrements INPUTINPUT, do not report error even if not type check, because the decrement is meant to be non-deterministic.
        * 5. Annotate class fields
        */
      val methodAnnotations = elements.getAllAnnotationMirrors(TreeUtils.elementFromDeclaration(node)).asScala
      val success = node.getBody.getStatements.asScala.forall {
        stmt => isInvariantPreserved(stmt)
      }
    }
  }

  private def isInvariantPreserved(node: StatementTree): Boolean = {
    node match {
      case stmt: BlockTree => stmt.getStatements.asScala.forall(s => isInvariantPreserved(s))
      case stmt: DoWhileLoopTree => isInvariantPreserved(stmt.getStatement)
      case stmt: EnhancedForLoopTree => isInvariantPreserved(stmt.getStatement)
      case stmt: ForLoopTree => isInvariantPreserved(stmt.getStatement)
      case stmt: ExpressionStatementTree => isInvariantPreserved(stmt)
      case stmt: LabeledStatementTree => isInvariantPreserved(stmt.getStatement)
      case stmt: IfTree => isInvariantPreserved(stmt.getThenStatement) && isInvariantPreserved(stmt.getElseStatement)
      case stmt: ReturnTree => ???
      case stmt: SwitchTree => ???
      // stmt.getCases.asScala.forall(caseTree => caseTree.getStatements.asScala)
      case stmt: WhileLoopTree => isInvariantPreserved(stmt.getStatement)
      case _ => ???
    }
  }

  private def isInvariantPreserved(node: ExpressionStatementTree): Boolean = {
    // println(AnnoTypeUtils.getLineNumber(node, positions, root))
    node.getExpression match {
      case stmt: AssignmentTree =>
        // println(stmt.getVariable, stmt.getVariable.getClass)
        ???
      case stmt: CompoundAssignmentTree => ???
      case _ => ???
    }
  }

  /**
    *
    * @param node a statement tree
    * @return collect a set of all leave statements
    *         Note: Some StatementTrees are ignored (e.g. try-catch, synchronized)
    */
  private def flattenStatement(node: StatementTree): HashSet[StatementTree] = {
    node match {
      case stmt: BlockTree => stmt.getStatements.asScala.foldLeft(new HashSet[StatementTree])((acc, s) => flattenStatement(s))
      case stmt: DoWhileLoopTree => flattenStatement(stmt.getStatement)
      case stmt: EnhancedForLoopTree => flattenStatement(stmt.getStatement)
      case stmt: ForLoopTree => flattenStatement(stmt.getStatement)
      case stmt: WhileLoopTree => flattenStatement(stmt.getStatement)
      case stmt: LabeledStatementTree => flattenStatement(stmt.getStatement)
      case stmt: IfTree => flattenStatement(stmt.getThenStatement) ++ flattenStatement(stmt.getElseStatement)
      case stmt: SwitchTree =>
        stmt.getCases.asScala.foldLeft(new HashSet[StatementTree]) {
          (acc, caseTree) => caseTree.getStatements.asScala.foldLeft(acc)((acc2, s) => acc2 ++ flattenStatement(s))
        }
      case stmt: ExpressionStatementTree => HashSet[StatementTree](stmt)
      case stmt: ReturnTree => HashSet[StatementTree](stmt)
      case stmt: VariableTree => HashSet[StatementTree](stmt)
      case _ => new HashSet[StatementTree]
    }
  }

  /**
    *
    * @param invLangAST an invariant
    * @param acc        a map from a line number to an invariant that might be changed by that line
    * @return a map that is updated by invLangAST
    */
  private def mapInvToLine(invLangAST: InvLangAST, acc: HashMap[Int, InvLangAST]): HashMap[Int, InvLangAST] = {
    invLangAST match {
      case me@Inv(remainder, self, posLine, negLine) =>
        val tmpAcc = negLine.foldLeft(acc)((acc2, line) => acc2 + (line -> me))
        posLine.foldLeft(tmpAcc)((acc2, line) => acc2 + (line -> me))
      case me@InvNoRem(self, posLine, negLine) =>
        val tmpAcc = negLine.foldLeft(acc)((acc2, line) => acc2 + (line -> me))
        posLine.foldLeft(tmpAcc)((acc2, line) => acc2 + (line -> me))
      case _ => acc
    }
  }

  /**
    *
    * @param node a variable tree
    * @return the annotation in the variable tree
    */
  private def getAnnotationFromVariableTree(node: VariableTree): Option[InvLangAST] = {
    val annotations = elements.getAllAnnotationMirrors(TreeUtils.elementFromDeclaration(node)).asScala
    val listInvAnnotations = annotations.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, LISTINV))
    // val annotations: List[String] = AnnoTypeUtils.extractValues(TreeUtils.annotationFromAnnotationTree(node))
    // TODO: extract annotations of ListInv type
    if (listInvAnnotations.nonEmpty) {
      if (DEBUG) println(listInvAnnotations)
      val invs = AnnoTypeUtils.extractValues(listInvAnnotations.head)
      assert(invs.size == 1, "ListInv should only have 1 element")
      val inv = InvLangCompiler(invs.head)
      if (inv.isRight) {
        Some(inv.right.get)
      } else {
        PrintStuff.printRedString("Wrong annotation format: " + invs.head)
        None // parser error
      }
    } else {
      None
    }
  }

  @deprecated
  private def getTypeQualifiers: HashSet[AnnotationMirror] = new HashSet[AnnotationMirror] ++ atypeFactory.getQualifierHierarchy.getTypeQualifiers.asScala

  @deprecated
  private def getAnnotationMirror(node: Tree): HashSet[AnnotationMirror] = new HashSet ++ atypeFactory.getAnnotatedType(node).getAnnotations.asScala
}
