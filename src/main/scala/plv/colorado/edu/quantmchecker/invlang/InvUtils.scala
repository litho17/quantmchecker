package plv.colorado.edu.quantmchecker.invlang

import javax.lang.model.element.AnnotationMirror

import com.sun.source.tree.VariableTree
import com.sun.source.util.Trees
import org.checkerframework.javacutil.AnnotationUtils
import plv.colorado.edu.Utils
import plv.colorado.edu.quantmchecker.QuantmAnnotatedTypeFactory

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet

/**
  * @author Tianhan Lu
  */
object InvUtils {
  private val DEBUG_COLLECT_INV = false
  private val MALFORMAT_INVARIANT = "Malformat invariant"

  /**
    *
    * @param invariant an invariant
    * @return 1. A list of remainders
    *         2. A list of selfs
    *
    */
  def extractInv(invariant: InvLangAST): (List[String], List[String]) = {
    invariant match {
      case Invariant(remainders, selfs, _, _) =>
        (remainders.map(r => r.toString), selfs.map(s => s.toString))
      case _ => (List.empty, List.empty)
    }
  }

  /**
    *
    * @param node a variable tree
    * @param atypeFactory type factory
    * @param trees trees
    * @return all annotations on the variable declaration
    */
  def getAnnotationFromVariableTree(node: VariableTree,
                                    atypeFactory: QuantmAnnotatedTypeFactory,
                                    trees: Trees): HashSet[AnnotationMirror] = {
    node.getModifiers.getAnnotations.asScala.foldLeft(new HashSet[AnnotationMirror]) {
      (acc, t) =>
        acc ++ atypeFactory.getAnnotatedType(trees.getElement(atypeFactory.getPath(node))).getAnnotations.asScala
    }
  }

  /**
    *
    * @param node  a variable tree
    * @param annot which annotation to collect
    * @return collect the specified type of annotations in the variable tree
    */
  def getAnnotationFromVariableTree(node: VariableTree,
                                    annot: AnnotationMirror,
                                    atypeFactory: QuantmAnnotatedTypeFactory,
                                    trees: Trees): HashSet[InvLangAST] = {
    // val annotations = elements.getAllAnnotationMirrors(TreeUtils.elementFromDeclaration(node)).asScala
    val annotations = getAnnotationFromVariableTree(node, atypeFactory, trees)
    val listInvAnnotations = annotations.filter(mirror => AnnotationUtils.areSameIgnoringValues(mirror, annot))
    // val annotations: List[String] = AnnoTypeUtils.extractValues(TreeUtils.annotationFromAnnotationTree(node))
    if (listInvAnnotations.nonEmpty) {
      val invs: List[String] = Utils.extractArrayValues(listInvAnnotations.head, "value")
      invs.foldLeft(new HashSet[InvLangAST]) {
        (acc, str) =>
          // Before parsing, replace multiple spaces with a single space
          val invStr = str.replaceAll("\\s+", " ")
          val inv = InvLangCompiler(invStr)
          if (inv.isRight) {
            // val name = node.getName.toString // the variable that <self> represents
            inv.right.get match {
              case Invariant(remainders, selfs, posLines, negLines) =>
                val invariant = Invariant(remainders, selfs, posLines, negLines)
                // assert(invariant.toString != invStr)
                if (DEBUG_COLLECT_INV)
                  Utils.logging("Collected invariants:\n\t" + invariant + "\n\t" + node + "\n")
                acc + invariant
              case _ => println(node, MALFORMAT_INVARIANT); acc
            }
          } else {
            println(node, MALFORMAT_INVARIANT)
            acc // parser error
          }
      }
    } else {
      new HashSet[InvLangAST]
    }
  }
}