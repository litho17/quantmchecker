package plv.colorado.edu.quantmchecker.verification

import java.io.{File, IOException, PrintWriter}
import java.util.StringTokenizer

import com.ibm.wala.analysis.typeInference.TypeInference
import com.ibm.wala.classLoader._
import com.ibm.wala.ipa.callgraph._
import com.ibm.wala.ipa.callgraph.impl.{DefaultEntrypoint, Everywhere}
import com.ibm.wala.ipa.callgraph.propagation.{LocalPointerKey, SSAPropagationCallGraphBuilder}
import com.ibm.wala.ipa.cha.{ClassHierarchyFactory, IClassHierarchy}
import com.ibm.wala.shrikeCT.InvalidClassFileException
import com.ibm.wala.ssa.{DefaultIRFactory, IR}
import com.ibm.wala.types.{ClassLoaderReference, Descriptor, MethodReference}
import com.ibm.wala.util.config.AnalysisScopeReader
import com.ibm.wala.util.debug.Assertions
import com.ibm.wala.util.io.FileProvider
import com.ibm.wala.util.strings.Atom
import org.scalatest.{FlatSpec, Matchers}

import scala.collection.JavaConverters._
import scala.collection.immutable.HashSet


/**
  * @author Tianhan Lu
  */
class TestWala extends FlatSpec with Matchers {
  val DEFAULT_EXCLUSION_FILE = "exclusions.txt"
  val path = "/Users/lumber/Documents/workspace/quantmchecker/src/test/jars/textcrunchr_1.jar"
  val scope: AnalysisScope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(path, (new FileProvider).getFile(DEFAULT_EXCLUSION_FILE))
  // val scope = AnalysisScopeReader.makePrimordialScope(null)
  // val loader = scope.getLoader(AnalysisScope.APPLICATION)
  // readSourceFile(path, scope, loader)
  val cha: IClassHierarchy = ClassHierarchyFactory.make(scope, new ClassLoaderFactoryImpl(scope.getExclusions))
  val eps: java.util.HashSet[Entrypoint] = createEntrypoints(scope, cha)
  val options = new AnalysisOptions(scope, eps)
  val cache = new AnalysisCacheImpl(new DefaultIRFactory())
  val builder = com.ibm.wala.ipa.callgraph.impl.Util.makeZeroOneCFABuilder(Language.JAVA, options, cache, cha, scope)
  val cg = genCallGraph(builder, options)
  val cfgs = genControlFlowGraph(cha, cache, options)
  val pa = builder.getPointerAnalysis

  val fullFileName = "/Users/lumber/Desktop/abc.txt"
  val file = new File(fullFileName)
  file.getParentFile.mkdirs()
  file.createNewFile()
  val writer = new PrintWriter(fullFileName, "UTF-8")

  cfgs.foreach {
    fact =>
      val klass = fact.klass
      val method = fact.method
      val ir = fact.ir
      val ti = fact.ti
      if (method.getDeclaringClass.getClassLoader.getReference.equals(ClassLoaderReference.Application)) {
        val methodName = klass.getName + "." + method.getName
        writer.println("\n\n\n" + methodName)
        val numOfVar = ir.getSymbolTable.getMaxValueNumber
        cg.getNodes(method.getReference).asScala.foreach {
          node =>
            for( a <- 1 to numOfVar) {
              val pointer = pa.getHeapModel.getPointerKeyForLocal(node, a)
              val name = ir.getLocalNames(ir.getInstructions.length-1, a)
              val typ = ti.getType(a)
              val varName = {
                if (name != null) name.head else "v" + a
              } + ": " + {
                if (typ.getType != null) typ.getType.getName.toString else ""
              }
              val mayAlias = pa.getHeapGraph.getSuccNodes(pointer).asScala.foldLeft(new HashSet[LocalPointerKey]) {
                (acc, ik) => pa.getHeapGraph.getPredNodes(ik).asScala.foldLeft(acc) {
                  (acc2, pt) => pt match {
                    case pt: LocalPointerKey =>
                      if (pt.getNode.getMethod.getDeclaringClass.getClassLoader.getReference.equals(ClassLoaderReference.Application))
                        acc2 + pt
                      else acc2
                    case _ => acc2
                  }
                }
              }
              if (mayAlias.size > 10)
                writer.println(varName + "\n" + mayAlias.size + "\n")
              else
                writer.println(varName + "\n" + mayAlias + "\n")
            }
        }
      }
  }

  writer.close()


  def createEntrypoints(scope: AnalysisScope, cha: IClassHierarchy): java.util.HashSet[Entrypoint] = {
    val result = new java.util.HashSet[Entrypoint]()
    val mainMethod: Atom = Atom.findOrCreateAsciiAtom("main")

    cha.asScala.foreach {
      klass =>
        if (klass.getClassLoader.getReference == scope.getApplicationLoader) {
          val mainRef: MethodReference = MethodReference.findOrCreate(klass.getReference, mainMethod, Descriptor.findOrCreateUTF8("([Ljava/lang/String;)V"))
          val m: IMethod = klass.getMethod(mainRef.getSelector)
          if (m != null) result.add(new DefaultEntrypoint(m, cha))
        }
    }
    result
  }

  case class MethodFacts(klass: IClass, method: IMethod, ir: IR, ti: TypeInference)

  def genControlFlowGraph(cha: IClassHierarchy, cache: AnalysisCache, options: AnalysisOptions): HashSet[MethodFacts] = {
    cha.asScala.foldLeft(new HashSet[MethodFacts]) {
      (acc, klass) =>
        klass.getAllMethods.asScala.foldLeft(acc) {
          (acc2, method) =>
            if (method.getDeclaringClass.getClassLoader.getReference.equals(ClassLoaderReference.Application)) {
              val ir = cache.getSSACache.findOrCreateIR(method, Everywhere.EVERYWHERE, options.getSSAOptions)
              if (ir != null) {
                val g = ir.getControlFlowGraph
                val ti = TypeInference.make(ir, false)
                acc2 + MethodFacts(klass, method, ir, ti)
              } else acc2
            } else acc2
        }
    }
  }

  def genCallGraph(builder: SSAPropagationCallGraphBuilder, options: AnalysisOptions): CallGraph = {
    try {
      val cg = builder.makeCallGraph(options, null)
      cg
    } catch {
      case e: Exception =>
        // e.printStackTrace()
        // System.exit(-1)
        null
    }
  }

  def readSourceFile(path: String, scope: AnalysisScope, loader: ClassLoaderReference): Unit = {
    try {
      val paths = new StringTokenizer(path, File.pathSeparator)
      while ( {
        paths.hasMoreTokens
      }) {
        val path = paths.nextToken
        val f = new File(path)
        if (f.isDirectory) {
          scope.addToScope(loader, new SourceDirectoryTreeModule(f))
          f.listFiles().foreach(subFile => readSourceFile(subFile.getAbsolutePath, scope, loader))
        }
        else scope.addSourceFileToScope(loader, f, f.getName)
        // else scope.addToScope(loader, f)
      }
    } catch {
      case e: IOException =>
        Assertions.UNREACHABLE(e.toString)
      case e: InvalidClassFileException =>
        Assertions.UNREACHABLE(e.toString)
    }
  }

  def dumpToFile(contents: String, fileName: String, outputDir: String): Unit = {
    val fullFileName = outputDir + fileName
    val file = new File(fullFileName)
    file.getParentFile.mkdirs()
    file.createNewFile()
    val writer = new PrintWriter(fullFileName, "UTF-8")
    writer.println(contents)
    writer.close()
  }
}

// https://github.com/wala/WALA/tree/0752bf321c9a62548ebe38f1dc09b882916c7130/com.ibm.wala.core/src/com/ibm/wala/ipa/callgraph/propagation
// https://github.com/wala/WALA/wiki/Getting-Started
// https://github.com/wala/WALA/blob/0752bf321c9a62548ebe38f1dc09b882916c7130/com.ibm.wala.cast.java/src/com/ibm/wala/cast/java/ipa/callgraph/JavaSourceAnalysisScope.java
// https://github.com/wala/WALA/tree/master/com.ibm.wala.cast.java/src/com/ibm/wala/cast/java
// https://www.cs.cornell.edu/Projects/polyglot/