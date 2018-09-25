package plv.colorado.edu.quantmchecker.verification

import org.scalatest.{FlatSpec, Matchers}
import soot.Scene
import soot.jimple.spark.SparkTransformer
import soot.options.Options

import scala.collection.JavaConverters._


/**
  * @author Tianhan Lu
  */
class TestSoot extends FlatSpec with Matchers {
  val paths = List("/Users/lumber/Documents/workspace/quantmchecker/src/test/java/textcrunchr_1")

  val fileSep: String = System.getProperty("file.separator")
  val pathSep: String = System.getProperty("path.separator")
  val javaLibraryPath: String = System.getProperty("java.home") + fileSep + "lib" + fileSep
  val jcePath: String = javaLibraryPath + "jce.jar"
  val rtPath: String = javaLibraryPath + "rt.jar"

  soot.G.reset()
  Options.v().keep_line_number()
  Options.v().set_src_prec(Options.src_prec_class)
  Options.v().set_process_dir(paths.asJava)
  // Options.v().unfriendly_mode() //allow to run with no command line args
  Options.v().set_allow_phantom_refs(true)
  Options.v().set_whole_program(true)

  // Options.v().set_oaat(true)
  Options.v().set_drop_bodies_after_load(false)

  // Set main class
  val mainClass = "textcrunchr"
  Options.v().set_main_class(mainClass)

  // Set soot class path to directories: (1) where the jars to be analyzed are located (2) rt.jar (3) jce.jar
  // Scene.v().setSootClassPath(paths.foldLeft("")((acc, str) => acc + str + pathSep) + jcePath + pathSep + rtPath)

  // PackManager.v().getPack("wjtp").add(new Transform("wjtp.loop_detector", new LoopDetector(paths)))

  // runPaddle()
  runSpark()
  // soot.Main.main(Array("-unfriendly-mode"))
  soot.Main.main(Array("-unfriendly-mode"))
  val pa = Scene.v().getPointsToAnalysis


  def runSpark(): Unit = {
    val opt = new java.util.HashMap[String, String]()
    opt.put("verbose", "true")
    opt.put("propagator", "worklist")
    opt.put("simple-edges-bidirectional", "false")
    opt.put("on-fly-cg", "true")
    opt.put("set-impl", "double")
    opt.put("double-set-old", "hybrid")
    opt.put("double-set-new", "hybrid")
    SparkTransformer.v.transform("", opt)
  }
}
