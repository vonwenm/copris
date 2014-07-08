import jp.kobe_u.copris._
import jp.kobe_u.copris.loader.XCSPLoader
import jp.kobe_u.copris.dsl._

case object XCSPSolver {
  def checker(xcspFileName: String, solFileName: String) {
    import scala.sys.process._
    import java.io._
    import java.util.zip.GZIPInputStream
    var fileName = xcspFileName
    if (xcspFileName.endsWith(".gz")) {
      val in = new GZIPInputStream(new FileInputStream(xcspFileName))
      val outFile = File.createTempFile("copris", ".xsp")
      outFile.deleteOnExit
      val outFileName = outFile.getAbsolutePath
      val out = new FileOutputStream(outFile)
      var buffer = new Array[Byte](1024)
      var len = 0
      do {
        len = in.read(buffer)
        if (len > 0) out.write(buffer, 0, len)
      } while (len > 0)
      in.close
      out.close
      fileName = outFileName
    }
    // http://www.cril.univ-artois.fr/~lecoutre/research/tools/Tools2008.jar
    val cmd = Seq(
      "java", "-Xss300m", "-Xmx1g",
      "-cp", "Tools2008.jar", "abscon.instance.tools.SolutionChecker",
      fileName, solFileName
    )
    Process(cmd).run
  }
  def writeSolFile(sol: String): String = {
    import java.io._
    val solFile = File.createTempFile("copris", ".sol")
    solFile.deleteOnExit
    val solFileName = solFile.getAbsolutePath
    val writer = new PrintWriter(new File(solFileName))
    writer.write(sol)
    writer.write("\n")
    writer.close()
    solFileName
  }
  def parseOptions(args: List[String]): List[String] = args match {
    case "-s1" :: solver :: rest => {
      val satSolver = new sugar.SatSolver1(solver)
      use(new sugar.Solver(csp, satSolver))
      parseOptions(rest)
    }
    case "-s2" :: solver :: rest => {
      val satSolver = new sugar.SatSolver2(solver)
      use(new sugar.Solver(csp, satSolver))
      parseOptions(rest)
    }
    case "-smt" :: solver :: rest => {
      val smtSolver = new smt.SmtSolver(solver)
      use(new smt.Solver(csp, smtSolver))
      parseOptions(rest)
    }
    case "-jsr331" :: rest => {
      use(new jsr331.Solver(csp))
      parseOptions(rest)
    }
    case _ =>
      args
  }
  def main(args: Array[String]) {
    var xcspFileName = ""
    parseOptions(args.toList) match {
      case f :: Nil =>
        xcspFileName = f
      case _ => {
        println(s"Usage: copris $productPrefix xcspFileName")
        sys.exit(1)
      }
    }
    val loader = new XCSPLoader(csp)
    loader.load(xcspFileName)
    if (find) {
      println("s SATISFIABLE")
      val sol = csp.variables.map(solution(_)).mkString(" ")
      println("v " + sol)
      val solFileName = writeSolFile(sol)
      checker(xcspFileName, solFileName)
    } else {
      println("s UNSATISFIABLE")
    }
  }
}
