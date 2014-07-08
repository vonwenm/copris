package jp.kobe_u.copris.pb

import jp.kobe_u.copris._
import jp.kobe_u.copris.sugar.{Translator => SugarTranslator}
import jp.kobe_u.{sugar => javaSugar}
import jp.kobe_u.sugar.expression.{Expression => SugarExpr}

import scala.collection._

/**
 * Class for analyzing PB solver log output
 */
abstract class PbSolverLogger(file: java.io.File) extends scala.sys.process.FileProcessLogger(file) {
  /** Status of PB solver */
  var stat: Map[String,Number] = Map.empty
  /** Adds the status */
  def addStat(key: String, value: Number) =
    stat = stat + (key -> value)
  /** Parses the log output and update status */
  def parseLog(s: String): Unit
  override def out(s: => String) {
    super.out(s)
    parseLog(s)
  }
  override def err(s: => String) {
    super.err(s)
    parseLog(s)
  }
}
/**
 * Class for PB solvers
 */
class PbSolver(command: String, opts: Seq[String] = Seq.empty) {
  import scala.sys.process._
  /** Runs the PB solver */
  def run(pbFileName: String, outFileName: String, solver: Solver): Int = {
    val outFile = new java.io.File(outFileName)
    outFile.delete
    val logger = new PbSolverLogger(outFile) {
      def parseLog(s: String) {}
    }
    runProcess(opts :+ pbFileName, logger, solver)
  }
  protected def runProcess(args: Seq[String], logger: FileProcessLogger, solver: Solver): Int = {
    var process = Process(command, args).run(logger)
    solver.setTimeoutTask {
      // println("kill " + command)
      if (process != null)
        process.destroy
    }
    var rc = process.exitValue
    process = null
    logger.close
    rc
  }
  override def toString = command
}
/**
 * Object for clasp solver ("clasp")
 */
object Clasp extends PbSolver("clasp", Seq.empty)

/**
 * Class for translating CSP to PB
 */
class Translator extends SugarTranslator

/**
 * Class for encoding CSP to PB
 */
class Encoder(csp: CSP, solver: Solver, pbFileName: String, mapFileName: String, encoding: String = "binary") {
  val pbEncoding = encoding match {
    case "direct" => {
      javaSugar.pb.PBEncoder.Encoding.DIRECT_ENCODING
    }
    case "order" => {
      javaSugar.pb.PBEncoder.Encoding.ORDER_ENCODING
    }
    case s if s.matches("compact=\\d+") => {
      javaSugar.pb.PBEncoder.BASE = s.replace("compact=", "").toInt
      javaSugar.pb.PBEncoder.Encoding.COMPACT_ORDER_ENCODING
    }
    case "log" | "binary" => {
      javaSugar.pb.PBEncoder.BASE = 2
      javaSugar.pb.PBEncoder.Encoding.COMPACT_ORDER_ENCODING
    }
  }
  var translator = new Translator()
  var sugarCSP = new javaSugar.csp.CSP()
  var converter = new javaSugar.converter.Converter(sugarCSP)
  var pbProblem = new javaSugar.pb.PBFileProblem(pbFileName)
  var encoder = new javaSugar.pb.PBEncoder(sugarCSP, pbProblem, pbEncoding)
  def init {
    translator = new Translator()
    sugarCSP = new javaSugar.csp.CSP()
    converter = new javaSugar.converter.Converter(sugarCSP)
    pbProblem = new javaSugar.pb.PBFileProblem(pbFileName)
    encoder = new javaSugar.pb.PBEncoder(sugarCSP, pbProblem, pbEncoding)
  }
  def commit {
    // TODO verify
    sugarCSP.commit
    if (! sugarCSP.isUnsatisfiable)
      encoder.commit
  }
  def cancel {
    // TODO verify
    sugarCSP.cancel
    encoder.outputMap(mapFileName)
  }
  def encode: Boolean = {
    // println("Translating")
    val expressions = translator.toSugar(csp)
    solver.checkTimeout
    // println("Converting")
    javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = true
    converter.convert(expressions)
    solver.checkTimeout
    expressions.clear
    SugarExpr.clear
    // println("Propagating")
    sugarCSP.propagate
    solver.checkTimeout
    if (sugarCSP.isUnsatisfiable)
      false
    else {
      // println("Simplifying")
      val simplifier = new javaSugar.converter.Simplifier(sugarCSP)
      simplifier.simplify
      solver.checkTimeout
      // println("Encoding")
      encoder.encode()
      solver.checkTimeout
      encoder.outputMap(mapFileName)
      // println("Done")
      // commit
      true
    }
  }
  def encodeDelta {
    sugarCSP.cancel
    val expressions = translator.toSugarDelta(csp)
    solver.checkTimeout
    javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = false
    converter.convert(expressions)
    javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = true
    solver.checkTimeout
    expressions.clear
    SugarExpr.clear
    encoder.cancel
    encoder.encodeDelta
    encoder.outputMap(mapFileName)
  }
  def decode(outFileName: String): Option[Solution] = {
    import scala.collection.JavaConversions
    if (encoder.decode(outFileName)) {
      val intNameValues = mutable.Map.empty[String,Int]
      for (v <- JavaConversions.asScalaBuffer(sugarCSP.getIntegerVariables))
        if (! v.isAux())
          intNameValues += v.getName -> v.getValue
      var intValues = Map.empty[Var,Int]
      for (x <- csp.variables) {
	val s = translator.toSugarName(x)
	if (intNameValues.contains(s))
          intValues += x -> intNameValues(s)
      }
      val boolNameValues = mutable.Map.empty[String,Boolean]
      for (v <- JavaConversions.asScalaBuffer(sugarCSP.getBooleanVariables))
        if (! v.isAux())
          boolNameValues += v.getName -> v.getValue
      var boolValues = Map.empty[Bool,Boolean]
      for (p <- csp.bools) {
	val s = translator.toSugarName(p)
	if (boolNameValues.contains(s))
          boolValues += p -> boolNameValues(s)
      }
      Some(Solution(intValues, boolValues))
    } else {
      None
    }
  }
}

/**
 * Class for PB solver
 */
class Solver(csp: CSP, var pbSolver: PbSolver = Clasp, encoding: String = "binary") extends AbstractSolver(csp) {
  val solverName = "pb"
  var pbFileName: String = null
  var mapFileName: String = null
  var outFileName: String = null
  var encoder: Encoder = null
  var initial = true
  var commitFlag = true
  var solution: Solution = null
  init

  private def createTempFile(ext: String): String = {
    import java.io.File
    val file = File.createTempFile("sugar", ext)
    file.deleteOnExit
    file.getAbsolutePath
  }
  override def init {
    def fileName(key: String, ext: String) = {
      val file = options.getOrElse(key, createTempFile(ext))
      options = options + (key -> file)
      file
    }
    super.init
    pbFileName = fileName("pb", ".opb")
    mapFileName = fileName("map", ".map")
    outFileName = fileName("out", ".out")
    javaSugar.SugarMain.init()
    encoder = new Encoder(csp, this, pbFileName, mapFileName, encoding)
    encoder.init
    solution = null
    initial = true
    addSolverInfo("solver", solverName)
    addSolverInfo("pbSolver", pbSolver.toString)
    addSolverInfo("pbFile", pbFileName)
    addSolverInfo("mapFile", mapFileName)
  }
  def encode: Boolean = {
    measureTime("time", "encode") {
      encoder.encode
    }
  }
  def encodeDelta {
    measureTime("time", "encodeDelta") {
      encoder.encodeDelta
    }
  }
  @deprecated("use encodeDelta method of [[jp.kobe_u.copris.pb.Solver]] instead", "2.2.0")
  def addDelta = encodeDelta
  def pbSolve: Boolean = {
    // addSolverStat("pb", "size", encoder.encoder.getSatFileSize)
    measureTime("time", "find") {
      pbSolver.run(pbFileName, outFileName, this)
    }
    measureTime("time", "decode") {
      val sat = encoder.decode(outFileName) match {
        case None => {
	  solution = null
          false
	}
        case Some(sol) => {
          solution = sol
          true
        }
      }
      // (new java.io.File(outFileName)).delete
      // (new java.io.File(logFileName)).delete
      sat
    }
  }
  def commit { encoder.commit }
  def cancel { encoder.cancel }
  def find(commitFlag: Boolean): Boolean = {
    this.commitFlag = commitFlag
    super.find
  }
  override def find: Boolean = find(true)
  def findBody: Boolean = {
    val result = 
      if (initial) {
	initial = false
	encode && pbSolve
      } else {
	encodeDelta
	pbSolve
      }
    if (commitFlag) {
      csp.commit
      commit
    }
    result
  }
  def findNext(commitFlag: Boolean): Boolean = {
    this.commitFlag = commitFlag
    super.findNext
  }
  override def findNext: Boolean = findNext(false)
  def findNextBody: Boolean = {
    measureTime("time", "encode") {
      val cs1 = for (x <- csp.variables if ! x.aux)
                yield Eq(x, Num(solution(x)))
      val cs2 = for (p <- csp.bools if ! p.aux)
                yield if (solution.boolValues(p)) p else Not(p)
      csp.add(Not(And(And(cs1), And(cs2))))
      encodeDelta
      if (commitFlag) {
	csp.commit
	commit
      }
    }
    pbSolve
  }
  def findOptBody: Boolean = {
    val v = csp.objective
    if (csp.variables.contains(v)) {
      var lb = csp.dom(v).lb
      var ub = csp.dom(v).ub
      encode
      csp.commit
      commit
      val sat = pbSolve
      addSolverStat("result", "find", if (sat) 1 else 0)
      if (sat) {
        var lastSolution = solution
        if (csp.isMinimize) {
          ub = solution(v)
          while (lb < ub) {
            val mid = (lb + ub) / 2
            if (findOptBound(lb, mid)) {
              ub = solution(v)
              lastSolution = solution
            } else {
              lb = mid + 1
            }
          }
        } else {
          lb = solution(v)
          while (lb < ub) {
            val mid = (lb + ub + 1) / 2
            if (findOptBound(mid, ub)) {
              lb = solution(v)
              lastSolution = solution
            } else {
              ub = mid - 1
            }
          }
        }
        solution = lastSolution
        true
      } else {
        false
      }
    } else {
      throw new RuntimeException("Objective variable is not defined")
    }
  }
  def findOptBoundBody(lb: Int, ub: Int) = {
    val v = csp.objective
    measureTime("time", "encode") {
      csp.cancel
      cancel
      csp.add(v >= lb && v <= ub)
      encodeDelta
    }
    pbSolve
  }
  def dump(fileName: String, format: String) {
    format match {
      case "" | "pb" => {
        val encoder = new Encoder(csp, this, fileName, mapFileName, encoding)
        encoder.encode
      }
    }
  }
}

/**
 * Class for PB DSL
 */
class PB(val csp: CSP, var solver: Solver) extends CoprisTrait {
  def this(csp: CSP) =
    this(csp, new Solver(csp))
  def this(csp: CSP, pbSolver: PbSolver) =
    this(csp, new Solver(csp, pbSolver = pbSolver))
  def this(pbSolver: PbSolver) =
    this(CSP(), pbSolver = pbSolver)
  def this() =
    this(CSP())
  def use(newSolver: AbstractSolver): Unit = newSolver match {
    case sugarSolver: Solver =>
      solver = sugarSolver
  }
  def use(newPbSolver: PbSolver): Unit = {
    solver.pbSolver = newPbSolver
    solver.addSolverInfo("pbSolver", newPbSolver.toString)
  }
}

/**
 * Object for PB DSL
 */
object dsl extends CoprisTrait {
  val pbVar = new util.DynamicVariable[PB](new PB())
  def csp = pbVar.value.csp
  def solver = pbVar.value.solver
  def using(pb: PB = new PB())(block: => Unit) =
    pbVar.withValue(pb) { block }
  def use(newSolver: AbstractSolver) =
    pbVar.value.use(newSolver)
  def use(pbSolver: PbSolver) =
    pbVar.value.use(pbSolver)
}
