package jp.kobe_u.copris.smt

import jp.kobe_u.copris._
import jp.kobe_u.copris.sugar.{Translator => SugarTranslator}
import jp.kobe_u.{sugar => javaSugar}
import jp.kobe_u.sugar.expression.{Expression => SugarExpr}

import scala.collection._

/**
 * Class for analyzing SMT solver log output
 */
abstract class SmtSolverLogger(file: java.io.File) extends scala.sys.process.FileProcessLogger(file) {
  /** Status of SMT solver */
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
 * Class for SMT solvers
 */
class SmtSolver(command: String, opts: Seq[String] = Seq.empty) {
  import scala.sys.process._
  /** Runs the SMT solver */
  def run(smtFileName: String, outFileName: String, solver: Solver): Int = {
    val outFile = new java.io.File(outFileName)
    outFile.delete
    val logger = new SmtSolverLogger(outFile) {
      def parseLog(s: String) {}
    }
    runProcess(opts :+ smtFileName, logger, solver)
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
 * Object for Z3 solver ("z3")
 */
object Z3 extends SmtSolver("z3", Seq.empty)

/**
 * Class for translating CSP to SMT
 */
class Translator extends SugarTranslator

/**
 * Class for encoding CSP to SMT
 */
class Encoder(csp: CSP, solver: Solver, smtFileName: String) {
  var translator = new Translator()
  var sugarCSP = new javaSugar.csp.CSP()
  var converter = new javaSugar.converter.Converter(sugarCSP)
  def init {
    translator = new Translator()
    sugarCSP = new javaSugar.csp.CSP()
    converter = new javaSugar.converter.Converter(sugarCSP)
  }
  def commit {
    // csp.commit
    sugarCSP.commit
  }
  def cancel {
    // csp.cancel
    sugarCSP.cancel
  }
  def encode: Boolean = {
    // println("Translating")
    val expressions = translator.toSugar(csp)
    solver.checkTimeout
    // println("Converting")
    javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = true
    // no_norm,no_reduce,no_decomp_alldiff,replace_args,no_hints
    javaSugar.converter.Converter.NORMALIZE_LINEARSUM = false
    javaSugar.converter.Converter.REDUCE_ARITY = false
    javaSugar.converter.Converter.DECOMPOSE_ALLDIFFERENT = false
    javaSugar.converter.Converter.REPLACE_ARGUMENTS = true
    javaSugar.converter.Converter.HINT_ALLDIFF_PIGEON = false
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
      // sugarCSP.simplify
      // solver.checkTimeout
      val outSmt = new javaSugar.OutputSMT()
      val out = new java.io.PrintWriter(new java.io.BufferedWriter(new java.io.FileWriter(smtFileName)))
      outSmt.setCSP(sugarCSP)
      outSmt.setOut(out)
      outSmt.setFormat("smt")
      outSmt.output()
      out.close()
      solver.checkTimeout
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
    // no_norm,no_reduce,no_decomp_alldiff,replace_args,no_hints
    javaSugar.converter.Converter.NORMALIZE_LINEARSUM = false
    javaSugar.converter.Converter.REDUCE_ARITY = false
    javaSugar.converter.Converter.DECOMPOSE_ALLDIFFERENT = false
    javaSugar.converter.Converter.REPLACE_ARGUMENTS = true
    javaSugar.converter.Converter.HINT_ALLDIFF_PIGEON = false
    converter.convert(expressions)
    javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = true
    solver.checkTimeout
    expressions.clear
    SugarExpr.clear
    // always translate whole CSP
    val outSmt = new javaSugar.OutputSMT()
    val out = new java.io.PrintWriter(new java.io.BufferedWriter(new java.io.FileWriter(smtFileName)))
    outSmt.setCSP(sugarCSP)
    outSmt.setOut(out)
    outSmt.setFormat("smt")
    outSmt.output()
    out.close()
    solver.checkTimeout
  }
  def decode(outFileName: String): Option[Solution] = {
    import scala.io.Source
    val lines = Source.fromFile(outFileName).getLines.map(_.trim)
    val sat = lines.next
    if (sat == "sat") {
      val intNameValues = mutable.Map.empty[String,Int]
      val boolNameValues = mutable.Map.empty[String,Boolean]
      val r1 = """\s*\(?\s*\(\s*(\S+)\s+([^) ]+)\s*\)\s*\)?""".r
      val r2 = """\s*\(?\s*\(\s*(\S+)\s+\(\s*-\s*(\d+)\s*\)\s*\)\s*\)?""".r
      for (line <- lines) line match {
	case r1(x, a) if a == "true" || a == "false" =>
	  boolNameValues += x -> (a == "true")
	case r1(x, a) if a.matches("-?\\d+") =>
          intNameValues += x -> a.toInt
	case r2(x, a) =>
          intNameValues += x -> - a.toInt
      }
      var intValues = Map.empty[Var,Int]
      for (x <- csp.variables) {
	val s = translator.toSugarName(x)
	if (intNameValues.contains(s))
          intValues += x -> intNameValues(s)
      }
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
 * Class for SMT solver
 */
class Solver(csp: CSP, var smtSolver: SmtSolver = Z3) extends AbstractSolver(csp) {
  val solverName = "smt"
  var smtFileName: String = null
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
    smtFileName = fileName("smt", ".smt2")
    outFileName = fileName("out", ".out")
    javaSugar.SugarMain.init()
    encoder = new Encoder(csp, this, smtFileName)
    encoder.init
    solution = null
    initial = true
    addSolverInfo("solver", solverName)
    addSolverInfo("smtSolver", smtSolver.toString)
    addSolverInfo("smtFile", smtFileName)
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
  @deprecated("use encodeDelta method of [[jp.kobe_u.copris.smt.Solver]] instead", "2.2.0")
  def addDelta = encodeDelta
  def smtSolve: Boolean = {
    // addSolverStat("smt", "size", encoder.encoder.getSatFileSize)
    measureTime("time", "find") {
      smtSolver.run(smtFileName, outFileName, this)
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
	encode && smtSolve
      } else {
	encodeDelta
	smtSolve
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
    smtSolve
  }
  def findOptBody: Boolean = {
    val v = csp.objective
    if (csp.variables.contains(v)) {
      var lb = csp.dom(v).lb
      var ub = csp.dom(v).ub
      encode
      csp.commit
      commit
      val sat = smtSolve
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
    smtSolve
  }
  def dump(fileName: String, format: String) {
    format match {
      case "" | "smt" => {
        val encoder = new Encoder(csp, this, fileName)
        encoder.encode
      }
    }
  }
}

/**
 * Class for SMT DSL
 */
class SMT(val csp: CSP, var solver: Solver) extends CoprisTrait {
  def this(csp: CSP) =
    this(csp, new Solver(csp))
  def this(csp: CSP, smtSolver: SmtSolver) =
    this(csp, new Solver(csp, smtSolver = smtSolver))
  def this(smtSolver: SmtSolver) =
    this(CSP(), smtSolver = smtSolver)
  def this() =
    this(CSP())
  def use(newSolver: AbstractSolver): Unit = newSolver match {
    case sugarSolver: Solver =>
      solver = sugarSolver
  }
  def use(newSmtSolver: SmtSolver): Unit = {
    solver.smtSolver = newSmtSolver
    solver.addSolverInfo("smtSolver", newSmtSolver.toString)
  }
}

/**
 * Object for SMT DSL
 */
object dsl extends CoprisTrait {
  val smtVar = new util.DynamicVariable[SMT](new SMT())
  def csp = smtVar.value.csp
  def solver = smtVar.value.solver
  def using(smt: SMT = new SMT())(block: => Unit) =
    smtVar.withValue(smt) { block }
  def use(newSolver: AbstractSolver) =
    smtVar.value.use(newSolver)
  def use(smtSolver: SmtSolver) =
    smtVar.value.use(smtSolver)
}
