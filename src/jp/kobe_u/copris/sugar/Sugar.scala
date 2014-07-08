package jp.kobe_u.copris.sugar

import jp.kobe_u.copris._
import jp.kobe_u.{sugar => javaSugar}
import jp.kobe_u.sugar.expression.{Expression => SugarExpr}

import scala.collection._

/**
 * Class for analyzing SAT solver log output
 */
abstract class SatSolverLogger(file: java.io.File) extends scala.sys.process.FileProcessLogger(file) {
  /** Status of SAT solver */
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
 * Abstract class for SAT solvers
 */
abstract class SatSolver(command: String, opts: Seq[String]) {
  import scala.sys.process._
  /** Runs the SAT solver */
  def run(satFileName: String, outFileName: String, logFileName: String, solver: Solver): Int
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
 * Class for SAT solvers with one argument
 */
class SatSolver1(command: String, opts: Seq[String] = Seq.empty) extends SatSolver(command, opts) {
  import scala.sys.process._
  def run(satFileName: String, outFileName: String, logFileName: String, solver: Solver): Int = {
    val outFile = new java.io.File(outFileName)
    outFile.delete
    val logger = ProcessLogger(outFile)
    runProcess(opts :+ satFileName, logger, solver)
  }
}
/**
 * Class for SAT solvers with two arguments
 */
class SatSolver2(command: String, opts: Seq[String] = Seq.empty) extends SatSolver(command, opts) {
  import scala.sys.process._
  def run(satFileName: String, outFileName: String, logFileName: String, solver: Solver): Int = {
    val logger = ProcessLogger(new java.io.File(logFileName))
    runProcess(opts :+ satFileName :+ outFileName, logger, solver)
  }
}
/**
 * Class for MiniSat solvers
 */
class MiniSat(command: String, opts: Seq[String]) extends SatSolver2(command, opts) {
  import scala.sys.process._
  override def run(satFileName: String, outFileName: String, logFileName: String, solver: Solver): Int = {
    val logger = new SatSolverLogger(new java.io.File(logFileName)) {
      val reVariables = """\|\s+Number of variables:\s+(\d+).*""".r
      val reClauses = """\|\s+Number of clauses:\s+(\d+).*""".r
      val reParse = """\|\s+Pars(e|ing) time:\s+([\d.]+)\s+s.*""".r
      val reData = """(c )?(restarts|conflicts|decisions|propagations)\s+:\s+(\d+).*""".r
      val reMemory = """(c )?Memory use\s+:\s+([\d.]+) MB.*""".r
      val reCPU = """(c )?CPU time\s+:\s+([\d.]+) s.*""".r
      def parseLog(s: String) = s match {
        case reVariables(n) => addStat("variables", n.toLong)
        case reClauses(n) => addStat("clauses", n.toLong)
        case reParse(dmy, n) => addStat("parse", n.toDouble)
        case reData(dmy, key, n) => addStat(key, n.toLong)
        case reMemory(dmy, n) => addStat("memory", n.toDouble)
        case reCPU(dmy, n) => addStat("cpu", n.toDouble * 1000)
        case _ =>
      }
    }
    val rc = runProcess(opts :+ satFileName :+ outFileName, logger, solver)
    solver.addSolverStat(command, logger.stat)
    rc
  }
}
/**
 * Class for Sat4j solver
 */
class Sat4j(command: String, opts: Seq[String]) extends SatSolver(command, opts) {
  import scala.collection.JavaConversions
  import org.sat4j.minisat.SolverFactory
  import org.sat4j.reader.Reader
  import org.sat4j.reader.DimacsReader
  import org.sat4j.specs.IProblem
  import org.sat4j.specs.ISolver
  import org.sat4j.specs.ContradictionException
  import org.sat4j.specs.TimeoutException
  import java.io.BufferedWriter
  import java.io.OutputStreamWriter
  import java.io.FileOutputStream
  override def run(satFileName: String, outFileName: String, logFileName: String, solver: Solver): Int = {
    val sat4jSolver: ISolver = SolverFactory.newDefault()
    val reader: Reader = new DimacsReader(sat4jSolver)
    val writer = new BufferedWriter(new OutputStreamWriter(
      new FileOutputStream(outFileName), "UTF-8"))
    try {
      solver.checkTimeout
      val problem: IProblem = reader.parseInstance(satFileName)
      solver.checkTimeout
      if (solver.timer != null && solver.timeout > 0) {
	val rest: Long = solver.timer.restTime
	if (rest > 0) {
          // println("sat4j timeout " + rest)
          sat4jSolver.setTimeoutMs(rest)
	}
      }
      if (problem.isSatisfiable()) {
        writer.write("SAT\n")
        val model = problem.model()
        val sb = new StringBuffer()
        for (i <- 0 until model.length) {
          sb.append(model(i))
          sb.append(" ");
        }
        sb.append("0\n");
        writer.write(sb.toString)
      } else {
        writer.write("UNSAT\n")
      }
    } catch {
      case e: ContradictionException => {
	writer.write("UNSAT\n")
      }
      case e: InterruptedException => {
        // println("kill sat4j interrupted")
        solver.raiseTimeout
      }
      case e: TimeoutException => {
        // println("kill sat4j")
        solver.raiseTimeout
      }
      case e: Exception => {
        println(e)
        throw e
      }
    } finally {
      writer.close()
      sat4jSolver.setTimeoutMs(0)
      sat4jSolver.reset
      // println("reset sat4j")
    }
    val stat = JavaConversions.mapAsScalaMap(sat4jSolver.getStat)
    solver.addSolverStat("sat4j", stat)
    sat4jSolver.setTimeoutMs(0)
    sat4jSolver.reset
    0
  }
}
/**
 * Object for PicoSat solver ("picosat")
 */
object PicoSat extends SatSolver1("picosat", Seq.empty)
/**
 * Object for PrecoSat solver ("precosat")
 */
object PrecoSat extends SatSolver1("precosat", Seq.empty)
/**
 * Object for MiniSat solver ("minisat")
 */
object MiniSat extends MiniSat("minisat", Seq.empty)
/**
 * Object for MiniSat 2 solver ("minisat2")
 */
object MiniSat2 extends MiniSat("minisat2", Seq.empty)
/**
 * Object for MiniSat 2.2 solver ("minisat22")
 */
object MiniSat22 extends MiniSat("minisat22", Seq.empty)
/**
 * Object for GlueMiniSat solver ("glueminisat")
 */
object GlueMiniSat extends MiniSat("glueminisat", Seq.empty)
/**
 * Object for Gluecose solver ("glucose")
 */
object Glucose extends MiniSat("glucose", Seq.empty)
/**
 * Object for Sat4j solver
 */
object Sat4j extends Sat4j("sat4j", Seq.empty)

/**
 * Class for translating CSP to a list of Sugar expressions
 */
class Translator {
  private var sugarVarNameMap: Map[Var,String] = Map.empty
  private var sugarBoolNameMap: Map[Bool,String] = Map.empty
  def createSugarExpr(x: SugarExpr, xs: SugarExpr*) =
    SugarExpr.create(x, xs.toArray)
  def toSugarName(name: String, is: String*): String =
    (Seq(name) ++ is.map(_.toString)).mkString("_").flatMap { c =>
      if (('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') ||
          ('0' <= c && c <= '9') || "_+-*/%=<>!&|".contains(c) ||
          (0x000080 <= c && c <= 0x10FFFF))
        c.toString
      else if (c < 0x100)
        "$%02x".format(c.toInt)
      else
        "$%04x".format(c.toInt)
    }
  def toSugarName(x: Var): String =
    sugarVarNameMap.getOrElse(x, {
      val s = toSugarName(x.name, x.is: _*)
      sugarVarNameMap += x -> s
      s
    })
  def toSugarName(p: Bool): String =
    sugarBoolNameMap.getOrElse(p, {
      val s = toSugarName(p.name, p.is: _*)
      sugarBoolNameMap += p -> s
      s
    })
  def toSugar(x: Term): SugarExpr = x match {
    case NIL =>
      SugarExpr.NIL
    case Num(value) =>
      SugarExpr.create(value)
    case Var(name, is @ _*) =>
      SugarExpr.create(toSugarName(name, is: _*))
    case Abs(x0) =>
      createSugarExpr(SugarExpr.ABS, toSugar(x0))
    case Neg(x0) =>
      createSugarExpr(SugarExpr.NEG, toSugar(x0))
    case Add(xs @ _*) =>
      createSugarExpr(SugarExpr.ADD, xs.map(toSugar(_)): _*)
    case Sub(xs @ _*) =>
      createSugarExpr(SugarExpr.SUB, xs.map(toSugar(_)): _*)
    case Mul(xs @ _*) =>
      xs.map(toSugar(_)).reduceLeft(createSugarExpr(SugarExpr.MUL, _, _))
    case Div(x0, x1) =>
      createSugarExpr(SugarExpr.DIV, toSugar(x0), toSugar(x1))
    case Mod(x0, x1) =>
      createSugarExpr(SugarExpr.MOD, toSugar(x0), toSugar(x1))
    case Max(xs @ _*) =>
      xs.map(toSugar(_)).reduceLeft(createSugarExpr(SugarExpr.MAX, _, _))
    case Min(xs @ _*) =>
      xs.map(toSugar(_)).reduceLeft(createSugarExpr(SugarExpr.MIN, _, _))
    case If(c, x0, x1) =>
      createSugarExpr(SugarExpr.IF, toSugar(c), toSugar(x0), toSugar(x1))
  }
  def toSugar(c: Constraint): SugarExpr = c match {
    case FALSE =>
      SugarExpr.FALSE
    case TRUE =>
      SugarExpr.TRUE
    case Bool(name, is @ _*) =>
      SugarExpr.create(toSugarName(name, is: _*))
    case Not(c0) =>
      createSugarExpr(SugarExpr.NOT, toSugar(c0))
    case And(cs @ _*) =>
      createSugarExpr(SugarExpr.AND, cs.map(toSugar(_)): _*)
    case Or(cs @ _*) =>
      createSugarExpr(SugarExpr.OR, cs.map(toSugar(_)): _*)
    case Imp(c0, c1) =>
      createSugarExpr(SugarExpr.IMP, toSugar(c0), toSugar(c1))
    case Xor(c0, c1) =>
      createSugarExpr(SugarExpr.XOR, toSugar(c0), toSugar(c1))
    case Iff(c0, c1) =>
      createSugarExpr(SugarExpr.IFF, toSugar(c0), toSugar(c1))
    case Eq(x0, x1) =>
      createSugarExpr(SugarExpr.EQ, toSugar(x0), toSugar(x1))
    case Ne(x0, x1) =>
      createSugarExpr(SugarExpr.NE, toSugar(x0), toSugar(x1))
    case Le(x0, x1) =>
      createSugarExpr(SugarExpr.LE, toSugar(x0), toSugar(x1))
    case Lt(x0, x1) =>
      createSugarExpr(SugarExpr.LT, toSugar(x0), toSugar(x1))
    case Ge(x0, x1) =>
      createSugarExpr(SugarExpr.GE, toSugar(x0), toSugar(x1))
    case Gt(x0, x1) =>
      createSugarExpr(SugarExpr.GT, toSugar(x0), toSugar(x1))
    case Alldifferent(xs @ _*) =>
      createSugarExpr(SugarExpr.ALLDIFFERENT, xs.map(toSugar(_)): _*)
    case Weightedsum(axs, cmp, b) =>
      createSugarExpr(SugarExpr.WEIGHTEDSUM, toSugarAny(axs), toSugarAny(cmp), toSugar(b))
    case Cumulative(tasks, limit) =>
      createSugarExpr(SugarExpr.CUMULATIVE, toSugarAny(tasks), toSugar(limit))
    case Element(i, xs, xi) =>
      createSugarExpr(SugarExpr.ELEMENT, toSugar(i), toSugarAny(xs), toSugar(xi))
    case Disjunctive(tasks @ _*) =>
      createSugarExpr(SugarExpr.DISJUNCTIVE, toSugarAny(tasks))
    case LexLess(xs, ys) =>
      createSugarExpr(SugarExpr.LEX_LESS, toSugarAny(xs), toSugarAny(ys))
    case LexLesseq(xs, ys) =>
      createSugarExpr(SugarExpr.LEX_LESSEQ, toSugarAny(xs), toSugarAny(ys))
    case Nvalue(count, xs) =>
      createSugarExpr(SugarExpr.NVALUE, toSugar(count), toSugarAny(xs))
    case GlobalCardinality(xs, card) =>
      createSugarExpr(SugarExpr.GLOBAL_CARDINALITY, toSugarAny(xs), toSugarAny(card))
    case GlobalCardinalityWithCosts(xs, card, table, cost) =>
      createSugarExpr(SugarExpr.GLOBAL_CARDINALITY_WITH_COSTS,
                      toSugarAny(xs), toSugarAny(card), toSugarAny(table), toSugar(cost))
    case Count(value, xs, cmp, count) =>
      createSugarExpr(SugarExpr.COUNT,
                      toSugar(value), toSugarAny(xs), toSugarAny(cmp), toSugar(count))
  }
  def toSugarAny(a: Any): SugarExpr = a match {
    case i: Int => SugarExpr.create(i)
    case s: String => SugarExpr.create(s)
    case x: Term => toSugar(x)
    case xs: Seq[Any] =>
      SugarExpr.create(xs.map(toSugarAny(_)).toArray)
    case p: (Any,Any) =>
      createSugarExpr(toSugarAny(p._1), toSugarAny(p._2))
    case p: (Any,Any,Any) =>
      createSugarExpr(toSugarAny(p._1), toSugarAny(p._2), toSugarAny(p._3))
    case p: (Any,Any,Any,Any) =>
      createSugarExpr(toSugarAny(p._1), toSugarAny(p._2), toSugarAny(p._3), toSugarAny(p._4))
  }
  def toSugarInt(csp: CSP, x: Var) = csp.dom(x) match {
    case d: IntervalDomain => {
      val lo = SugarExpr.create(d.lo)
      val hi = SugarExpr.create(d.hi)
      SugarExpr.create(SugarExpr.INT_DEFINITION, toSugar(x), lo, hi)
    }
    case d: SetDomain => {
      val dom = d.values.toList.sortWith(_ < _).map(SugarExpr.create(_))
      val xs = toSugar(x) :: SugarExpr.create(dom.toArray) :: Nil
      SugarExpr.create(SugarExpr.INT_DEFINITION, xs.toArray)
    }
  }
  def toSugarBool(csp: CSP, p: Bool) =
    SugarExpr.create(SugarExpr.BOOL_DEFINITION, toSugar(p))
  def toSugar(csp: CSP): java.util.ArrayList[SugarExpr] = {
    val expressions = new java.util.ArrayList[SugarExpr]()
    // println("Translating integer variables")
    csp.variables.foreach(v => expressions.add(toSugarInt(csp, v)))
    // println("Translating boolean variables")
    csp.bools.foreach(p => expressions.add(toSugarBool(csp, p)))
    // println("Translating constraints")
    // csp.constraints.foreach(c => expressions.add(toSugar(c)))
    val n = csp.constraints.size
    for (i <- 0 until n) {
      // if (i % 10000 == 0)
      // println("Translating " + i + "/" + n + " constraints")
      expressions.add(toSugar(csp.constraints(i)))
    }
    expressions
  }
  def toSugarDelta(csp: CSP): java.util.ArrayList[SugarExpr] = {
    val expressions = new java.util.ArrayList[SugarExpr]()
    csp.variablesDelta.foreach(v => expressions.add(toSugarInt(csp, v)))
    csp.boolsDelta.foreach(p => expressions.add(toSugarBool(csp, p)))
    csp.constraintsDelta.foreach(c => expressions.add(toSugar(c)))
    expressions
  }
}

/**
 * Class for encoding CSP to SAT
 */
class Encoder(csp: CSP, solver: Solver, satFileName: String, mapFileName: String) {
  var translator = new Translator()
  var sugarCSP = new javaSugar.csp.CSP()
  var converter = new javaSugar.converter.Converter(sugarCSP)
  var encoder = new javaSugar.encoder.Encoder(sugarCSP)
  def init {
    translator = new Translator()
    sugarCSP = new javaSugar.csp.CSP()
    converter = new javaSugar.converter.Converter(sugarCSP)
    encoder = new javaSugar.encoder.Encoder(sugarCSP)
  }
  def commit {
    // csp.commit
    sugarCSP.commit
    if (! sugarCSP.isUnsatisfiable)
      encoder.commit
  }
  def cancel {
    // csp.cancel
    sugarCSP.cancel
    encoder.cancel
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
      encoder.encode(satFileName, false)
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
 * Class for Sugar solver
 */
class Solver(csp: CSP, var satSolver: SatSolver = Sat4j) extends AbstractSolver(csp) {
  val solverName = "sugar"
  var satFileName: String = null
  var mapFileName: String = null
  var outFileName: String = null
  var logFileName: String = null
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
    satFileName = fileName("sat", ".cnf")
    mapFileName = fileName("map", ".map")
    outFileName = fileName("out", ".out")
    logFileName = fileName("log", ".log")
    javaSugar.SugarMain.init()
    encoder = new Encoder(csp, this, satFileName, mapFileName)
    encoder.init
    solution = null
    initial = true
    addSolverInfo("solver", solverName)
    addSolverInfo("satSolver", satSolver.toString)
    addSolverInfo("satFile", satFileName)
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
  @deprecated("use encodeDelta method of [[jp.kobe_u.copris.sugar.Solver]] instead", "2.2.0")
  def addDelta = encodeDelta
  def satSolve: Boolean = {
    addSolverStat("sat", "variables", encoder.encoder.getSatVariablesCount)
    addSolverStat("sat", "clauses", encoder.encoder.getSatClausesCount)
    addSolverStat("sat", "size", encoder.encoder.getSatFileSize)
    measureTime("time", "find") {
      satSolver.run(satFileName, outFileName, logFileName, this)
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
	encode && satSolve
      } else {
	encodeDelta
	satSolve
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
    satSolve
  }
  def findOptBody: Boolean = {
    val v = csp.objective
    if (csp.variables.contains(v)) {
      var lb = csp.dom(v).lb
      var ub = csp.dom(v).ub
      encode
      csp.commit
      commit
      val sat = satSolve
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
    satSolve
  }
  def dumpCSP(fileName: String) {
    import java.io._
    val translator = new Translator()
    val expressions = translator.toSugar(csp)
    val writer = new BufferedWriter(new OutputStreamWriter(
      new FileOutputStream(fileName)))
    for (i <- 0 until expressions.size)
      writer.write(expressions.get(i).toString + "\n")
    writer.close
  }
  def dumpCNF(fileName: String) {
    import java.io._
    import java.nio.channels._
    if (initial) encode else encodeDelta
    val in = new FileInputStream(satFileName).getChannel()
    val out = new FileOutputStream(fileName).getChannel()
    in.transferTo(0, in.size(), out)
    in.close()
    out.close()
  }
  def dump(fileName: String, format: String) {
    format match {
      case "" | "csp" => dumpCSP(fileName)
      case "cnf" => dumpCNF(fileName)
    }
  }
}

/**
 * Class for Sugar DSL
 */
class Sugar(val csp: CSP, var solver: Solver) extends CoprisTrait {
  def this(csp: CSP) =
    this(csp, new Solver(csp))
  def this(csp: CSP, satSolver: SatSolver) =
    this(csp, new Solver(csp, satSolver = satSolver))
  def this(satSolver: SatSolver) =
    this(CSP(), satSolver = satSolver)
  def this() =
    this(CSP())
  def use(newSolver: AbstractSolver): Unit = newSolver match {
    case sugarSolver: Solver =>
      solver = sugarSolver
  }
  def use(newSatSolver: SatSolver): Unit = {
    solver.satSolver = newSatSolver
    solver.addSolverInfo("satSolver", newSatSolver.toString)
  }
}

/**
 * Object for Sugar DSL
 */
object dsl extends CoprisTrait {
  val sugarVar = new util.DynamicVariable[Sugar](new Sugar())
  def csp = sugarVar.value.csp
  def solver = sugarVar.value.solver
  def using(sugar: Sugar = new Sugar())(block: => Unit) =
    sugarVar.withValue(sugar) { block }
  def use(newSolver: AbstractSolver) =
    sugarVar.value.use(newSolver)
  def use(satSolver: SatSolver) =
    sugarVar.value.use(satSolver)
}
