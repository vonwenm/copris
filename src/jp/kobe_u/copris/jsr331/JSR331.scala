package jp.kobe_u.copris.jsr331

import jp.kobe_u.copris._

import javax.constraints.{Problem => Jsr331Problem}
import javax.constraints.{Solver => Jsr331Solver}
import javax.constraints.{Var => Jsr331Var}
import javax.constraints.{VarBool => Jsr331VarBool}
import javax.constraints.{Constraint => Jsr331Constraint}
import javax.constraints.{SolutionIterator => Jsr331SolutionIterator}

class Translator(csp: CSP, problem: Jsr331Problem) {
  private var jsr331VarMap: Map[Var,Jsr331Var] = Map.empty
  private var jsr331BoolMap: Map[Bool,Jsr331VarBool] = Map.empty
  def error(x: Expr) = {
    new RuntimeException("Cannot translate " + x)
  }
  def toJsr331Name(name: String, is: String*): String =
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
  def toJsr331Name(x: Var): String = toJsr331Name(x.name, x.is: _*)
  def toJsr331Name(p: Bool): String = toJsr331Name(p.name, p.is: _*)
  def toJsr331Var(x: Var): Jsr331Var =
    jsr331VarMap.getOrElse(x, {
      val name = toJsr331Name(x)
      val v = csp.dom(x) match {
	case d: IntervalDomain => {
	  problem.variable(name, d.lo, d.hi)
	}
	case d: SetDomain => {
	  val dom = d.values.toArray
	  problem.variable(name, dom)
	}
      }
      jsr331VarMap += x -> v
      v
    })
  def toJsr331VarBool(p: Bool): Jsr331VarBool =
    jsr331BoolMap.getOrElse(p, {
      val name = toJsr331Name(p)
      val v = problem.variableBool(name)
      jsr331BoolMap += p -> v
      v
    })
  def toJsr331Op(cmp: String) = cmp match {
    case "eq" => "="
    case "ne" => "!="
    case "lt" => "<"
    case "le" => "<="
    case "gt" => ">"
    case "ge" => ">="
  }
  def toJsr331(x: Term): Jsr331Var = x match {
    case NIL =>
      throw error(x)
    case Num(value) =>
      problem.variable(value, value)
    case v @ Var(name, is @ _*) =>
      toJsr331Var(v)
    case Abs(x0) =>
      toJsr331(x0).abs()
    case Neg(x0) =>
      toJsr331(x0).negative()
    case Add(xs @ _*) =>
      xs.map(toJsr331).reduce(_ plus _)
    case Sub(xs @ _*) =>
      toJsr331(xs.head).minus(toJsr331(Add(xs.tail: _*)))
    case Mul(xs @ _*) =>
      xs.map(toJsr331).reduce(_ multiply _)
    case Div(x0, x1) =>
      toJsr331(x0).divide(toJsr331(x1))
    case Mod(x0, x1) =>
      toJsr331(x0 - x1 * (x0 / x1))
    case Max(xs @ _*) =>
      problem.max(xs.map(toJsr331).toArray)
    case Min(xs @ _*) =>
      problem.min(xs.map(toJsr331).toArray)
    case If(c, x0, x1) => {
      val b = toJsr331(c).asBool()
      // x1 + b * (x0 - x1)
      toJsr331(x1).plus(b.multiply(toJsr331(x0 - x1)))
    }
  }
  def toJsr331(c: Constraint): Jsr331Constraint = c match {
    case FALSE =>
      problem.getFalseConstraint()
    case TRUE =>
      problem.getTrueConstraint()
    case v @ Bool(name, is @ _*) =>
      problem.linear(toJsr331VarBool(v), ">", 0)
    case Not(c0) =>
      toJsr331(c0).negation()
    case And(cs @ _*) =>
      if (cs.isEmpty) toJsr331(TRUE)
      else if (cs.size == 1) toJsr331(cs(0))
      else cs.map(toJsr331).reduce(_ and _)
    case Or(cs @ _*) =>
      if (cs.isEmpty) toJsr331(FALSE)
      else if (cs.size == 1) toJsr331(cs(0))
      else cs.map(toJsr331).reduce(_ or _)
    case Imp(c0, c1) =>
      toJsr331(c0).implies(toJsr331(c1))
    case Xor(c0, c1) =>
      toJsr331((c0 || c1) && (! c0 || ! c1))
    case Iff(c0, c1) =>
      toJsr331((c0 ==> c1) && (c1 ==> c0))
    case Eq(x0, x1) =>
      problem.linear(toJsr331(x0), "=", toJsr331(x1))
    case Ne(x0, x1) =>
      problem.linear(toJsr331(x0), "!=", toJsr331(x1))
    case Le(x0, x1) =>
      problem.linear(toJsr331(x0), "<=", toJsr331(x1))
    case Lt(x0, x1) =>
      problem.linear(toJsr331(x0), "<", toJsr331(x1))
    case Ge(x0, x1) =>
      problem.linear(toJsr331(x0), ">=", toJsr331(x1))
    case Gt(x0, x1) =>
      problem.linear(toJsr331(x0), ">", toJsr331(x1))
    case Alldifferent(xs @ _*) =>
      problem.allDiff(xs.map(toJsr331).toArray)
    case Weightedsum(axs, cmp, b) => {
      val as = axs.map(_._1)
      val xs = axs.map(_._2)
      val sum = problem.scalProd(as.toArray, xs.map(toJsr331).toArray)
      val op = toJsr331Op(cmp)
      problem.linear(sum.minus(toJsr331(b)), op, 0)
    }
    case Cumulative(tasks, limit) =>
      throw error(c)
    case Element(i, xs, xi) => {
      val x = problem.element(xs.map(toJsr331).toArray, toJsr331(i - 1))
      problem.linear(x, "=", toJsr331(xi))
    }
    case Disjunctive(tasks @ _*) =>
      throw error(c)
    case LexLess(xs, ys) =>
      throw error(c)
    case LexLesseq(xs, ys) =>
      throw error(c)
    case Nvalue(count, xs) =>
      throw error(c)
    case GlobalCardinality(xs, card) =>
      throw error(c)
    case GlobalCardinalityWithCosts(xs, card, table, cost) =>
      throw error(c)
    case Count(value, xs, cmp, count) =>
      throw error(c)
  }
  def translate(v: Var): Unit = toJsr331Var(v)
  def translate(p: Bool): Unit = toJsr331VarBool(p)
  def translate(c: Constraint) {
    c match {
      case GlobalCardinality(xs, card) => {
	val vs = xs.map(toJsr331).toArray
	val as = card.map(_._1).toArray
	val cs = card.map(_._2).map(toJsr331).toArray
	problem.postGlobalCardinality(vs, as, cs)
      }
      case Count(value, xs, cmp, count) => {
	val vs = xs.map(toJsr331).toArray
	val v1 = toJsr331(value)
	val op = toJsr331Op(cmp)
	val v2 = toJsr331(count)
	problem.postCardinality(vs, v1, op, v2)
      }
      case _ =>
	problem.post(toJsr331(c))
    }
  }
  def translate {
    // println("Translating integer variables")
    for (v <- csp.variables)
      translate(v)
    // println("Translating boolean variables")
    for (p <- csp.bools)
      translate(p)
    // println("Translating constraints")
    for (c <- csp.constraints)
      translate(c)
  }
  def translateDelta {
    for (v <- csp.variablesDelta)
      translate(v)
    for (p <- csp.boolsDelta)
      translate(p)
    for (c <- csp.constraintsDelta)
      translate(c)
  }
}

/**
 * Class for JSR331 solver
 */
class Solver(csp: CSP) extends AbstractSolver(csp) {
  var translated = false
  var solution: Solution = _
  var problem: Jsr331Problem = _
  var solver: Jsr331Solver = _
  var translator: Translator = _
  var solutionIterator: Jsr331SolutionIterator = _
  init

  def error(msg: String) = {
    new RuntimeException(msg)
  }
  override def init {
    super.init
    solution = null
    problem = javax.constraints.ProblemFactory.newProblem("Copris")
    translator = new Translator(csp, problem)
    addSolverInfo("solver", problem.getImplVersion())
    translated = false
  }
  private def _setUp {
    if (! translated) {
      translator.translate
      solver = problem.getSolver()
      val strategy = solver.getSearchStrategy()
      val intVars = csp.variables.map(translator.toJsr331Var(_))
      val boolVars = csp.bools.map(translator.toJsr331VarBool(_))
      strategy.setVars((intVars ++ boolVars).toArray)
      translated = true
    }
  }
  private def _setSolution(sol: javax.constraints.Solution) = {
    val intValues =
      csp.variables.map(v => v -> sol.getValue(translator.toJsr331Name(v))).toMap
    val boolValues =
      csp.bools.map(p => p -> (sol.getValue(translator.toJsr331Name(p)) > 0)).toMap
    solution = Solution(intValues, boolValues)
  }
  def commit {
    throw error("commit")
  }
  def cancel {
    throw error("cancel")
  }
  def findBody: Boolean = {
    _setUp
    solutionIterator = solver.solutionIterator()
    findNextBody
  }
  def findNextBody: Boolean = {
    solution = null
    if (solutionIterator.hasNext()) {
      val sol = solutionIterator.next()
      _setSolution(sol)
    }
    solution != null
  }
  def findOptBody: Boolean = {
    _setUp
    val v = translator.toJsr331Var(csp.objective)
    val sol = 
      if (csp.isMinimize)
	solver.findOptimalSolution(javax.constraints.Objective.MINIMIZE, v)
      else
	solver.findOptimalSolution(javax.constraints.Objective.MAXIMIZE, v)
    _setSolution(sol)
    solution != null
  }
  def findOptBoundBody(lb: Int, ub: Int): Boolean = {
    throw error("findOptBoundBody")
  }
  def dumpCSP(fileName: String) {
    import java.io._
    val writer = new BufferedWriter(new OutputStreamWriter(
      new FileOutputStream(fileName)))
    _setUp
    if (problem.getVars() != null) {
      for (v <- problem.getVars())
	writer.write(v.getImpl().toString + "\n")
    }
    if (problem.getVarBools() != null) {
      for (p <- problem.getVarBools())
	writer.write(p.getImpl().toString + "\n")
    }
    if (problem.getConstraints() != null) {
      for (c <- problem.getConstraints())
	writer.write(c.getImpl().toString + "\n")
    }
    writer.close
  }
  def dump(fileName: String, format: String) {
    format match {
      case "" | "csp" => dumpCSP(fileName)
    }
  }
}

/**
 * Class for JSR331 DSL
 */
class JSR331(val csp: CSP, var solver: Solver) extends CoprisTrait {
  def this(csp: CSP) =
    this(csp, new Solver(csp))
  def this() =
    this(CSP())
  def use(newSolver: AbstractSolver): Unit = newSolver match {
    case jsr331Solver: Solver =>
      solver = jsr331Solver
  }
}

/**
 * Object for JSR331 DSL
 */
object dsl extends CoprisTrait {
  val jsr331Var = new util.DynamicVariable[JSR331](new JSR331())
  def csp = jsr331Var.value.csp
  def solver = jsr331Var.value.solver
  def using(jsr331: JSR331 = new JSR331())(block: => Unit) =
    jsr331Var.withValue(jsr331) { block }
  def use(newSolver: AbstractSolver) =
    jsr331Var.value.use(newSolver)
}
