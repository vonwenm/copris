/*
 * This program is a part of Copris software package.
 * http://bach.istc.kobe-u.ac.jp/copris/
 */

import jp.kobe_u.copris._
import scala.io.Source

case class Graph(
  var nodes: Set[Int] = Set.empty, var edges: Set[(Int,Int)] = Set.empty) {
  def edge(n1: Int, n2: Int) = if (n1 < n2) (n1, n2) else (n2, n1)
  private var adjacentMap: Map[Int, Set[Int]] = Map.empty
  private def addAdjacent(n1: Int, n2: Int) =
    adjacentMap += n1 -> (adjacentMap.getOrElse(n1, Set.empty) + n2)
  def addNode(n1: Int) =
    nodes += n1
  def addEdge(n1: Int, n2: Int) =
    if (n1 != n2) {
      edges += edge(n1, n2)
      addAdjacent(n1, n2)
      addAdjacent(n2, n1)
    }
  def adjacent(n: Int) = adjacentMap(n)
  def adjacentEdge(n: Int) = adjacent(n).map(n2 => edge(n, n2))
}
object Graph {
  def parse(source: Source): Graph = {
    val graph = Graph()
    val re = """e\s+(\d+)\s+(\d+)""".r
    for (line <- source.getLines.map(_.trim)) {
      line match {
	case re(s1, s2) => {
	  val n1 = s1.toInt; graph.addNode(n1)
	  val n2 = s2.toInt; graph.addNode(n2)
	  graph.addEdge(n1, n2)
	}
	case _ =>
      }
    }
    graph
  }
}

abstract class CoprisApp extends Copris {
  var help = false
  var quiet = false
  var dumpFile: String = null
  def parseOptions(args: List[String]): List[String] = args match {
    case "-h" :: rest =>
      { help = true; parseOptions(rest) }
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
    case "-dump" :: file :: rest =>
      { dumpFile = file; parseOptions(rest) }
    case "-q" :: rest =>
      { quiet = true; parseOptions(rest) }
    case _ =>
      args
  }
  def showOptions = {
    println("\t-h          : Help")
    println("\t-q          : Quiet output")
    println("\t-s1 solver  : Use SAT solver (minisat, etc.)")
    println("\t-s2 solver  : Use SAT solver (precosat, etc.)")
    println("\t-smt solver : Use SMT solver (z3, etc.)")
    println("\t-jsr331     : Use JSR331 solver")
  }
}

/**
 * Hamiltonian Cycle Problem solver
 */
object HCP extends CoprisApp {
  var graph: Graph = null
  def addition(xs: Seq[Term]): Term = {
    if (xs.size < 8)
      Add(xs)
    else {
      val (xs1, xs2) = xs.splitAt(xs.size / 2)
      val x1 = int(Var(), 0, 1)
      val x2 = int(Var(), 0, 1)
      add(x1 === addition(xs1))
      add(x2 === addition(xs2))
      x1 + x2
    }
  }
  def define = {
    for ((n1,n2) <- graph.edges) {
      int('arc(n1,n2), 0, 1)
      int('arc(n2,n1), 0, 1)
      add('arc(n1,n2) + 'arc(n2,n1) <= 1)
    }
    for (n1 <- graph.nodes) {
      val nodes = graph.adjacent(n1).toSeq
      // in-degree(n1) == 1
      add(addition(nodes.map('arc(_,n1))) === 1)
      // out-degree(n1) == 1
      add(addition(nodes.map('arc(n1,_))) === 1)
    }
  }
  def getCycle(node: Int, initial: Int, cycle: List[Int]): List[Int] = {
    val node2 = graph.adjacent(node).find(node2 => solution('arc(node,node2)) > 0).get
    if (node2 == initial) {
      node2 :: cycle
    } else {
      getCycle(node2, initial, node2 :: cycle)
    }
  }
  def getCycles = {
    var cycles: Set[List[Int]] = Set.empty
    var nodes = graph.nodes
    while (! nodes.isEmpty) {
      val node = nodes.head
      val cycle = getCycle(node, node, List(node))
      cycles += cycle
      nodes --= cycle
    }
    cycles
  }
  def solve: Option[List[Int]] = {
    def arcs(cycle: List[Int]): Seq[(Int,Int)] =
      for (edge <- cycle.sliding(2).toList) yield (edge(0), edge(1))
    var hamiltonian: Option[List[Int]] = None
    var iteration = 0
    var count = 0
    while (hamiltonian == None && find) {
      val cycles = getCycles
      iteration += 1
      count += cycles.size
      println("Iteration " + iteration +
	      ": " + cycles.size + " cycles found (" + count + " cycles in total)")
      if (cycles.size == 1) {
	hamiltonian = Some(cycles.head)
      } else {
	for (cycle <- cycles) {
	  val arcs1 = for ((n1,n2) <- arcs(cycle)) yield 'arc(n1,n2) === 0
	  add(Or(arcs1))
	  val arcs2 = for ((n1,n2) <- arcs(cycle)) yield 'arc(n2,n1) === 0
	  add(Or(arcs2))
	}
      }
    }
    hamiltonian
  }
  def main(args: Array[String]) = {
    parseOptions(args.toList) match {
      case Nil if ! help =>
	graph = Graph.parse(Source.stdin)
      case file :: Nil if ! help =>
        graph = Graph.parse(Source.fromFile(file))
      case _ => {
        println("Usage: ./copris HCP [options] [inputFile]")
	showOptions
        println("Example: ./copris HCP 1-FullIns_3.col")
	System.exit(1)
      }
    }
    println(graph.nodes.size + " nodes, " + graph.edges.size + " edges")
    define
    if (dumpFile != null)
      dump(dumpFile)
    val hamiltonian = solve
    if (hamiltonian == None) {
      println("HC not found")
    } else {
      println("HC found")
      if (! quiet)
	println(hamiltonian.get.mkString(" "))
    }
  }
}
