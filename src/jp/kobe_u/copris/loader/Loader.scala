package jp.kobe_u.copris.loader

import jp.kobe_u.copris._
import jp.kobe_u.{sugar => javaSugar}
import jp.kobe_u.sugar.expression.{Expression => SugarExpr}

import scala.collection.JavaConversions._

class SugarLoader(csp: CSP) {
  def parseSugar(fileName: String): javaSugar.csp.CSP = {
    javaSugar.SugarMain.init()
    javaSugar.converter.Converter.HOLD_CONSTRAINTS = true
    javaSugar.converter.Converter.INCREMENTAL_PROPAGATION = false
    val sugarMain = new javaSugar.SugarMain()
    val expressions = sugarMain.parse(fileName)
    val sugarCSP = new javaSugar.csp.CSP()
    val sugarConverter = new javaSugar.converter.Converter(sugarCSP)
    sugarConverter.convert(expressions)
    javaSugar.expression.Expression.clear()
    javaSugar.SugarMain.init()
    sugarCSP
  }

  def load(fileName: String) {
    val sugarCSP = parseSugar(fileName)
    translate(sugarCSP)
  }

  def translate(sugarCSP: javaSugar.csp.CSP) {
    for (v <- sugarCSP.getIntegerVariables.iterator) {
      val domain = v.getDomain()
      val x = Var(v.getName())
      if (domain.intervals().size == 1) {
        csp.int(x, domain.getLowerBound(), domain.getUpperBound())
      } else {
        val values = domain.values.map(_.toInt).toSet
        csp.int(x, Domain(values))
      }
    }
    for (v <- sugarCSP.getBooleanVariables.iterator) {
      val x = Bool(v.getName())
      csp.bool(x)
    }
    require(sugarCSP.getRelations().isEmpty(), "cannot load relations")
    val objectiveVariables = sugarCSP.getObjectiveVariables()
    require(objectiveVariables == null || objectiveVariables.size() <= 1, "cannot load multiple objective variables")
    if (sugarCSP.isMaximize()) {
      val x = Var(objectiveVariables.get(0).getName())
      csp.maximize(x)
    } else if (sugarCSP.isMinimize()) {
      val x = Var(objectiveVariables.get(0).getName())
      csp.minimize(x)
    }
    for (clause <- sugarCSP.getClauses().iterator) {
      val c = translateConstraint(clause)
      csp.add(c)
    }
  }

  def translateConstraint(clause: javaSugar.csp.Clause): Constraint = {
    val cs = clause.getLiterals().map(translateLiteral).toSeq
    if (cs.size == 0) FALSE
    else if (cs.size == 1) cs.head
    else Or(cs)
  }

  def translateLiteral(lit: javaSugar.csp.Literal): Constraint = {
    lit match {
      case holdLit: javaSugar.csp.HoldLiteral if ! holdLit.isNegative => {
        val ex = holdLit.getExpression()
        toConstraint(ex)
      }
      case _ =>
        throw new RuntimeException("cannot load " + lit)
    }
  }

  def toConstraint(ex: SugarExpr): Constraint = ex match {
    case _ if ex.equals(SugarExpr.TRUE) =>
      TRUE
    case _ if ex.equals(SugarExpr.FALSE) =>
      FALSE
    case a : javaSugar.expression.Atom =>
      Bool(a.stringValue())
    case seq : javaSugar.expression.Sequence => seq.getExpressions match {
      case Array(SugarExpr.NOT, x1) => Not(toConstraint(x1))
      case Array(SugarExpr.IMP, x1, x2) => Imp(toConstraint(x1), toConstraint(x2))
      case Array(SugarExpr.XOR, x1, x2) => Xor(toConstraint(x1), toConstraint(x2))
      case Array(SugarExpr.IFF, x1, x2) => Iff(toConstraint(x1), toConstraint(x2))
      case Array(SugarExpr.AND, xs @ _*) => And(xs.map(toConstraint))
      case Array(SugarExpr.OR, xs @ _*) => Or(xs.map(toConstraint))
      case Array(SugarExpr.EQ, x1, x2) => Eq(toTerm(x1), toTerm(x2))
      case Array(SugarExpr.NE, x1, x2) => Ne(toTerm(x1), toTerm(x2))
      case Array(SugarExpr.LE, x1, x2) => Le(toTerm(x1), toTerm(x2))
      case Array(SugarExpr.LT, x1, x2) => Lt(toTerm(x1), toTerm(x2))
      case Array(SugarExpr.GE, x1, x2) => Ge(toTerm(x1), toTerm(x2))
      case Array(SugarExpr.GT, x1, x2) => Gt(toTerm(x1), toTerm(x2))
      case Array(SugarExpr.ALLDIFFERENT, xs) => Alldifferent(toTerms(xs))
      case Array(SugarExpr.ALLDIFFERENT, xs @ _*) => Alldifferent(xs.map(toTerm))
      case Array(SugarExpr.WEIGHTEDSUM, x1, x2, x3) => {
        val axs = for (ax <- toExprs(x1); Seq(a,x) = toExprs(ax))
                  yield (a.integerValue().toInt, toTerm(x))
        val cmp = x2.stringValue()
        val b = toTerm(x3)
        Weightedsum(axs, cmp, b)
      }
      case Array(SugarExpr.CUMULATIVE, x1, x2) => {
        val tasks = for (task <- toExprs(x1); Seq(y1,y2,y3,y4) = toTerms(task))
                    yield (y1,y2,y3,y4)
        val limit = toTerm(x2)
        Cumulative(tasks, limit)
      }
      case Array(SugarExpr.ELEMENT, x1, x2, x3) => {
        val index = toTerm(x1)
        val xs = toTerms(x2)
        val xi = toTerm(x3)
        Element(index, xs, xi)
      }
      case Array(SugarExpr.DISJUNCTIVE, x1) => {
        val tasks = for (task <- toExprs(x1); Seq(y1,y2) = toTerms(task))
                    yield (y1,y2)
        Disjunctive(tasks)
      }
      case Array(SugarExpr.LEX_LESS, x1, x2) => {
        val xs = toTerms(x1)
        val ys = toTerms(x2)
        LexLess(xs, ys)
      }
      case Array(SugarExpr.LEX_LESSEQ, x1, x2) => {
        val xs = toTerms(x1)
        val ys = toTerms(x2)
        LexLesseq(xs, ys)
      }
      case Array(SugarExpr.NVALUE, x1, x2) => {
        val count = toTerm(x1)
        val xs = toTerms(x2)
        Nvalue(count, xs)
      }
      case Array(SugarExpr.GLOBAL_CARDINALITY, x1, x2) => {
        val xs = toTerms(x1)
        val card = for (ax <- toExprs(x2); Seq(a,x) = toExprs(ax))
                   yield (a.integerValue().toInt, toTerm(x))
        GlobalCardinality(xs, card)
      }
      case Array(SugarExpr.GLOBAL_CARDINALITY_WITH_COSTS, x1, x2, x3, x4) => {
        val xs = toTerms(x1)
        val card = for (ax <- toExprs(x2); Seq(a,x) = toExprs(ax))
                   yield (a.integerValue().toInt, toTerm(x))
        val table = for (t <- toExprs(x3); Seq(a1,a2,a3) = toExprs(t).map(_.integerValue().toInt))
                    yield (a1,a2,a3)
        val cost = toTerm(x4)
        GlobalCardinalityWithCosts(xs, card, table, cost)
      }
      case Array(SugarExpr.COUNT, x1, x2, x3, x4) => {
        val value = toTerm(x1)
        val xs = toTerms(x2)
        val cmp = x3.stringValue()
        val count = toTerm(x4)
        Count(value, xs, cmp, count)
      }
      case _ => throw new RuntimeException("cannot load " + ex)
    }
    case _ =>
      throw new RuntimeException("cannot load " + ex)
  }

  def toExprs(ex: SugarExpr): Seq[SugarExpr] =
    ex.asInstanceOf[javaSugar.expression.Sequence].getExpressions().toSeq

  def toTerms(ex: SugarExpr): Seq[Term] = toExprs(ex).map(toTerm)

  def toTerm(ex: SugarExpr): Term = ex match {
    case a : javaSugar.expression.Atom => {
      if (a.isInteger()) Num(a.integerValue())
      else if (a == SugarExpr.NIL) NIL
      else Var(a.stringValue())
    }
    case seq : javaSugar.expression.Sequence => seq.getExpressions() match {
      case Array(SugarExpr.ABS, x1) => Abs(toTerm(x1))
      case Array(SugarExpr.NEG, x1) => Neg(toTerm(x1))
      case Array(SugarExpr.ADD, xs @ _*) => Add(xs.map(toTerm))
      case Array(SugarExpr.SUB, xs @ _*) => Sub(xs.map(toTerm))
      case Array(SugarExpr.MUL, xs @ _*) => Mul(xs.map(toTerm))
      case Array(SugarExpr.DIV, x1, x2) => Div(toTerm(x1), toTerm(x2))
      case Array(SugarExpr.MOD, x1, x2) => Mod(toTerm(x1), toTerm(x2))
      case Array(SugarExpr.MAX, xs @ _*) => Max(xs.map(toTerm))
      case Array(SugarExpr.MIN, xs @ _*) => Min(xs.map(toTerm))
      case Array(SugarExpr.IF, x1, x2, x3) => If(toConstraint(x1), toTerm(x2), toTerm(x3))
      case _ => throw new RuntimeException("cannot load " + ex)
    }
    case _ =>
      throw new RuntimeException("cannot load " + ex)
  }
}

class XCSPLoader(csp: CSP) {
  def load(fileName: String) {
    val cspFile = java.io.File.createTempFile("copris", ".csp")
    cspFile.deleteOnExit
    val cspFileName = cspFile.getAbsolutePath
    val xml2csp = new javaSugar.XML2CSP(fileName, cspFileName)
    xml2csp.load()
    xml2csp.convert()
    val sugarLoader = new SugarLoader(csp)
    sugarLoader.load(cspFileName)
    cspFile.delete
  }
}
