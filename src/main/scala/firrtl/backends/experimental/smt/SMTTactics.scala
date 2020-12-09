package firrtl.backends.experimental.smt

import SMTTransitionSystemEncoder._
import scala.collection.mutable

object SMTTactics {

  def dispatch(sys: TransitionSystem)(s: Signal): List[SMTCommand] = 
    if (s.name.contains("memoryInduction"))
        memInduction(sys, s)
    else 
        List[SMTCommand]()

  def memInduction(sys: TransitionSystem, s: Signal): List[SMTCommand] = {
    val name = sys.name
    val cmds = mutable.ArrayBuffer[SMTCommand]()
    val assert_name = (SMTExprVisitor.map(symbolToFunApp(_, "", ""))(s.e) match {
      case BVImplies(_, BVRawExpr(name, width, BVSymbol(_, 1))) => name
    }).replace(" ", "").replace(")", "").replace("(", "")
    val predicate = sys.signals.filter(p => p.name.contains(assert_name)).head
    val registers = getSymbols(predicate.e, List()) ++ List("io_in")

    cmds += Comment("""""")
    cmds += Comment(""" Induction : Initial state of memory (state after reset holds) holds assertion""")
    cmds += Comment("""           : P(s) => p(next(s)) if s => next(s) is a valid transition """)

    // base case
    val init      = s.name + InitSuffix
    val next_init = s.name + NextSuffix + InitSuffix
    cmds += Comment("""""")
    cmds += Comment("""base case""")
    cmds += Push
    cmds += DeclareState(init, name + "_s")
    cmds += DeclareState(next_init, name + "_s")
    cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", init))(BVEqual(BVSymbol("reset_f", 1), BVLiteral(1, 1))))
    cmds += Assert(
      SMTExprVisitor
        .map(symbolToFunApp(_, "", init + " " + next_init))(BVEqual(BVSymbol(name + "_t", 1), BVLiteral(1, 1)))
    )
    cmds += Assert(
      SMTExprVisitor.map(symbolToFunApp(_, "", next_init))(BVNot(BVEqual(BVSymbol(name + "_a", 1), BVLiteral(1, 1))))
    )

    cmds += CheckSat
    val next_values = registers.filter(r => !r.contains("io_in")).map(r => (r + SignalSuffix, next_init))
    cmds += GetValue(next_values)
    cmds += Pop

    // inductive case
    val valid      = s.name + "_valid"
    val next_valid = s.name + NextSuffix + "_valid"
    cmds += Comment("""""")
    cmds += Comment("""inductive case""")
    cmds += Push
    cmds += DeclareState(valid, name + "_s")
    cmds += DeclareState(next_valid, name + "_s")
    cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", valid))(BVEqual(BVSymbol(name + "_a", 1), BVLiteral(1, 1))))
    cmds += Assert(
      SMTExprVisitor
        .map(symbolToFunApp(_, "", valid + " " + next_valid))(BVEqual(BVSymbol(name + "_t", 1), BVLiteral(1, 1)))
    )
    cmds += Assert(
      SMTExprVisitor.map(symbolToFunApp(_, "", next_valid))(BVNot(BVEqual(BVSymbol(name + "_a", 1), BVLiteral(1, 1))))
    )

    cmds += CheckSat
    val valid_values      = registers.map(r => (r + SignalSuffix, valid))
    val next_valid_values = registers.filter(r => !r.contains("io_in")).map(r => (r + SignalSuffix, next_valid))
    cmds += GetValue(valid_values ++ next_valid_values)
    cmds += Pop
    cmds += Comment("""""")
    cmds.toList
  }

  def getSymbols(e: SMTExpr, acc: List[String]): List[String] = e match {
    // nullary
    case BVLiteral(name, width)    => acc
    case BVSymbol(name, width)     => name :: acc
    case BVRawExpr(name, width, _) => name :: acc
    // unary
    case BVExtend(e, by, signed) => getSymbols(e, acc)
    case BVSlice(e, hi, lo)      => getSymbols(e, acc) // TODO:check
    case BVNot(e)                => getSymbols(e, acc)
    case BVNegate(e)             => getSymbols(e, acc)
    case BVReduceAnd(e)          => getSymbols(e, acc)
    case BVReduceOr(e)           => getSymbols(e, acc)
    case BVReduceXor(e)          => getSymbols(e, acc)
    // binary
    case BVImplies(a, b)                => getSymbols(b, getSymbols(a, acc))
    case BVEqual(a, b)                  => getSymbols(b, getSymbols(a, acc))
    case ArrayEqual(a, b)               => getSymbols(b, getSymbols(a, acc))
    case BVComparison(op, a, b, signed) => getSymbols(b, getSymbols(a, acc))
    case BVOp(op, a, b)                 => getSymbols(b, getSymbols(a, acc))
    case BVConcat(a, b)                 => getSymbols(b, getSymbols(a, acc))
    case ArrayRead(a, b)                => getSymbols(b, getSymbols(a, acc))
    case ArrayConstant(e, _)            => getSymbols(e, acc)
    // ternary
    case BVIte(a, b, c)              => getSymbols(c, getSymbols(b, getSymbols(a, acc)))
    case ArrayIte(a, b, c)           => getSymbols(c, getSymbols(b, getSymbols(a, acc)))
    case ArrayRawExpr(name, _, _, _) => name :: acc
    case ArraySymbol(name, _, _)     => name :: acc
    case ArrayStore(array, _, _)     => getSymbols(array, acc)
  }
}
