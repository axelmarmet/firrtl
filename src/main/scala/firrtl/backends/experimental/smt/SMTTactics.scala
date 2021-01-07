package firrtl.backends.experimental.smt

import SMTTransitionSystemEncoder._
import scala.collection.mutable

object SMTTactics {

  def dispatch(sys: TransitionSystem, delay : Int)(s: Signal): List[SMTCommand] =
    if (s.name.contains("memoryInduction"))
      memInduction(sys, s)
    else if (s.name.contains("combinatorial"))
      combinatorial(sys, s)
    else if (s.name.contains("loopInvariant"))
      loopInvariant(sys, s)
    else if (s.name.contains("BoundedModelCheck"))
      boundedModelCheck(sys, delay, s)
    else
      List[SMTCommand]()

  def printRegisters(e: SMTExpr, sys: TransitionSystem, states: List[String])(cmds: mutable.ArrayBuffer[SMTCommand]) = {
    def createValuePairs(regName: String): List[(String, String)] =
      states.map((regName + SignalSuffix, _))

    def getAllContributingSymbols(e: SMTExpr, s: TransitionSystem): List[String] = {
      var oldSymbolSet = Set[String]()
      var newSymbolSet = getSymbols(e)
      while (!oldSymbolSet.equals(newSymbolSet)) {
        oldSymbolSet = newSymbolSet
        val symbolsToAdd = s.signals
          .filter(s => oldSymbolSet.contains(s.name))
          .flatMap { case Signal(n, e) => getSymbols(e) }
        newSymbolSet =
          oldSymbolSet ++ symbolsToAdd
      }
      (s.inputs.flatMap{
        case BVSymbol(name, _) => if (newSymbolSet.contains(name)) List(name) else List()
      } ++
      s.states.filter {
        case State(symbol, _, _) => newSymbolSet.contains(symbol.name)
      }.map {
        case State(symbol, _, _) => symbol.name
      }).toList 
    }

    def getSymbols(e: SMTExpr): Set[String] = e match {
      case BVLiteral(value, width)                                     => Set()
      case BVSymbol(name, width)                                       => Set(name)
      case BVIn(e, delay)                                              => getSymbols(e)
      case BVExtend(e, by, signed)                                     => getSymbols(e)
      case BVSlice(e, hi, lo)                                          => getSymbols(e)
      case BVNot(e)                                                    => getSymbols(e)
      case BVNegate(e)                                                 => getSymbols(e)
      case BVReduceOr(e)                                               => getSymbols(e)
      case BVReduceAnd(e)                                              => getSymbols(e)
      case BVReduceXor(e)                                              => getSymbols(e)
      case BVImplies(a, b)                                             => getSymbols(a) ++ getSymbols(b)
      case BVEqual(a, b)                                               => getSymbols(a) ++ getSymbols(b)
      case BVComparison(op, a, b, signed)                              => getSymbols(a) ++ getSymbols(b)
      case BVOp(op, a, b)                                              => getSymbols(a) ++ getSymbols(b)
      case BVConcat(a, b)                                              => getSymbols(a) ++ getSymbols(b)
      case ArrayRead(array, index)                                     => getSymbols(array) ++ getSymbols(index)
      case BVIte(cond, tru, fals)                                      => getSymbols(cond) ++ getSymbols(tru) ++ getSymbols(fals)
      case ArraySymbol(name, indexWidth, dataWidth)                    => Set(name)
      case ArrayStore(array, index, data)                              => getSymbols(array) ++ getSymbols(index) ++ getSymbols(data)
      case ArrayIte(cond, tru, fals)                                   => getSymbols(cond) ++ getSymbols(tru) ++ getSymbols(fals)
      case ArrayEqual(a, b)                                            => getSymbols(a) ++ getSymbols(b)
      case ArrayConstant(e, indexWidth)                                => getSymbols(e)
      case BVRawExpr(serialized, width, initSymbol)                    => Set(serialized)
      case ArrayRawExpr(serialized, indexWidth, dataWidth, initSymbol) => Set(serialized)
    }

    getAllContributingSymbols(e, sys).foreach(s => cmds += GetValue(createValuePairs(s)))
  }

  def instantiateStates(states : List[String], sys : TransitionSystem)(cmds : mutable.ArrayBuffer[SMTCommand]){
    val systemName = sys.name
    states.foreach(cmds += DeclareState(_, systemName + "_s"))
    states.foreach(s =>
      cmds += Assert(BVRawExpr(s"(${systemName}_u $s)", 1, BVSymbol(s"${systemName}_u", 1)))
    )
    states.foreach(s =>
      cmds += Assert(BVNot(BVRawExpr(s"(reset_f $s)", 1, BVSymbol(systemName, 1))))
    )
    states.zip(states.tail).foreach{
      case (state, next_state) => cmds += Assert(BVRawExpr(s"(${systemName}_t $state $next_state)", 1, BVSymbol(systemName, 1)))
    }
  }

  def assumeDependencies(s : Signal, sys : TransitionSystem, states : List[String])(cmds : mutable.ArrayBuffer[SMTCommand]) {
    cmds += Comment("Assume the dependencies")
    sys.assumeDeps(s.name).foreach(dep => 
      states.foreach(state =>
        cmds += Assert(BVRawExpr(s"(${dep}_f $state)", 1, BVSymbol(sys.name, 1)))
      )
    )
  }

  def memInduction(sys: TransitionSystem, s: Signal): List[SMTCommand] = {
    val name = sys.name
    val cmds = mutable.ArrayBuffer[SMTCommand]()

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
    cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", init))(BVSymbol("reset_f", 1)))
    cmds += Assert(
      SMTExprVisitor
        .map(symbolToFunApp(_, "", init + " " + next_init))(BVSymbol(name + "_t", 1))
    )
    cmds += Assert(
      SMTExprVisitor.map(symbolToFunApp(_, "", next_init))(BVNot(BVSymbol(name + "_a", 1)))
    )

    cmds += CheckSat
    printRegisters(s.e, sys, List(init, next_init))(cmds)
    cmds += Pop

    // inductive case
    val valid      = s.name + "_valid"
    val next_valid = s.name + NextSuffix + "_valid"
    cmds += Comment("""""")
    cmds += Comment("""inductive case""")
    cmds += Push
    cmds += DeclareState(valid, name + "_s")
    cmds += DeclareState(next_valid, name + "_s")
    cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", valid))(BVSymbol(name + "_a", 1)))
    cmds += Assert(
      SMTExprVisitor
        .map(symbolToFunApp(_, "", valid + " " + next_valid))(BVSymbol(name + "_t", 1))
    )
    cmds += Assert(
      SMTExprVisitor.map(symbolToFunApp(_, "", next_valid))(BVNot(BVSymbol(name + "_a", 1)))
    )

    cmds += CheckSat
    printRegisters(s.e, sys, List(valid, next_valid))(cmds)
    cmds += Pop
    cmds += Comment("""""")
    cmds.toList
  }

  def combinatorial(sys: TransitionSystem, s: Signal): List[SMTCommand] = {
    val name = sys.name
    val cmds = mutable.ArrayBuffer[SMTCommand]()

    cmds += LineBreak
    cmds += Comment(""" Combinatorial """)
    cmds += Push

    val state = s.name
    instantiateStates(List(state), sys)(cmds)
    assumeDependencies(s, sys, List(state))(cmds)
    cmds += Assert(
      SMTExprVisitor.map(symbolToFunApp(_, "", state))(BVNot(BVSymbol(s.name + "_f", 1)))
    )
    cmds += CheckSat
    printRegisters(s.e, sys, List(state))(cmds)
    cmds += Pop
    cmds += LineBreak
    
    cmds.toList
  }

  def loopInvariant(sys: TransitionSystem, s: Signal): List[SMTCommand] = {
    val systemName = sys.name
    val assertName = s"${s.name}_f"
    val cmds       = mutable.ArrayBuffer[SMTCommand]()
    // val assertName = (SMTExprVisitor.map(symbolToFunApp(_, "", ""))(s.e) match {
    //   case BVImplies(_, BVRawExpr(name, width, BVSymbol(_, 1))) => name
    // }).replace(" ", "").replace(")", "").replace("(", "")
    //val predicate = sys.signals.filter(p => p.name.contains(s.n)).head

    cmds += Comment("""""")
    cmds += Comment(""" Induction on Loop Invariant : if state S is in a loop""")
    cmds += Comment("""           : P(s) => p(next(s)) if s => next(s) is a valid transition """)

    // inductive case
    val valid      = "s0"
    val next_valid = "s1"
    cmds += Comment("""""")
    cmds += Comment("""inductive case""")
    cmds += Push
    instantiateStates(List(valid, next_valid), sys)(cmds)
    cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", valid))(BVSymbol(assertName, 1)))
    cmds += Assert(
      SMTExprVisitor.map(symbolToFunApp(_, "", next_valid))(BVNot(BVSymbol(assertName, 1)))
    )

    cmds += CheckSat
    printRegisters(s.e, sys, List(valid, next_valid))(cmds)
    // val valid_values      = registers.map(r => (r + SignalSuffix, valid))
    // val next_valid_values = registers.filter(r => !r.contains("io_in")).map(r => (r + SignalSuffix, next_valid))
    // cmds += GetValue(valid_values ++ next_valid_values)
    cmds += Pop
    cmds += Comment("""""")
    cmds.toList
  }

  def boundedModelCheck(sys: TransitionSystem, delay: Int, s: Signal): List[SMTCommand] = {
    val systemName = sys.name
    val assertName = s"${s.name}_f"
    val cmds       = mutable.ArrayBuffer[SMTCommand]()

    cmds += Push
    val states = (0 to delay).map(i => s"state_$i").toList
    instantiateStates(states, sys)(cmds)
    assumeDependencies(s, sys, states)(cmds)

    cmds += Assert(BVNot(BVRawExpr(s"($assertName ${states.reduce(_ ++ " " ++ _)})", 1, BVSymbol(systemName, 1))))
    cmds += CheckSat
    printRegisters(s.e, sys, states)(cmds)
    cmds += Pop
  
    cmds.toList
  }

}
