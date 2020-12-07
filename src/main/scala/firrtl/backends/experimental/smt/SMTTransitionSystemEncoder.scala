// SPDX-License-Identifier: Apache-2.0
// Author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package firrtl.backends.experimental.smt

import scala.collection.mutable
import java.io.PushbackInputStream

/** This Transition System encoding is directly inspired by yosys' SMT backend:
  * https://github.com/YosysHQ/yosys/blob/master/backends/smt2/smt2.cc
  * It if fairly compact, but unfortunately, the use of an uninterpreted sort for the state
  * prevents this encoding from working with boolector.
  * For simplicity reasons, we do not support hierarchical designs (no `_h` function).
  */
private object SMTTransitionSystemEncoder {

  def encode(sys: TransitionSystem): Iterable[SMTCommand] = {
    val cmds = mutable.ArrayBuffer[SMTCommand]()
    val name = sys.name

    // emit header as comments
    cmds ++= sys.header.map(Comment)

    // declare state type
    val stateType = id(name + "_s")
    cmds += DeclareUninterpretedSort(stateType)

    // inputs and states are modelled as constants
    def declare(sym: SMTSymbol, kind: String): Unit = {
      cmds ++= toDescription(sym, kind, sys.comments.get)
      val s = SMTSymbol.fromExpr(sym.name + SignalSuffix, sym)
      cmds += DeclareFunction(s, List(stateType))
    }
    sys.inputs.foreach(i => declare(i, "input"))
    sys.states.foreach(s => declare(s.sym, "register"))

    // signals are just functions of other signals, inputs and state
    def define(sym: SMTSymbol, e: SMTExpr, suffix: String = SignalSuffix): Unit = {
      cmds += DefineFunction(sym.name + suffix, List((State, stateType)), replaceSymbols(e))
    }
    sys.signals.foreach { signal =>
      val kind = if (sys.outputs.contains(signal.name)) { "output" }
      else if (sys.assumes.contains(signal.name)) { "assume" }
      else if (sys.asserts.contains(signal.name)) { "assert" }
      else { "wire" }
      val sym = SMTSymbol.fromExpr(signal.name, signal.e)
      cmds ++= toDescription(sym, kind, sys.comments.get)
      define(sym, signal.e)
    }

    // define the next and init functions for all states
    sys.states.foreach { state =>
      assert(state.next.nonEmpty, "Next function required")
      define(state.sym, state.next.get, NextSuffix)
      // init is optional
      state.init.foreach { init =>
        define(state.sym, init, InitSuffix)
      }
    }

    def defineConjunction(e: Iterable[BVExpr], suffix: String): Unit = {
      define(BVSymbol(name, 1), andReduce(e), suffix)
    }

    // the transition relation asserts that the value of the next state is the next value from the previous state
    // e.g., (reg state_n) == (reg_next state)
    val transitionRelations = sys.states.map { state =>
      val newState = symbolToFunApp(state.sym, SignalSuffix, StateNext)
      val nextOldState = symbolToFunApp(state.sym, NextSuffix, State)
      SMTEqual(newState, nextOldState)
    }
    // the transition relation is over two states
    val transitionExpr = replaceSymbols(andReduce(transitionRelations))
    cmds += Comment(
"""This function evaluates to ’true’ if the states ’state’ and
’next_state’ form a valid state transition.""""
    )
    cmds += DefineFunction(name + "_t", List((State, stateType), (StateNext, stateType)), transitionExpr)

    // The init relation just asserts that all init function hold
    val initRelations = sys.states.filter(_.init.isDefined).map { state =>
      val stateSignal = symbolToFunApp(state.sym, SignalSuffix, State)
      val initSignal = symbolToFunApp(state.sym, InitSuffix, State)
      SMTEqual(stateSignal, initSignal)
    }

    cmds += Comment(
"""This function must be asserted ’true’ for initial states. For
non-initial states it must be left unconstrained.""")
    defineConjunction(initRelations, "_i")

    // assertions and assumptions
    val assertions = sys.signals.filter(a => sys.asserts.contains(a.name)).map(a => replaceSymbols(a.toSymbol))
    cmds += Comment(
"""This function evaluates to ’true’ if all assertions hold in the state.""")
    defineConjunction(assertions, "_a")
    val assumptions = sys.signals.filter(a => sys.assumes.contains(a.name)).map(a => replaceSymbols(a.toSymbol))
    cmds += Comment(
"""This function evaluates to ’true’ if all assumptions hold in the state.""")
    defineConjunction(assumptions, "_u")


    // For all assertions (assumptions?) check for a methodology and apply it if present.
    val asserts = sys.signals.filter(a => sys.asserts.contains(a.name))
    generateMethod(asserts)

    // TODO: might want to move the following functions in a separate file
    def generateMethod(asserts: Iterable[Signal]): Unit = {
      val memInductions = asserts.filter(a => a.name.contains("memoryInduction"))
      memInduction(memInductions)
    }

    def memInduction(asserts: Iterable[Signal]): Unit = asserts.foreach { s =>
      val assert_name = (SMTExprVisitor.map(symbolToFunApp(_, "", ""))(s.e) match { case BVImplies(_, BVRawExpr(name, width)) => name }).
                  replace(" ", "").replace(")", "").replace("(", "")
      val predicate = sys.signals.filter(p => p.name.contains(assert_name)).head
      val registers = getSymbols(predicate.e, List()) ++ List("io_in")

      cmds += Comment("""""")
      cmds += Comment(""" Induction : Initial state of memory (state after reset holds) holds assertion""")
      cmds += Comment("""           : P(s) => p(next(s)) if s => next(s) is a valid transition """)

      // base case 
      val init = s.name + InitSuffix
      val next_init = s.name + NextSuffix + InitSuffix
      cmds += Comment("""""")
      cmds += Comment("""base case""")
      cmds += Push()
      cmds += DeclareState(init, List(), BVRawExpr(name + "_s", 1))
      cmds += DeclareState(next_init, List(), BVRawExpr(name + "_s", 1))
      cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", init))(BVEqual(BVSymbol("reset_f", 1), BVRawExpr("true", 1))))
      cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", init + " " + next_init))(BVEqual(BVSymbol(name + "_t", 1), BVRawExpr("true", 1))))
      cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", next_init))(BVNot(BVEqual(BVSymbol(name + "_a", 1), BVRawExpr("true", 1)))))

      cmds += CheckSAT()
      val next_values = registers.filter(r => !r.contains("io_in")).map(r => (r + SignalSuffix, next_init))
      cmds += GetValue(next_values)
      cmds += Pop()

      // inductive case
      val valid = s.name + "_valid"
      val next_valid = s.name + NextSuffix + "_valid"
      cmds += Comment("""""")
      cmds += Comment("""inductive case""")
      cmds += Push()
      cmds += DeclareState(valid, List(), BVRawExpr(name + "_s", 1))
      cmds += DeclareState(next_valid, List(), BVRawExpr(name + "_s", 1))
      cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", valid))(BVEqual(BVSymbol(name + "_a", 1), BVRawExpr("true", 1))))
      cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", valid + " " + next_valid))(BVEqual(BVSymbol(name + "_t", 1), BVRawExpr("true", 1))))
      cmds += Assert(SMTExprVisitor.map(symbolToFunApp(_, "", next_valid))(BVNot(BVEqual(BVSymbol(name + "_a", 1), BVRawExpr("true", 1)))))

      cmds += CheckSAT()
      val valid_values = registers.map(r => (r + SignalSuffix, valid))
      val next_valid_values = registers.filter(r => !r.contains("io_in")).map(r => (r + SignalSuffix, next_valid))
      cmds += GetValue(valid_values ++ next_valid_values)
      cmds += Pop()
      cmds += Comment("""""")
    }

    def getSymbols(e: SMTExpr, acc: List[String]): List[String] = e match {
      // nullary
      case BVLiteral(name, width)   => acc
      case BVSymbol(name, width)    => name :: acc
      case BVRawExpr(name, width)   => name :: acc
      // unary
      case BVExtend(e, by, signed)  => getSymbols(e, acc)
      case BVSlice(e, hi, lo)       => getSymbols(e, acc) // TODO:check
      case BVNot(e)                 => getSymbols(e, acc)
      case BVNegate(e)              => getSymbols(e, acc)
      case BVReduceAnd(e)           => getSymbols(e, acc)
      case BVReduceOr(e)            => getSymbols(e, acc)
      case BVReduceXor(e)           => getSymbols(e, acc)
      // binary
      case BVImplies(a, b)          => getSymbols(b, getSymbols(a, acc))
      case BVEqual(a, b)            => getSymbols(b, getSymbols(a, acc))
      case ArrayEqual(a, b)         => getSymbols(b, getSymbols(a, acc))
      case BVComparison(op, a, b, signed) 
                                    => getSymbols(b, getSymbols(a, acc))
      case BVOp(op, a, b)           => getSymbols(b, getSymbols(a, acc))
      case BVConcat(a, b)           => getSymbols(b, getSymbols(a, acc))
      case ArrayRead(a, b)          => getSymbols(b, getSymbols(a, acc))
      case ArrayConstant(e, _)      => getSymbols(e, acc)
      // ternary
      case BVIte(a, b, c)           => getSymbols(c, getSymbols(b, getSymbols(a, acc)))
      case ArrayIte(a, b, c)        => getSymbols(c, getSymbols(b, getSymbols(a, acc)))
      case ArrayRawExpr(name, _, _) => name :: acc
      case ArraySymbol(name, _, _)  => name :: acc
      case ArrayStore(array, _, _)  => getSymbols(array, acc)
    } 
    
    cmds
  }

  private def id(s: String): String = SMTLibSerializer.escapeIdentifier(s)
  private val State = "state"
  private val StateNext = "state_n"
  private val SignalSuffix = "_f"
  private val NextSuffix = "_next"
  private val InitSuffix = "_init"
  private def toDescription(sym: SMTSymbol, kind: String, comments: String => Option[String]): List[Comment] = {
    List(sym match {
      case BVSymbol(name, width) =>
        Comment(s"firrtl-smt2-$kind $name $width")
      case ArraySymbol(name, indexWidth, dataWidth) =>
        Comment(s"firrtl-smt2-$kind $name $indexWidth $dataWidth")
    }) ++ comments(sym.name).map(Comment)
  }

  private def andReduce(e: Iterable[BVExpr]): BVExpr =
    if (e.isEmpty) BVLiteral(1, 1) else e.reduce((a, b) => BVOp(Op.And, a, b))

  // All signals are modelled with functions that need to be called with the state as argument,
  // this replaces all Symbols with function applications to the state.
  private def replaceSymbols(e: SMTExpr): SMTExpr = {
    SMTExprVisitor.map(symbolToFunApp(_, SignalSuffix, State))(e)
  }
  private def replaceSymbols(e:   BVExpr): BVExpr = replaceSymbols(e.asInstanceOf[SMTExpr]).asInstanceOf[BVExpr]
  private def symbolToFunApp(sym: SMTExpr, suffix: String, arg: String): SMTExpr = sym match {
    case BVSymbol(name, width)                    => BVRawExpr(s"(${id(name + suffix)} $arg)", width)
    case ArraySymbol(name, indexWidth, dataWidth) => ArrayRawExpr(s"(${id(name + suffix)} $arg)", indexWidth, dataWidth)
    case other                                    => other
  }
}

/** minimal set of pseudo SMT commands needed for our encoding */
private sealed trait SMTCommand
private case class Comment(msg: String) extends SMTCommand
private case class DefineFunction(name: String, args: Seq[(String, String)], e: SMTExpr) extends SMTCommand
private case class DeclareFunction(sym: SMTSymbol, tpes: Seq[String]) extends SMTCommand
private case class DeclareUninterpretedSort(name: String) extends SMTCommand
private case class Push() extends SMTCommand
private case class Pop() extends SMTCommand
private case class CheckSAT() extends SMTCommand
private case class Assert(e: SMTExpr) extends SMTCommand
private case class DeclareState(name: String, args: Seq[(String, String)], e: SMTExpr) extends SMTCommand
private case class GetValue(args: Seq[(String, String)]) extends SMTCommand
