// SPDX-License-Identifier: Apache-2.0
// Author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package firrtl.backends.experimental.smt

import scala.collection.mutable
import java.io.PushbackInputStream
import SMTTactics._

/** This Transition System encoding is directly inspired by yosys' SMT backend:
 * https://github.com/YosysHQ/yosys/blob/master/backends/smt2/smt2.cc
 * It if fairly compact, but unfortunately, the use of an uninterpreted sort for the state
 * prevents this encoding from working with boolector.
 * For simplicity reasons, we do not support hierarchical designs (no `_h` function).
 */
object SMTTransitionSystemEncoder {

  def measurementDelay(e: SMTExpr)(implicit measurementDelaysSymbol : mutable.Map[SMTSymbol, Int]): Int = e match {
    case e: SMTSymbol    => measurementDelaysSymbol(e)
    case _: BVLiteral    => 0
    case e: BVRawExpr    => measurementDelaysSymbol(e.initSymbol)
    case e: ArrayRawExpr => measurementDelaysSymbol(e.initSymbol)
    case BVIn(e, delay)  => measurementDelay(e) + delay
    case e               => e.children.map(measurementDelay).max
  }

  // All signals are modelled with functions that need to be called with the state as argument,
  // this replaces all Symbols with function applications to the state.
  def replaceSymbols(e: SMTExpr)(implicit measurementDelaysSymbol : mutable.Map[SMTSymbol, Int]): SMTExpr = e match {
    case BVIn(expr, delay) =>
      symbolToFunApp(expr, SignalSuffix, (delay to measurementDelay(e)).map(i => s"${State}_${i}").mkString(" "))
    case _ =>
      SMTExprVisitor.map(
        expr =>
          symbolToFunApp(expr, SignalSuffix, (0 to measurementDelay(expr)).map(i => s"${State}_${i}").mkString(" "))
      )(e)
  }

  def symbolToFunApp(sym: SMTExpr, suffix: String, arg: String): SMTExpr = sym match {
    case sym @ BVSymbol(name, width) =>
      BVRawExpr(s"(${id(name + suffix)} $arg)", width, sym)
    case sym @ ArraySymbol(name, indexWidth, dataWidth) =>
      ArrayRawExpr(s"(${id(name + suffix)} $arg)", indexWidth, dataWidth, sym)
    case other => other
  }

  def encode(sys: TransitionSystem): Iterable[SMTCommand] = {
    val cmds                    = mutable.ArrayBuffer[SMTCommand]()
    val name                    = sys.name
    val measurementDelaysSymbol = mutable.Map[SMTSymbol, Int]()

    // {
    //   println(s"Replacing $e")
    //   SMTExprVisitor.map(expr => {
    //     expr match {
    //         case BVIn(_, delay) =>

    //         case _ =>
    //           symbolToFunApp(expr, SignalSuffix,
    //             (0 to measurementDelay(expr)).map(i => s"${State}_${i}").mkString(" "))
    //     }
    //   })(e)
    // }

    // emit header as comments
    cmds ++= sys.header.map(Comment)

    // declare state type
    val stateType = id(name + "_s")
    cmds += DeclareUninterpretedSort(stateType)

    // inputs and states are modelled as constants
    def declare(sym: SMTSymbol, kind: String): Unit = {
      cmds ++= toDescription(sym, kind, sys.comments.get)
      val s = SMTSymbol.fromExpr(sym.name + SignalSuffix, sym)
      measurementDelaysSymbol += sym -> 0
      cmds += DeclareFunction(s, List(stateType))
    }
    sys.inputs.foreach(i => declare(i, "input"))
    sys.states.foreach(s => declare(s.sym, "register"))

    // signals are just functions of other signals, inputs and state
    def define(sym: SMTSymbol, e: SMTExpr, suffix: String = SignalSuffix): Unit = {
      val delay     = measurementDelay(e)(measurementDelaysSymbol)
      val replacedE = replaceSymbols(e)(measurementDelaysSymbol)
      measurementDelaysSymbol += sym -> delay
      val args = (0 to (delay)).toList.map(i => (s"${State}_${i}", stateType))
      cmds += DefineFunction(sym.name + suffix, args, replacedE)
    }
    
    sys.signals.foreach { signal =>
      val kind = if (sys.outputs.contains(signal.name)) {
        "output"
      } else if (sys.assumes.contains(signal.name)) {
        "assume"
      } else if (sys.asserts.contains(signal.name)) {
        "assert"
      } else {
        "wire"
      }
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

    def defineConjunction(e: Iterable[BVExpr], suffix: String): Unit =
      define(BVSymbol(name, 1), andReduce(e), suffix)

    // the transition relation asserts that the value of the next state is the next value from the previous state
    // e.g., (reg state_n) == (reg_next state)
    val transitionRelations = sys.states.map { state =>
      val newState     = symbolToFunApp(state.sym, SignalSuffix, StateNext)
      val nextOldState = symbolToFunApp(state.sym, NextSuffix, State)
      SMTEqual(newState, nextOldState)
    }
    // the transition relation is over two states
    val transitionExpr = andReduce(transitionRelations)
    cmds += Comment(
      """This function evaluates to ’true’ if the states ’state’ and
’next_state’ form a valid state transition.""""
    )
    cmds += DefineFunction(name + "_t", List((State, stateType), (StateNext, stateType)), transitionExpr)

    // The init relation just asserts that all init function hold
    val initRelations = sys.states.filter(_.init.isDefined).map { state =>
      val stateSignal = symbolToFunApp(state.sym, SignalSuffix, State)
      val initSignal  = symbolToFunApp(state.sym, InitSuffix, State)
      SMTEqual(stateSignal, initSignal)
    }

    cmds += Comment("""This function must be asserted ’true’ for initial states. For
non-initial states it must be left unconstrained.""")
    defineConjunction(initRelations, "_i")

    // assertions and assumptions
    val assertions =
      sys.signals.filter(a => sys.asserts.contains(a.name)).map(a => replaceSymbols(a.toSymbol)(measurementDelaysSymbol).asInstanceOf[BVRawExpr])
    cmds += Comment("""This function evaluates to ’true’ if all assertions hold in the state.""")
    defineConjunction(assertions, "_a")
    val assumptions =
      sys.signals.filter(a => sys.assumes.contains(a.name)).map(a => replaceSymbols(a.toSymbol)(measurementDelaysSymbol).asInstanceOf[BVExpr])
    cmds += Comment("""This function evaluates to ’true’ if all assumptions hold in the state.""")
    defineConjunction(assumptions, "_u")

    // For all assertions (assumptions?) check for a methodology and apply it if present.
    val assertCmds:List[SMTCommand] = sys.signals
      .filter(a => sys.asserts.contains(a.name)).toList
      .flatMap(s => SMTTactics.dispatch(sys, measurementDelay(s.e)(measurementDelaysSymbol))(s))

    cmds ++= assertCmds
    cmds
  }

  def id(s: String): String = SMTLibSerializer.escapeIdentifier(s)
  val State                 = "state"
  val StateNext             = "state_n"
  val SignalSuffix          = "_f"
  val NextSuffix            = "_next"
  val InitSuffix            = "_init"
  def toDescription(sym: SMTSymbol, kind: String, comments: String => Option[String]): List[Comment] =
    List(sym match {
      case BVSymbol(name, width) =>
        Comment(s"firrtl-smt2-$kind $name $width")
      case ArraySymbol(name, indexWidth, dataWidth) =>
        Comment(s"firrtl-smt2-$kind $name $indexWidth $dataWidth")
    }) ++ comments(sym.name).map(Comment)

  private def andReduce(e: Iterable[BVExpr]): BVExpr =
    if (e.isEmpty) BVLiteral(1, 1) else e.reduce((a, b) => BVOp(Op.And, a, b))
}

/** minimal set of pseudo SMT commands needed for our encoding */
sealed trait SMTCommand
case class Comment(msg: String)                                                  extends SMTCommand
case class DefineFunction(name: String, args: Seq[(String, String)], e: SMTExpr) extends SMTCommand
case class DeclareFunction(sym: SMTSymbol, tpes: Seq[String])                    extends SMTCommand
case class DeclareUninterpretedSort(name: String)                                extends SMTCommand
case object Push                                                                 extends SMTCommand
case object Pop                                                                  extends SMTCommand
case class GetValue(args: Seq[(String, String)])                                 extends SMTCommand
case class DeclareState(name: String, tpe: String)                               extends SMTCommand
case class Assert(e: SMTExpr)                                                    extends SMTCommand
case object CheckSat                                                             extends SMTCommand
case object LineBreak                                                            extends SMTCommand
case class Echo(msg: String)                                                     extends SMTCommand
