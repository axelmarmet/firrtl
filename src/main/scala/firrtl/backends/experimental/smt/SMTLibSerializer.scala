// SPDX-License-Identifier: Apache-2.0
// Author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package firrtl.backends.experimental.smt

import scala.util.matching.Regex

//horrible hack but quick
case class IndentLevel(var i: Int) {
  def getTabs   = "\t" * i;
  def increment = i += 1
  def decrement = i -= 1
}
object IndentLevel {
  implicit val defaultIndent = IndentLevel(0)
}

/** Converts STM Expressions to a SMTLib compatible string representation.
 *  See http://smtlib.cs.uiowa.edu/
 *  Assumes well typed expression, so it is advisable to run the TypeChecker
 *  before serializing!
 *  Automatically converts 1-bit vectors to bool.
 */
private object SMTLibSerializer {

  def setLogic(hasMem: Boolean) = "(set-logic QF_" + (if (hasMem) "A" else "") + "UFBV)"

  def serialize(e: SMTExpr): String = e match {
    case b: BVExpr    => serialize(b)
    case a: ArrayExpr => serialize(a)
  }

  def serializeType(e: SMTExpr): String = e match {
    case b: BVExpr    => serializeBitVectorType(b.width)
    case a: ArrayExpr => serializeArrayType(a.indexWidth, a.dataWidth)
  }

  private def serialize(e: BVExpr)(implicit indentLevel: IndentLevel): String = {

    def inner (e: BVExpr) : String = e match {
      case BVLiteral(value, width) =>
        val mask = (BigInt(1) << width) - 1
        val twosComplement = if (value < 0) {
          ((~(-value)) & mask) + 1
        } else value
        if (width == 1) {
          if (twosComplement == 1) "true" else "false"
        } else {
          s"(_ bv$twosComplement $width)"
        }
      case BVSymbol(name, _)                            => escapeIdentifier(name)
      case BVExtend(e, 0, _)                            => inner(e)
      case BVExtend(BVLiteral(value, width), by, false) => inner(BVLiteral(value, width + by))
      case BVExtend(e, by, signed) =>
        val foo = if (signed) "sign_extend" else "zero_extend"
        s"((_ $foo $by) ${asBitVector(e)})"
      case BVSlice(e, hi, lo) =>
        if (lo == 0 && hi == e.width - 1) {
          inner(e)
        } else {
          val bits = s"((_ extract $hi $lo) ${asBitVector(e)})"
          // 1-bit extracts need to be turned into a boolean
          if (lo == hi) {
            toBool(bits)
          } else {
            bits
          }
        }
      case BVNot(BVEqual(a, b)) if a.width == 1 => s"(distinct ${serialize(a)} ${serialize(b)})"
      case BVNot(BVNot(e))                      => inner(e)
      case BVNot(e) =>
        if (e.width == 1) {
          s"(not ${serialize(e)})"
        } else {
          s"(bvnot ${serialize(e)})"
        }
      case BVNegate(e)                                     => s"(bvneg ${asBitVector(e)})"
      case r: BVReduceAnd                                  => inner(Expander.expand(r))
      case r: BVReduceOr                                   => inner(Expander.expand(r))
      case r: BVReduceXor                                  => inner(Expander.expand(r))
      case BVImplies(BVLiteral(v, 1), b) if v == 1         => inner(b)
      case BVImplies(a, b)                                 => s"(=> ${serialize(a)} ${serialize(b)})"
      
      case BVEqual(a, BVLiteral(bigInt, 1)) if bigInt == 0 => s"(not ${serialize(a)})"
      case BVEqual(a, BVLiteral(bigInt, 1)) if bigInt == 1 => inner(a)
      case BVEqual(BVLiteral(bigInt, 1), b) if bigInt == 0 => s"(not ${serialize(b)})"
      case BVEqual(BVLiteral(bigInt, 1), b) if bigInt == 1 => inner(b)
      
      case BVEqual(a, b)                                   => s"(= ${serialize(a)} ${serialize(b)})"
      
      case ArrayEqual(a, b)                                => s"(= ${serialize(a)} ${serialize(b)})"
      case BVComparison(Compare.Greater, a, b, false)      => s"(bvugt ${asBitVector(a)} ${asBitVector(b)})"
      case BVComparison(Compare.GreaterEqual, a, b, false) => s"(bvuge ${asBitVector(a)} ${asBitVector(b)})"
      case BVComparison(Compare.Greater, a, b, true)       => s"(bvsgt ${asBitVector(a)} ${asBitVector(b)})"
      case BVComparison(Compare.GreaterEqual, a, b, true)  => s"(bvsge ${asBitVector(a)} ${asBitVector(b)})"
      // boolean operations get a special treatment for 1-bit vectors aka bools
      case BVOp(Op.And, BVLiteral(bigInt, 1), b) if bigInt == 1  => inner(b)
      case BVOp(Op.And, BVLiteral(bigInt, 1), b) if bigInt == 0  => "false"
      case BVOp(Op.And, a, BVLiteral(bigInt, 1)) if bigInt == 1  => inner(a)
      case BVOp(Op.And, a, BVLiteral(bigInt, 1)) if bigInt == 0  => "false"

      case BVOp(Op.And, a, b) if a.width == 1 => s"(and ${serialize(a)} ${serialize(b)})"
      case BVOp(Op.Or, a, b) if a.width == 1  => s"(or ${serialize(a)} ${serialize(b)})"
      case BVOp(Op.Xor, a, b) if a.width == 1 => s"(xor ${serialize(a)} ${serialize(b)})"
      case BVOp(op, a, b) if a.width == 1     => toBool(s"(${serialize(op)} ${asBitVector(a)} ${asBitVector(b)})")
      case BVOp(op, a, b)                     => s"(${serialize(op)} ${serialize(a)} ${serialize(b)})"
      case BVConcat(a, b)                     => s"(concat ${asBitVector(a)} ${asBitVector(b)})"
      case ArrayRead(array, index)            => s"(select ${serialize(array)} ${asBitVector(index)})"
      case BVIte(cond, tru, fals)             => s"(ite ${serialize(cond)} ${serialize(tru)} ${serialize(fals)})"
      case BVRawExpr(serialized, _, _)        => serialized
      case BVIn(e, delay) =>
        inner(e) // + s"; measure delay missing $delay\n"
    }

    indentLevel.increment
    val res = "\n" ++ indentLevel.getTabs ++ inner(e)
    indentLevel.decrement
    res
  }
  def serialize(e: ArrayExpr): String = e match {
    case ArraySymbol(name, _, _)           => escapeIdentifier(name)
    case ArrayStore(array, index, data)    => s"(store ${serialize(array)} ${serialize(index)} ${serialize(data)})"
    case ArrayIte(cond, tru, fals)         => s"(ite ${serialize(cond)} ${serialize(tru)} ${serialize(fals)})"
    case c @ ArrayConstant(e, _)           => s"((as const ${serializeArrayType(c.indexWidth, c.dataWidth)}) ${serialize(e)})"
    case ArrayRawExpr(serialized, _, _, _) => serialized
  }

  def serialize(c: SMTCommand): String = c match {
    case Comment(msg)                   => msg.split("\n").map("; " + _).mkString("\n")
    case DeclareUninterpretedSort(name) => s"(declare-sort ${escapeIdentifier(name)} 0)"
    case DefineFunction(name, args, e) =>
      val aa = args.map(a => s"(${escapeIdentifier(a._1)} ${a._2})").mkString(" ")
      s"(define-fun ${escapeIdentifier(name)} ($aa) ${serializeType(e)} ${serialize(e)})"
    case DeclareFunction(sym, tpes) =>
      val aa = tpes.mkString(" ")
      s"(declare-fun ${escapeIdentifier(sym.name)} ($aa) ${serializeType(sym)})"
    case Push =>
      s"(push ${"1"})"
    case Pop =>
      s"(pop ${"1"})"
    case CheckSat =>
      s"(check-sat)"
    case Assert(e) =>
      s"(assert ${serialize(e)})"
    case GetValue(args) =>
      val aa = args.map(a => s"(${escapeIdentifier(a._1)} ${a._2})").mkString(" ")
      s"(get-value ($aa))"
    case DeclareState(name, tpe) => 
      s"(declare-fun ${name} () $tpe)"
    case LineBreak => "\n";
    case Echo(msg) => s"""(echo "${msg}")"""
  }

  private def serializeArrayType(indexWidth: Int, dataWidth: Int): String =
    s"(Array ${serializeBitVectorType(indexWidth)} ${serializeBitVectorType(dataWidth)})"
  private def serializeBitVectorType(width: Int): String =
    if (width == 1) {
      "Bool"
    } else {
      assert(width > 1); s"(_ BitVec $width)"
    }

  private def serialize(op: Op.Value): String = op match {
    case Op.And                  => "bvand"
    case Op.Or                   => "bvor"
    case Op.Xor                  => "bvxor"
    case Op.ArithmeticShiftRight => "bvashr"
    case Op.ShiftRight           => "bvlshr"
    case Op.ShiftLeft            => "bvshl"
    case Op.Add                  => "bvadd"
    case Op.Mul                  => "bvmul"
    case Op.Sub                  => "bvsub"
    case Op.SignedDiv            => "bvsdiv"
    case Op.UnsignedDiv          => "bvudiv"
    case Op.SignedMod            => "bvsmod"
    case Op.SignedRem            => "bvsrem"
    case Op.UnsignedRem          => "bvurem"
  }

  private def toBool(e: String): String = s"(= $e (_ bv1 1))"

  private val bvZero = "(_ bv0 1)"
  private val bvOne  = "(_ bv1 1)"
  private def asBitVector(e: BVExpr): String =
    if (e.width > 1) {
      serialize(e)
    } else {
      s"(ite ${serialize(e)} $bvOne $bvZero)"
    }

  // See <simple_symbol> definition in the Concrete Syntax Appendix of the SMTLib Spec
  private val simple: Regex = raw"[a-zA-Z\+-/\*\=%\?!\.\$$_~&\^<>@][a-zA-Z0-9\+-/\*\=%\?!\.\$$_~&\^<>@]*".r
  def escapeIdentifier(name: String): String = name match {
    case simple() => name
    case _        => if (name.startsWith("|") && name.endsWith("|")) name else s"|$name|"
  }
}

/** Expands expressions that are not natively supported by SMTLib */
private object Expander {
  def expand(r: BVReduceAnd): BVExpr =
    if (r.e.width == 1) {
      r.e
    } else {
      val allOnes = (BigInt(1) << r.e.width) - 1
      BVEqual(r.e, BVLiteral(allOnes, r.e.width))
    }
  def expand(r: BVReduceOr): BVExpr =
    if (r.e.width == 1) {
      r.e
    } else {
      BVNot(BVEqual(r.e, BVLiteral(0, r.e.width)))
    }
  def expand(r: BVReduceXor): BVExpr =
    if (r.e.width == 1) {
      r.e
    } else {
      val bits = (0 until r.e.width).map(ii => BVSlice(r.e, ii, ii))
      bits.reduce[BVExpr]((a, b) => BVOp(Op.Xor, a, b))
    }
}
