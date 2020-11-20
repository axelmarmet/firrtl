package firrtl.transforms.formal

import firrtl._
import firrtl.ir._
import firrtl.graph._
import firrtl.options.Dependency
import firrtl.Mappers._
import firrtl.passes.MemPortUtils
import collection.mutable
import firrtl.Utils.{ kind, throwInternalError }
import firrtl.annotations.TargetToken.Ref

/** Convert Preconditions and Postconditions
 *
 * Module A
 *  inst module B
 * Module B
 *  require(P)
 *  ensure(Q)
 * Then we want to have
 * Module A
 *     assert(P)
 *     inst(Module B)
 *     assume(Q)
 * Module B
 *     assume(P)
 *     body
 *     assert(Q)
 */
object ConvertPrePostCondition extends Transform with DependencyAPIMigration {
  override def prerequisites          = Nil
  override def optionalPrerequisites  = Nil
  override def optionalPrerequisiteOf = Nil

  override def invalidates(a: Transform): Boolean = false

  def extract(m: DefModule, s: Statement, ioMapping: Map[String, Reference]): Seq[Statement] = {

    def liftStatement(statement: Statement): Statement = {

      def walkExpr(expr: Expression): Expression = expr.mapExpr(walkExpr) match {
        case Reference(name, tpe, kind, flow) if kind != PortKind => Reference(s"lifted_$name", tpe, kind, flow)
        case any                                                  => any
      }

      def walkStatement(stm: Statement): Statement = {
        def renameStatement(s: Statement): Statement = s match {
          case DefInstance(info, name, module, tpe) => DefInstance(info, s"lifted_$name", module, tpe)
          case DefMemory(
              info,
              name,
              dataType,
              depth,
              writeLatency,
              readLatency,
              readers,
              writers,
              readwriters,
              readUnderWrite
              ) =>
            DefMemory(
              info,
              s"lifted_$name",
              dataType,
              depth,
              writeLatency,
              readLatency,
              readers,
              writers,
              readwriters,
              readUnderWrite
            )
          case DefNode(info, name, value) => DefNode(info, s"lifted_$name", value)
          case DefRegister(info, name, tpe, clock, reset, init) =>
            DefRegister(info, s"lifted_$name", tpe, clock, reset, init)
          case DefWire(info, name, tpe) => DefWire(info, s"lifted_$name", tpe)
          case WDefInstanceConnector(info, name, module, tpe, portCons) =>
            WDefInstanceConnector(info, s"lifted_$name", module, tpe, portCons)
          case rest => rest
        }
        renameStatement(stm.mapStmt(walkStatement).mapExpr(walkExpr))
      }

      walkStatement(statement)
    }

    def getSubTree(statement: Statement): Seq[Statement] = {

      def getReferences(refs: mutable.ArrayBuffer[Reference])(expr: Expression): Unit = {
        expr.foreachExpr(getReferences(refs))
        expr match {
          case e: Reference => refs += e
          case _            => ()
        }
      }

      def walkStatement(refs: mutable.ArrayBuffer[Reference])(stm: Statement): Unit = {
        stm.foreachStmt(walkStatement(refs))
        stm.foreachExpr(getReferences(refs))
      }

      def followReference(ref: Reference): Option[Statement] = {
        //disgusting hack because there is only  map A => A and foreach
        var res: Option[Statement] = None
        def inner(stm: Statement): Unit =
          stm match {
            case DefInstance(_, name, _, _) if name == ref.name                 => res = Some(stm)
            case DefMemory(_, name, _, _, _, _, _, _, _, _) if name == ref.name => res = Some(stm)
            case DefNode(_, name, _) if name == ref.name                        => res = Some(stm)
            case DefRegister(_, name, _, _, _, _) if name == ref.name           => res = Some(stm)
            case DefWire(_, name, _) if name == ref.name                        => res = Some(stm)
            case _                                                              => stm.foreachStmt(inner)
          }
        m.foreachStmt(inner)
        res
      }

      val refs = mutable.ArrayBuffer.empty[Reference]
      walkStatement(refs)(statement)
      val subtrees = refs
        .map(followReference)
        .collect { case Some(x) => getSubTree(x) }
        .foldLeft(Seq[Statement]())(_ ++ _)
      subtrees :+ statement
    }

    def modifyReferences(expr: Statement): Statement = {
      def walkStatement(statement: Statement): Statement =
        statement.mapStmt(walkStatement).mapExpr(walkExpr)
      def walkExpr(expr: Expression): Expression =
        expr.mapExpr(walkExpr) match {
          case Reference(ioName, tpe, PortKind, flow) => ioMapping(ioName)
          case any                                    => any
        }
      expr.mapStmt(walkStatement).mapExpr(walkExpr)
    }

    getSubTree(s)
      .map(liftStatement)
      .map(modifyReferences)
  }

  def getIoMappings(body: Statement, moduleToLiftName: String): Map[String, Reference] = {

    def getAllStatements(statements : mutable.ArrayBuffer[Statement])(statement : Statement): Unit = {
        statements += statement
        statement.foreachStmt(getAllStatements(statements))
    }
    
    val collectedStatements = mutable.ArrayBuffer[Statement]()
    
    getAllStatements(collectedStatements)(body)

    println(body)
    println("in IO mappings, collectedStatments")
    collectedStatements.foreach(println)

    collectedStatements.collect {
      case Connect(info, SubField(Reference(`moduleToLiftName`, _, _, _), name, _, _), ref: Reference) =>
      name -> ref
      case Connect(info, ref: Reference, SubField(Reference(`moduleToLiftName`, _, _, _), name, _, _)) =>
      name -> ref
    }.toMap
}

  def discoverAndReplaceConditions(
    conditions: mutable.Map[String, List[Verification]]
  )(m: DefModule): DefModule = {
    def walkStatement(s: Statement): Statement =
      s match {
        case s @ Verification(op, info, clk, pred, en, msg) =>
          conditions(m.name) = s :: conditions.getOrElse(m.name, Nil)
          op match {
            case Formal.Require => Verification(Formal.Assume, info, clk, pred, en, msg)
            case Formal.Ensure  => Verification(Formal.Assert, info, clk, pred, en, msg)
            case _              => s
          }
        case _ =>
          s.mapStmt(walkStatement)
      }
    m.mapStmt(walkStatement)
  }

  def liftConditionsToParentModule(conditions: mutable.Map[String, List[Verification]], c : Circuit): Circuit = {
    def walkStatement(m : Module)(s: Statement): Statement =
      s match {
        case s @ DefInstance(info, instanceName, moduleName, tpe) =>
          if (conditions.contains(moduleName)) {

            val innerModule = c.modules.collectFirst{case m@Module(info, name, ports, body) if name == moduleName => m}.get
            val ioMappings = getIoMappings(m.body, instanceName)
            println("Iomappings")
            ioMappings.foreach(println)
            val relatedConditions = conditions(moduleName)
            val asserts: Seq[Statement] = relatedConditions
              .filter(_.op == Formal.Require)
              .map {
                case Verification(_, info, clk, pred, en, msg) => Verification(Formal.Assert, info, clk, pred, en, msg)
              }
              .map (extract(innerModule, _, ioMappings))
              .reduce(_ ++ _)
              .toSeq
            val assumes: Seq[Statement] = relatedConditions
              .filter(_.op == Formal.Ensure)
              .map {
                case Verification(_, info, clk, pred, en, msg) => Verification(Formal.Assume, info, clk, pred, en, msg)
              }
              .map (extract(innerModule, _, ioMappings))
              .reduce(_ ++ _)
              .toSeq
            Block((assumes :+ s) ++ asserts)
          } else {
            s
          }
        case _ => s.mapStmt(walkStatement(m))
      }
    c.mapModule{
        case m@Module(info, name, ports, body) => m.mapStmt(walkStatement(m))
    }
  }

  def execute(state: CircuitState): CircuitState = {
    val map = mutable.Map[String, List[Verification]]()
    val circuit = state.circuit
        .mapModule(discoverAndReplaceConditions(map))
    val otherCircuit = liftConditionsToParentModule(map, circuit)
    state.copy(
      circuit = otherCircuit
    )
  }
}
