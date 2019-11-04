// See LICENSE for license details.

package reporters

import firrtl.{Transform, LowForm, CircuitState, Utils, WRef, WSubField, WDefInstance, RegKind}
import firrtl.ir.{Circuit, Module, DefModule, DefRegister, Statement, Expression, Mux, UIntLiteral, SIntLiteral, DoPrim, UIntType, SIntType, IntWidth, Connect, Block, EmptyStmt, IsInvalid, Field, DefNode, DefWire, DefMemory, Stop, Print, Type}
import firrtl.Mappers._

import scala.collection.mutable
import scala.math.Ordering.Implicits._


import spray.json._
import DefaultJsonProtocol._
import java.io._

import firrtl.annotations.NoTargetAnnotation

case class AreaAnnotation( val area : Int) extends NoTargetAnnotation {
  def value: String = s"${area}"
}

case class PowerAnnotation(val name : String, val opType : String, val tpe : Type) extends NoTargetAnnotation

class Ledger {

  private var moduleName: Option[String] = None

  private val moduleOpMap = mutable.Map[String,mutable.Map[Area,Int]]()

  private val moduleOpInputsMap = mutable.Map[String,mutable.ListBuffer[PowerAnnotation]]()

  def foundOp( a : Area): Unit = {
    val innerMap = moduleOpMap(getModuleName)
    innerMap(a) = innerMap.getOrElse( a, 0) + 1
  }

  private def getExprName(e: Expression): String = {
    e match {
      case WRef(name, _, _, _) => name
      case _ => "ERROR"
    }
  }

  def registerPowerSignal(name: String, opType: String, tpe: Type): Unit = {
    if (!moduleOpInputsMap.contains(getModuleName)) moduleOpInputsMap += (getModuleName -> mutable.ListBuffer[PowerAnnotation]())
    val innerInputsMap = moduleOpInputsMap(getModuleName)
    innerInputsMap += PowerAnnotation(name, opType, tpe)
  }

  def getModuleName: String = moduleName match {
    case None => Utils.error("Module name not defined in Ledger!")
    case Some(name) => name
  }
  def setModuleName(myName: String): Unit = {
    moduleOpMap(myName) = moduleOpMap.getOrElse( myName, mutable.Map())
    moduleName = Some(myName)
  }
  def report() : Int = {
    val arcs = for { (tgt,m) <- moduleOpMap
                     (AreaModule(src,_),_) <- m
    } yield (src,tgt)

    val tbl = mutable.Map[String,Int]()
    val ts = TopoSort( moduleOpMap.keys.toSeq, arcs.toSeq)
    for{ nm <- ts} {
      val area = ComputeArea(moduleOpMap(nm),tbl)
      val areas = for{ (k,v) <- moduleOpMap(nm)} yield (s"$k", v, ComputeArea(k,tbl)) // (k,v) is the pair of module and count

      val sortedAreas = areas.toList.sortWith{ case (x,y) => (-x._2*x._3,x._1) < (-y._2*y._3,y._1)}

      var cumulative : Int = 0

      println( f"${nm}%-30s     Area    Count         Total      Cumulative")
      println( f"-------------------------------    ----    -----     -------------  ----------")
      for{ (k,v,larea) <- sortedAreas} {
        val total = larea*v
        cumulative += total
        println( f"${k}%-30s ${larea}%8d ${v}%8d ${total}%9d ${total*100.0/area}%6.1f%%   ${cumulative*100.0/area}%8.1f%%")
      }
      println( f"-------------------------------    ----    -----     -------------  ----------")
      println( f"Sum                                              ${area}%9d")
      println( f"==============================================================================")

      tbl(nm) = area
    }
    tbl(ts.last)
  }

  def reportJson( circuit : Circuit, fn : String) : Unit = {

    val tbl = mutable.Map[String,Int]()

    def aux( nm : String, instanceName : String) : JsObject = {

      val children = mutable.ArrayBuffer[(String,String)]()
      val objs = mutable.ArrayBuffer[JsObject]()

      for{ (k,v) <- moduleOpMap(nm)} {
        k match {
          case AreaModule( templateName, instanceName) => children.append( (templateName, instanceName))
          case a => objs.append( JsObject( "name" -> JsString(s"$a $v"), "size" -> JsNumber(v*ComputeArea( a, tbl))))
        }
      }

      val seq = for ( (child,childInstanceName) <- children) yield {
        aux( child, childInstanceName)
      }

      JsObject( "name" -> JsString(instanceName), "children" -> JsArray( (objs ++ seq) : _*))
    }

    val jsonAST = aux( circuit.main, "top")

    val fp = new File( fn)
    val bw = new BufferedWriter(new FileWriter( fp))
    bw.write( jsonAST.prettyPrint)
    bw.close()

  }

  def getmoduleOpMap : mutable.Map[String,mutable.Map[Area,Int]] = moduleOpMap

  def getmoduleOpInputsMap : mutable.Map[String,mutable.ListBuffer[PowerAnnotation]] = moduleOpInputsMap

}

class ReportArea extends Transform {

  def extractWidth( x : Any) : Int = x match {
    case UIntType(IntWidth(w)) => w.toInt
    case SIntType(IntWidth(w)) => w.toInt
    case _ => -1
  }

  def isConst( x : Any) : Int = x match {
    case _ : UIntLiteral => 1
    case _ : SIntLiteral => 1
    case _ => 0
  }

  def inputForm = LowForm
  def outputForm = LowForm

  def execute(state: CircuitState): CircuitState = {
    val ledger = new Ledger()
    val circuit = state.circuit
    circuit map walkModule(ledger)
    val area = ledger.report
    ledger.reportJson( circuit, "areas.json")

    state.copy( annotations = state.annotations ++ Seq(AreaAnnotation( area)))
  }

  def moduleOpInputsMap(circuit: Circuit): mutable.Map[String, mutable.ListBuffer[PowerAnnotation]] = {
    val ledger = new Ledger()
    circuit map walkModule(ledger)
    val area = ledger.report
    ledger.getmoduleOpInputsMap
  }

  def walkModule(ledger: Ledger)(m: DefModule): DefModule = {
    ledger.setModuleName(m.name)
    m.ports.foreach(x => println(s"Found ${x.direction} Port ${x.name} of type ${x.tpe}"))
    m map walkStatement(ledger)
    m
  }

  def walkStatement(ledger: Ledger)(s: Statement): Statement = {
    s map walkExpression(ledger) map walkStatement(ledger)
    s match {
      case WDefInstance( info, instanceName, templateName, _) =>
        ledger.foundOp( AreaModule( s"$templateName", s"$instanceName"))
        println(s"Found WDefInstance ${instanceName}")
      case DefRegister( info, lhs, tpe, clock, reset, init) =>
        ledger.foundOp( AreaRegister( extractWidth( tpe)))
        ledger.registerPowerSignal(lhs, "reg", tpe)
      case DefMemory( info, nm, tpe, sz, wrLat, rdLat, readers, writers, readWriters, _) =>
        ledger.foundOp( AreaMemory( extractWidth( tpe), sz.toInt, readers.length, writers.length, readWriters.length))
        println(s"Found DefMemory ${nm}")
      case _ : Block => ()
      case DefNode(_, name, expr) => 
        ledger.registerPowerSignal(name, getOpName(expr), expr.tpe)
      case DefWire(_, name, _) => println(s"Found DefWire ${name}")
      case Connect(_, loc, expr) => loc match {
        case WRef(name, _, kind, _) => {
          if (kind == RegKind) ledger.registerPowerSignal(name + "/in", getOpName(expr), expr.tpe)
          else ledger.registerPowerSignal(name, getOpName(expr), expr.tpe)
        }
        case _ => println("Unimplemented Connect")
      }
      case _ : Print => ()
      case _ : Stop => ()
      case EmptyStmt => () // EmptyStmt is an object
      case _ => 
        println( s"Missed this statement: $s")
        ()
    }
    s
  }

  def walkExpression(ledger: Ledger)(e: Expression): Expression = {
    e map walkExpression(ledger)
    e match {
      case Mux(cond, tval, fval, tpe) => 
        ledger.foundOp( AreaMux( extractWidth(tpe), isConst(cond), isConst(tval)+isConst(fval)))
      case DoPrim( op, inps, _, tpe) =>

        val inpSizes : List[Int] = inps.map{
          case WRef( _, inpTpe, _, _) => extractWidth(inpTpe)
          case UIntLiteral( _, IntWidth( w)) => w.toInt
          case SIntLiteral( _, IntWidth( w)) => w.toInt
          case DoPrim( _, _, _, inpTpe) => extractWidth(inpTpe)
          case WSubField( expr, nm, inpTpe, gndr) =>
            extractWidth(inpTpe)
          case x =>
            println( s"inputSizes: Unimplemented match ${x}")
            0
        }.toList

        val c = inps.foldLeft( 0){ case (l,r) => l + isConst(r)}
        ledger.foundOp( AreaOp( s"${op}", inpSizes, extractWidth(tpe), c))
      case _ => ()
    }
    e
  }

  private def getOpName(e: Expression): String = {
    e match {
      case WRef(name, _, _, _) => name
      case DoPrim(op, _, _, _) => op.serialize
      case _ => "ERROR"
    }
  }

}

