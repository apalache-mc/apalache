package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper.deinterleave
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaFunOper, TlaSetOper, VariantOper}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}

import java.io.PrintWriter
import java.util.Calendar
import scala.collection.immutable.Map
import scala.collection.mutable

/**
 * This class produces counterexamples in the Informal Trace Format.
 *
 * @param writer
 *   a print writer to use
 * @author
 *   Igor Konnov
 */
class ItfCounterexampleWriter(writer: PrintWriter) extends CounterexampleWriter {
  override def write(cx: Counterexample): Unit = {
    writer.write(ujson.write(ItfCounterexampleWriter.mkJson(cx), indent = 2))
  }
}

object ItfCounterexampleWriter {

  /**
   * The minimal value that can be reliably represented with Double in JavaScript.
   */
  val MIN_JS_INT: BigInt = -BigInt(2).pow(53) + 1

  /**
   * The maximal value that can be reliably represented with Double in JavaScript.
   */
  val MAX_JS_INT: BigInt = BigInt(2).pow(53) - 1

  /**
   * Produce a JSON representation of a counterexample in the ITF format
   *
   * @param rootModule
   *   the module that produced the counterexample
   * @param states
   *   a sequence of next states
   * @return
   *   the JSON representation of the counterexample in the ITF format
   */
  def mkJson(cx: Counterexample): ujson.Value = {
    // merge constant initialization and variable initialization into a single state, and
    // take just the state maps, dropping the indexes, from the remaining states
    val states = cx.states match {
      case (constInit, _) :: Nil                    => List(constInit)
      case (constInit, _) :: (initState, _) :: rest => (constInit ++ initState :: rest.map(_._1))
      case Nil => throw new IllegalArgumentException("Expected at least one state, found none")
    }

    val rootMap: mutable.LinkedHashMap[String, ujson.Value] = mutable.LinkedHashMap()

    val metaInformation: Map[String, ujson.Value] = {
      val descriptions = Map[String, ujson.Value](
          "format-description" -> "https://apalache.informal.systems/docs/adr/015adr-trace.html",
          "description" -> "Created by Apalache on %s".format(Calendar.getInstance().getTime),
      )

      (if (NameReplacementMap.store.isEmpty)
         descriptions
       else
         descriptions ++
           Map("variables-to-expressions" -> NameReplacementMap.store))
    }

    rootMap.put("#meta",
        ujson.Obj(
            "format" -> "ITF",
            metaInformation.toSeq: _*
        ))
    paramsToJson(cx.module).foreach(params => rootMap.put("params", params))
    rootMap.put("vars", varsToJson(cx.module))
    rootMap.put("states", ujson.Arr(states.zipWithIndex.map((stateToJson _).tupled): _*))
    ujson.Obj(rootMap)
  }

  private def varsToJson(root: TlaModule): ujson.Value = {
    val names = root.declarations.collect { case TlaVarDecl(name) =>
      ujson.Str(name)
    }
    ujson.Arr(names: _*)
  }

  private def paramsToJson(root: TlaModule): Option[ujson.Value] = {
    val names = root.declarations.collect { case TlaConstDecl(name) =>
      ujson.Str(name)
    }
    if (names.isEmpty) None else Some(ujson.Arr(names: _*))
  }

  private def stateToJson(state: Map[String, TlaEx], index: Int): ujson.Value = {
    val meta = ujson.Obj("index" -> ujson.Num(index))
    val map = state.toList.sortBy(_._1).map(p => (p._1, exToJson(p._2)))
    ujson.Obj("#meta" -> meta, map: _*)
  }

  private def exToJson: TlaEx => ujson.Value = {
    case ValEx(TlaInt(num)) =>
      if (num >= MIN_JS_INT && num <= MAX_JS_INT) {
        ujson.Num(num.toDouble)
      } else {
        ujson.Obj("#bigint" -> ujson.Str(num.toString(10)))
      }

    case ValEx(TlaBool(b)) =>
      ujson.Bool(b)

    case ValEx(TlaStr(str)) =>
      ujson.Str(str)

    case ex @ OperEx(TlaFunOper.tuple, args @ _*) =>
      ex.typeTag match {
        case Typed(SeqT1(_)) =>
          ujson.Arr(args.map(exToJson): _*)

        case _ =>
          ujson.Obj("#tup" -> ujson.Arr(args.map(exToJson): _*))
      }

    case OperEx(TlaSetOper.enumSet, args @ _*) =>
      ujson.Obj("#set" -> ujson.Arr(args.map(exToJson): _*))

    case OperEx(TlaFunOper.rec, args @ _*) =>
      val (keyEs, valuesEs) = deinterleave(args)
      val keys = keyEs.collect { case ValEx(TlaStr(s)) => s }
      val values = valuesEs.map(exToJson)
      ujson.Obj(mutable.LinkedHashMap(keys.zip(values): _*))

    case OperEx(VariantOper.variant, ValEx(TlaStr(tagName)), valueEx) =>
      ujson.Obj(mutable.LinkedHashMap("tag" -> ujson.Str(tagName), "value" -> exToJson(valueEx)))

    case OperEx(ApalacheOper.setAsFun, OperEx(TlaSetOper.enumSet, args @ _*)) =>
      val keyValueArrays = args.collect { case OperEx(TlaFunOper.tuple, key, value) =>
        ujson.Arr(exToJson(key), exToJson(value))
      }
      ujson.Obj("#map" -> ujson.Arr(keyValueArrays: _*))

    case e =>
      // We don't know how to serialize this TLA+ expression (e.g., Int, Nat, FunSet, PowSet).
      // Output it as a serialization error.
      ujson.Obj("#unserializable" -> ujson.Str(e.toString))
  }
}
