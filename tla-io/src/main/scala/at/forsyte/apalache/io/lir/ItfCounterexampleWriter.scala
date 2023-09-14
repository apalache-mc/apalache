package at.forsyte.apalache.io.lir

import at.forsyte.apalache.io.itf._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper.deinterleave
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaFunOper, TlaSetOper, VariantOper}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}

import java.io.PrintWriter
import java.util.Calendar
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
  override def write(rootModule: TlaModule, notInvariant: NotInvariant, states: List[NextState]): Unit = {
    writer.write(ujson.write(ItfCounterexampleWriter.mkJson(rootModule, states), indent = 2))
  }
}

object ItfCounterexampleWriter {

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
  def mkJson(rootModule: TlaModule, states: List[NextState]): ujson.Value = {
    // merge constant initialization and variable initialization into a single state
    val state0 = states match {
      case constInit :: Nil            => constInit._2
      case constInit :: initState :: _ => constInit._2 ++ initState._2
      case Nil                         => throw new IllegalArgumentException("Expected at least one state, found none")
    }
    val mappedStates = state0 :: states.drop(2).map(_._2)
    // construct the root JSON object
    val rootMap: mutable.LinkedHashMap[String, ujson.Value] = mutable.LinkedHashMap()

    val metaInformation: Map[String, ujson.Value] = {
      val varTypes = Map[String, ujson.Value](
          VAR_TYPES_FIELD -> ujson.Obj.from(
              rootModule.varDeclarations.map { varDecl =>
                varDecl.name -> TlaType1.fromTypeTag(varDecl.typeTag).toString
              }
          )
      )
      val descriptions = Map[String, ujson.Value](
          FORMAT_DESCRIPTION_FIELD -> "https://apalache.informal.systems/docs/adr/015adr-trace.html",
          DESCRIPTION_FIELD -> "Created by Apalache on %s".format(Calendar.getInstance().getTime),
      )

      varTypes ++ descriptions ++
        Option.when(NameReplacementMap.store.nonEmpty)(VARIABLES_TO_EXPRESSIONS_FIELD -> NameReplacementMap.store)
    }

    rootMap.put(META_FIELD,
        ujson.Obj(
            FORMAT_FIELD -> "ITF",
            metaInformation.toSeq: _*
        ))
    paramsToJson(rootModule).foreach(params => rootMap.put(PARAMS_FIELD, params))
    rootMap.put(VARS_FIELD, varsToJson(rootModule))
    rootMap.put(STATES_FIELD, ujson.Arr(mappedStates.zipWithIndex.map((stateToJson _).tupled): _*))
    ujson.Obj.from(rootMap)
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
    val meta = ujson.Obj(INDEX_FIELD -> ujson.Num(index))
    val map = state.toList.sortBy(_._1).map(p => (p._1, exToJson(p._2)))
    ujson.Obj(META_FIELD -> meta, map: _*)
  }

  private def exToJson: TlaEx => ujson.Value = {
    case ValEx(TlaInt(num)) =>
      ujson.Obj(BIG_INT_FIELD -> ujson.Str(num.toString(10)))

    case ValEx(TlaBool(b)) =>
      ujson.Bool(b)

    case ValEx(TlaStr(str)) =>
      ujson.Str(str)

    case ex @ OperEx(TlaFunOper.tuple, args @ _*) =>
      ex.typeTag match {
        case Typed(SeqT1(_)) =>
          ujson.Arr(args.map(exToJson): _*)

        case _ =>
          ujson.Obj(TUP_FIELD -> ujson.Arr(args.map(exToJson): _*))
      }

    case OperEx(TlaSetOper.enumSet, args @ _*) =>
      ujson.Obj(SET_FIELD -> ujson.Arr(args.map(exToJson): _*))

    case OperEx(TlaFunOper.rec, args @ _*) =>
      val (keyEs, valuesEs) = deinterleave(args)
      val keys = keyEs.collect { case ValEx(TlaStr(s)) => s }
      val values = valuesEs.map(exToJson)
      ujson.Obj.from(keys.zip(values))

    case OperEx(VariantOper.variant, ValEx(TlaStr(tagName)), valueEx) =>
      ujson.Obj(TAG_FIELD -> ujson.Str(tagName), VALUE_FIELD -> exToJson(valueEx))

    case OperEx(ApalacheOper.setAsFun, OperEx(TlaSetOper.enumSet, args @ _*)) =>
      val keyValueArrays = args.collect { case OperEx(TlaFunOper.tuple, key, value) =>
        ujson.Arr(exToJson(key), exToJson(value))
      }
      ujson.Obj(MAP_FIELD -> ujson.Arr(keyValueArrays: _*))

    case e =>
      // We don't know how to serialize this TLA+ expression (e.g., Int, Nat, FunSet, PowSet).
      // Output it as a serialization error.
      ujson.Obj(UNSERIALIZABLE_FIELD -> ujson.Str(e.toString))
  }
}
