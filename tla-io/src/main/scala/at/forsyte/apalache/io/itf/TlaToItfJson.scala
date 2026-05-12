package at.forsyte.apalache.io.itf

import at.forsyte.apalache.io.json.{JsonRepresentation, ScalaToJsonAdapter}
import at.forsyte.apalache.io.lir.{NameReplacementMap, Trace}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper.deinterleave
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaFunOper, TlaSetOper, VariantOper}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}

import java.util.Calendar

/**
 * Converts TLA+ trace values to the Informal Trace Format JSON shape.
 *
 * @param adapter
 *   JSON representation adapter
 * @tparam T
 *   concrete JSON representation
 */
class TlaToItfJson[T <: JsonRepresentation](adapter: ScalaToJsonAdapter[T]) {

  /**
   * Produce a JSON representation of a counterexample in the ITF format.
   *
   * @param rootModule
   *   the module that produced the counterexample
   * @param states
   *   a sequence of next states
   * @return
   *   the JSON representation of the counterexample in the ITF format
   */
  def mkJson(rootModule: TlaModule, states: IndexedSeq[Trace.State]): T = {
    val state0 = states match {
      case constInit +: Seq()          => constInit
      case constInit +: initState +: _ => constInit ++ initState
      case Seq()                       => throw new IllegalArgumentException("Expected at least one state, found none")
    }
    val mappedStates = state0 +: states.drop(2)

    val metaFields = Seq(
        FORMAT_FIELD -> adapter.fromStr("ITF"),
        FORMAT_DESCRIPTION_FIELD -> adapter.fromStr("https://apalache-mc.org/docs/adr/015adr-trace.html"),
        DESCRIPTION_FIELD -> adapter.fromStr("Created by Apalache on %s".format(Calendar.getInstance().getTime)),
        VAR_TYPES_FIELD -> adapter.mkObj(rootModule.varDeclarations.map { varDecl =>
          varDecl.name -> adapter.fromStr(TlaType1.fromTypeTag(varDecl.typeTag).toString)
        }: _*),
    ) ++ Option.when(NameReplacementMap.store.nonEmpty)(
        VARIABLES_TO_EXPRESSIONS_FIELD -> adapter.mkObj(NameReplacementMap.store.toSeq.map { case (name, expression) =>
          name -> adapter.fromStr(expression)
        }: _*)
    )

    val rootFields =
      Seq(META_FIELD -> adapter.mkObj(metaFields: _*)) ++
        paramsToJson(rootModule).map(PARAMS_FIELD -> _).toSeq ++
        Seq(
            VARS_FIELD -> varsToJson(rootModule),
            STATES_FIELD -> adapter.fromIterable(mappedStates.zipWithIndex.map((stateToJson _).tupled)),
        )

    adapter.mkObj(rootFields: _*)
  }

  private def varsToJson(root: TlaModule): T = {
    val names = root.declarations.collect { case TlaVarDecl(name) =>
      adapter.fromStr(name)
    }
    adapter.fromIterable(names)
  }

  private def paramsToJson(root: TlaModule): Option[T] = {
    val names = root.declarations.collect { case TlaConstDecl(name) =>
      adapter.fromStr(name)
    }
    Option.when(names.nonEmpty)(adapter.fromIterable(names))
  }

  def stateToJson(state: Trace.State, index: Int): T = {
    val meta = adapter.mkObj(INDEX_FIELD -> adapter.fromInt(index))
    val fields = (META_FIELD -> meta) +: state.toList.sortBy(_._1).map { case (name, value) =>
      name -> exprToJson(value)
    }
    adapter.mkObj(fields: _*)
  }

  /**
   * Convert an individual TLA+ expression to its JSON representation in the ITF format.
   */
  def exprToJson(ex: TlaEx): T = ex match {
    case ValEx(TlaInt(num)) =>
      adapter.mkObj(BIG_INT_FIELD -> adapter.fromStr(num.toString(10)))

    case ValEx(TlaBool(b)) =>
      adapter.fromBool(b)

    case ValEx(TlaStr(str)) =>
      adapter.fromStr(str)

    case tuple @ OperEx(TlaFunOper.tuple, args @ _*) =>
      tuple.typeTag match {
        case Typed(SeqT1(_)) =>
          adapter.fromIterable(args.map(exprToJson))

        case _ =>
          adapter.mkObj(TUP_FIELD -> adapter.fromIterable(args.map(exprToJson)))
      }

    case OperEx(TlaSetOper.enumSet, args @ _*) =>
      adapter.mkObj(SET_FIELD -> adapter.fromIterable(args.map(exprToJson)))

    case OperEx(TlaFunOper.rec, args @ _*) =>
      val (keyEs, valueEs) = deinterleave(args)
      val keys = keyEs.collect { case ValEx(TlaStr(s)) => s }
      val values = valueEs.map(exprToJson)
      adapter.mkObj(keys.zip(values): _*)

    case OperEx(VariantOper.variant, ValEx(TlaStr(tagName)), valueEx) =>
      adapter.mkObj(TAG_FIELD -> adapter.fromStr(tagName), VALUE_FIELD -> exprToJson(valueEx))

    case OperEx(ApalacheOper.setAsFun, OperEx(TlaSetOper.enumSet, args @ _*)) =>
      val keyValueArrays = args.collect { case OperEx(TlaFunOper.tuple, key, value) =>
        adapter.fromIterable(Seq(exprToJson(key), exprToJson(value)))
      }
      adapter.mkObj(MAP_FIELD -> adapter.fromIterable(keyValueArrays))

    case e =>
      adapter.mkObj(UNSERIALIZABLE_FIELD -> adapter.fromStr(e.toString))
  }
}
