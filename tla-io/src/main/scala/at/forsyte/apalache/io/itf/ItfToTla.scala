package at.forsyte.apalache.io.itf

import at.forsyte.apalache.io.itf.ItfToTla._
import at.forsyte.apalache.io.json.{JsonDeserializationError, JsonRepresentation, ScalaFactory}
import at.forsyte.apalache.io.lir.Trace
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.{tla, ModelValueHandler}

/**
 * Reads a sequence of States, i.e. mappings from variable names to TlaEx values, from an ITF json.
 *
 * @tparam T
 *   Any class extending JsonRepresentation
 * @author
 *   Jure Kukovec
 */
class ItfToTla[T <: JsonRepresentation](
    scalaFactory: ScalaFactory[T]) {

  /**
   * Checks that the Apalache-specific ITF requirements are met, as defined in ADR15. If yes, returns a mapping from
   * variables to their types.
   */
  private[itf] def validateShapeAndGetTypes(json: T): Map[String, TlaType1] = {
    val varTypesOpt = for {
      meta <- json.getFieldOpt(META_FIELD)
      varTypes <- meta.getFieldOpt(VAR_TYPES_FIELD)
    } yield varTypes
    val varTypesJson = varTypesOpt.getOrElse {
      throw new JsonDeserializationError("ITF JSON does not satisfy Apalache requirements. " +
        "Toplevel \"#meta\" field must exist and contain \"varTypes\". " +
        "See ADR15: https://apalache.informal.systems/docs/adr/015adr-trace.html#itf-as-input-to-apalache. ")
    }

    val diffOpt = for {
      vars <- json.getFieldOpt(VARS_FIELD)
      varTypesKeys <- varTypesJson.allFieldsOpt
    } yield {
      val varsSet = scalaFactory.asSeq(vars).map { scalaFactory.asStr }.toSet
      // Symmetric difference
      (varsSet -- varTypesKeys) ++ (varTypesKeys -- varsSet)
    }

    val diff = diffOpt.getOrElse {
      throw new JsonDeserializationError(s"\"$VARS_FIELD\" or \"$VAR_TYPES_FIELD\" contents are malformed.")
    }
    if (diff.nonEmpty)
      throw new JsonDeserializationError(s"\"$VARS_FIELD\" and \"$VAR_TYPES_FIELD\" define different states. " +
        s"Variable(s) ${diff.toSeq.mkString(", ")} present in exactly one of the two fields.")

    varTypesJson.allFieldsOpt.get.map { k =>
      k -> DefaultType1Parser.parseType(scalaFactory.asStr(varTypesJson.getFieldOpt(k).get))
    }.toMap
  }

  /**
   * Some values, like the predefined sets (Int, Nat, etc.) are encoded as "UNSERIALIZABLE_FIELD": `<value>` Currently,
   * per our discussions, we disallow the use of this tag, but the function can be extended in the future.
   *
   * E.g. we could return Some(tla.intSet()) on str = "Int".
   */
  private[itf] def attemptUnserializable(json: T): Option[TBuilderInstruction] =
    if (json.allFieldsOpt.contains(Set(UNSERIALIZABLE_FIELD))) {
      val str = scalaFactory.asStr(json.getFieldOpt(UNSERIALIZABLE_FIELD).get)
      throw new JsonDeserializationError(s"Unserializable value $str is disallowed.")
    } else None

  // Note: attemptUnserializable + getOrElse is future-proof, and allows us to eventually case-match
  // unserializable values.

  private[itf] def typeDrivenBuild(json: T, tt1: TlaType1): TBuilderInstruction =
    attemptUnserializable(json).getOrElse {
      tt1 match {
        case BoolT1 =>
          tla.bool(scalaFactory.asBool(json))
        case StrT1 =>
          val s = scalaFactory.asStr(json)
          if (ModelValueHandler.isModelValue(s))
            throw new JsonDeserializationError(
                s"$s is annotated as a string, but has the value of an uninterpreted literal.")
          tla.str(s)
        case ct: ConstT1 =>
          val raw = scalaFactory.asStr(json)
          // ConstT1-type literals must adhere to the pattern regex
          val typeIndexOpt = ModelValueHandler.typeAndIndex(raw)
          val (constT, idx) = typeIndexOpt.getOrElse {
            throw new JsonDeserializationError(s"$raw is annotated as an uninterpreted literal, but has string form.")
          }
          // The pattern-suffix must also match the declared type
          if (ct != constT) {
            throw new JsonDeserializationError(s"$raw is annotated as $ct but has a $constT value.")
          }
          tla.const(idx, constT)
        case IntT1 =>
          // Big integers are written as strings, not JS integers
          if (json.allFieldsOpt.contains(Set(BIG_INT_FIELD))) {
            val biString = scalaFactory.asStr(json.getFieldOpt(BIG_INT_FIELD).get)
            tla.int(BigInt(biString))
          } else tla.int(scalaFactory.asInt(json))

        case SeqT1(elemT) =>
          val elems = scalaFactory.asSeq(json)
          val args = elems.map { typeDrivenBuild(_, elemT) }
          // Empty collections have special builder ctors
          if (args.isEmpty) tla.emptySeq(elemT)
          else tla.seq(args: _*)

        case RecT1(fieldTypes) =>
          val keys = fieldTypes.keySet
          val diffOpt = for {
            fields <- json.allFieldsOpt
          } yield (keys -- fields) ++ (fields -- keys) // symmetric difference

          // The above is None, iff json is not an Object with fields
          val diff = diffOpt.getOrElse {
            throw new JsonDeserializationError(s"Record object contents are malformed.")
          }

          // The record type and value must declare the _same_ fields
          if (diff.nonEmpty)
            throw new JsonDeserializationError(
                s"Record object and its type annotation $tt1 define different key sets. " +
                  s"The keys ${diff.toSeq.mkString(", ")} are present in exactly one of the two.")

          // TODO: We currently don't check the key shape against any sort of pattern.
          // Technically, "_-?*+" is a valid record field, as far as this code is concerned.
          // Do we want to restrict the permissible record field names, and if so, to what?

          val recElems = json.allFieldsOpt.get.toSeq.map { k =>
            k -> typeDrivenBuild(json.getFieldOpt(k).get, fieldTypes(k))
          }

          // Records must contain at least 1 kv pair
          if (recElems.isEmpty) throw new JsonDeserializationError(s"Records may not be empty.")

          tla.rec(recElems: _*)

        case TupT1(elems @ _*) =>
          if (!json.allFieldsOpt.contains(Set(TUP_FIELD)))
            throw new JsonDeserializationError(s"Tuple-type annotated values must declare a \"$TUP_FIELD\" field.")
          val tupSeq = scalaFactory.asSeq(json.getFieldOpt(TUP_FIELD).get)

          // The declared tuple length must match the # of elements
          val valLen = tupSeq.length
          val typeLen = elems.length
          if (valLen != typeLen)
            throw new JsonDeserializationError(
                s"Tuple value and type have $valLen and $typeLen elements respectively."
            )

          val args = tupSeq.zip(elems).map { case (elemJson, elemT) =>
            typeDrivenBuild(elemJson, elemT)
          }
          tla.tuple(args: _*)

        case SetT1(elemT) =>
          if (!json.allFieldsOpt.contains(Set(SET_FIELD)))
            throw new JsonDeserializationError(s"Set-type annotated values must declare a \"$SET_FIELD\" field.")
          val setSeq = scalaFactory.asSeq(json.getFieldOpt(SET_FIELD).get)
          val args = setSeq.map { elemJson =>
            typeDrivenBuild(elemJson, elemT)
          }
          // Empty collections have special builder ctors
          args match {
            case Seq() => tla.emptySet(elemT)
            case seq   => tla.enumSet(seq: _*)
          }

        case FunT1(argT, resT) =>
          if (!json.allFieldsOpt.contains(Set(MAP_FIELD)))
            throw new JsonDeserializationError(s"Function-type annotated values must declare a \"$MAP_FIELD\" field.")

          val funSeq = scalaFactory.asSeq(json.getFieldOpt(MAP_FIELD).get)

          // Since ITF functions are enumerated, we must construct a funAsSet, instead of a funDef.

          val args = funSeq.map { pairArrayJson =>
            val pairArray = scalaFactory.asSeq(pairArrayJson)
            if (pairArray.length != 2)
              throw new JsonDeserializationError(
                  s"Function entries must be 2-element arrays. Found entry with ${pairArray.length} elements.")
            val Seq(kJson, vJson) = pairArray
            val k = typeDrivenBuild(kJson, argT)
            val v = typeDrivenBuild(vJson, resT)
            tla.tuple(k, v) // for funAsSet, we need a set of paris
          }
          // Empty collections have special builder ctors
          val set =
            if (args.isEmpty) tla.emptySet(TupT1(argT, resT))
            else tla.enumSet(args: _*)

          // TODO: Check if keys are duplicated or let SetAsFun rule catch that? Aternatively,
          // treat it as double-except semantics

          tla.setAsFun(set)

        case _ =>
          throw new JsonDeserializationError(s"Type $tt1 does not match any of the permitted ITF value types.")

      }
    }

  def getTrace(json: T): Trace = {
    val typesMap = validateShapeAndGetTypes(json)
    val varSet = typesMap.keySet

    val states =
      json
        .getFieldOpt(STATES_FIELD)
        .map(jsonSeq => IndexedSeq.from(scalaFactory.asSeq(jsonSeq)))
        .getOrElse {
          throw new JsonDeserializationError(s"Malformed JSON: missing $STATES_FIELD field.")
        }

    states.map { stateJson =>
      stateJson.allFieldsOpt match {
        case None => throw new JsonDeserializationError(s"Malformed JSON: Value at $STATES_FIELD is not an object.")
        case Some(varsInState) =>
          val undeclared = (varsInState -- varSet) - META_FIELD // #meta is the only extra field allowed in states
          if (undeclared.nonEmpty)
            throw new JsonDeserializationError(
                s"Undeclared variable(s) present in state: ${undeclared.mkString(", ")}.")
          val missing = varSet -- varsInState
          if (missing.nonEmpty)
            throw new JsonDeserializationError(s"Variable(s) missing from state: ${missing.mkString(", ")}.")
      }
      // assume now the variables in the state are exactly the keys of typesMap
      typesMap.map { case (varName, varT) =>
        varName -> typeDrivenBuild(stateJson.getFieldOpt(varName).get, varT).build
      }
    }
  }
}

object ItfToTla {

  val META_FIELD: String = "#meta"
  val VAR_TYPES_FIELD: String = "varTypes"
  val VARS_FIELD: String = "vars"
  val STATES_FIELD: String = "states"

  val BIG_INT_FIELD: String = "#bigint"
  val TUP_FIELD: String = "#tup"
  val SET_FIELD: String = "#set"
  val MAP_FIELD: String = "#map"
  val UNSERIALIZABLE_FIELD: String = "#unserializable"
}
