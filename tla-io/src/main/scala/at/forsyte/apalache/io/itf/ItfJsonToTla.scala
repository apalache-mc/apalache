package at.forsyte.apalache.io.itf

import at.forsyte.apalache.io.json.{JsonDeserializationError, JsonRepresentation, ScalaFromJsonAdapter}
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
class ItfJsonToTla[T <: JsonRepresentation](scalaAdapter: ScalaFromJsonAdapter[T]) {

  /**
   * Parse a single state from ITF JSON into a mapping from variable names to TLA+ expressions.
   * @param varTypes
   *   variable types
   * @param jsonValue
   *   json value that represents a state
   * @return
   *   either an error or the parsed state
   */
  def parseState(varTypes: Map[String, TlaType1], jsonValue: T): Either[ItfError, Trace.State] = for {
    varsInState <- jsonValue.allFieldsOpt.toRight(ItfFormatError(s"State must be an object."))
    // build a TLA+ value for each variable
    mapSeq <- eitherSeq((varsInState - META_FIELD).toSeq.map { varName =>
      varTypes
        .get(varName)
        .toRight(ItfFormatError(s"Variable $varName has no type annotation."))
        .flatMap { varType =>
          parseItfValueToTlaExpr(jsonValue.getFieldOpt(varName).get, varType)
            .map { exprBuilderInst => varName -> exprBuilderInst.build }
        }
    })
  } yield mapSeq.toMap

  /**
   * Parses the trace from ITF JSON into a sequence of states.
   * @param json
   *   a JSON object representing an ITF trace
   * @return
   *   either an error or the parsed trace
   */
  def parseTrace(json: T): Either[Exception, IndexedSeq[Trace.State]] = for {
    varTypes <- parseHeaderAndVarTypes(json)
    varSet = varTypes.keySet
    statesJsonSeq <- json
      .getFieldOpt(STATES_FIELD)
      .toRight(ItfFormatError(s"ITF JSON must declare a $STATES_FIELD field."))
    states <- asSeq(statesJsonSeq)
    trace <- eitherSeq(states.map { stateJson =>
      for {
        // find the variable names present in this state
        varsInState <- stateJson.allFieldsOpt.toRight(ItfFormatError(s"State must be an object."))
        // make sure that no extra variables are present
        _ <- {
          val undeclared = (varsInState -- varSet) - META_FIELD // #meta is the only extra field allowed in states
          requirement(
              undeclared.isEmpty,
              ItfFormatError(s"Undeclared variable(s) present in state: ${undeclared.mkString(", ")}."),
          )
        }
        // make sure that no variables are missing
        _ <- {
          val missing = varSet -- varsInState
          requirement(
              missing.isEmpty,
              ItfFormatError(s"Variable(s) missing from state: ${missing.mkString(", ")}."),
          )
        }
        // build a TLA+ value for each variable
        state <- parseState(varTypes, stateJson)
      } yield state
    })
  } yield IndexedSeq.from(trace)

  /**
   * Checks that the Apalache-specific ITF requirements are met, as defined in ADR15. If yes, returns a mapping from
   * variables to their types in a Right(_), or an error-wrapping Left(_) otherwise.
   */
  private[itf] def parseHeaderAndVarTypes(json: T): Either[ItfError, Map[String, TlaType1]] = for {
    // ADR-15 declares "#meta" as an optional field, but we need it for type annotations.
    // So we have to require it here. There is a section in ADR-15 that mandates it for Apalache.
    meta <- json
      .getFieldOpt(META_FIELD)
      .toRight(ItfFormatError(s"ITF JSON must have the field $META_FIELD: { $VAR_TYPES_FIELD: {...}, ... }."))
    varTypes <- meta
      .getFieldOpt(VAR_TYPES_FIELD)
      .toRight(ItfFormatError(s"$META_FIELD must be of shape { $VAR_TYPES_FIELD: {...}, ... }."))
    varTypesKeys <- varTypes.allFieldsOpt.toRight(ItfFormatError(s"$VAR_TYPES_FIELD must be an object."))
    // make sure that the field "vars" is present
    vars <- json
      .getFieldOpt(VARS_FIELD)
      .toRight(ItfFormatError(s"ITF JSON must declare a $VARS_FIELD field."))
    varSeq <- asSeq(vars)
    varSet <- eitherSeq(varSeq.map(asStr)).map(_.toSet)
    // check whether all variables have type annotations
    _ <- {
      val untaggedVars = varSet -- varTypesKeys
      requirement(
          untaggedVars.isEmpty,
          ItfFormatError(s"Missing type annotations in $VAR_TYPES_FIELD for ${untaggedVars.mkString(", ")}."),
      )
    }
    // check that no extra variables are tagged with types
    _ <- {
      val spuriouslyTaggedVars = varTypesKeys -- varSet
      requirement(
          spuriouslyTaggedVars.isEmpty,
          ItfFormatError(
              s"Found type annotations in $VAR_TYPES_FIELD for unknown variables ${spuriouslyTaggedVars.mkString(", ")}."),
      )
    }
    // parse the type annotations
    typeMapAsSeq <- eitherSeq(varTypesKeys.toSeq.map { varName =>
      for {
        typeStringJson <- varTypes
          .getFieldOpt(varName)
          .toRight(ItfFormatError(s"$VAR_TYPES_FIELD must contain an entry for variable $varName."))
        typeString <- asStr(typeStringJson)
        variableType <-
          try {
            Right(DefaultType1Parser.parseType(typeString))
          } catch {
            case e: JsonDeserializationError => Left(ItfContentError(e.getMessage))
          }
      } yield (varName -> variableType)
    })

  } yield typeMapAsSeq.toMap

  /**
   * Some values, like the predefined sets (Int, Nat, etc.) are encoded as "UNSERIALIZABLE_FIELD": `<value>` Currently,
   * per our discussions, we disallow the use of this tag, but the function can be extended in the future.
   *
   * E.g. we could return tla.intSet() on str = "Int".
   */
  private[itf] def attemptUnserializable(json: T): Option[Either[ItfError, TBuilderInstruction]] =
    Option.when(json.allFieldsOpt.contains(Set(UNSERIALIZABLE_FIELD)))(
        asStr(json.getFieldOpt(UNSERIALIZABLE_FIELD).get).flatMap(str =>
          Left[ItfError, TBuilderInstruction](ItfContentError(s"Unserializable value $str is disallowed.")))
    )

  /**
   * Parses an ITF JSON value into a TLA+ expression, given its type. More specifically, it constructs a
   * `TBuilderInstruction`.
   * @param json
   *   a JSON object representing an ITF value
   * @param tt1
   *   the expected type of the ITF value
   * @return
   *   either an error or the TLA+ expression constructed via TLA+ builder
   */
  private[itf] def parseItfValueToTlaExpr(json: T, tt1: TlaType1): Either[ItfError, TBuilderInstruction] = {
    // Note: attemptUnserializable + getOrElse is future-proof, and allows us to eventually case-match
    // unserializable values.
    attemptUnserializable(json).getOrElse {
      tt1 match {
        case BoolT1 =>
          asBool(json).map { tla.bool }

        case StrT1 =>
          asStr(json).flatMap { s =>
            Either.cond(
                !ModelValueHandler.isModelValue(s),
                tla.str(s),
                ItfContentError(s"$s is annotated as a string, but has the value of an uninterpreted literal."),
            )
          }

        case ct: ConstT1 =>
          for {
            rawString <- asStr(json)
            // ConstT1-type literals must adhere to the pattern regex
            typeIndex <- ModelValueHandler
              .typeAndIndex(rawString)
              .toRight(
                  ItfContentError(s"$rawString is annotated as an uninterpreted literal, but has string form.")
              )
            (constT, idx) = typeIndex
            // The pattern-suffix must also match the declared type
            _ <- requirement(
                ct == constT,
                ItfContentError(s"$rawString is annotated as $ct but has a $constT value."),
            )
          } yield tla.const(idx, constT)

        case IntT1 =>
          // Big integers are written as strings, not JS integers
          if (json.allFieldsOpt.contains(Set(BIG_INT_FIELD))) {
            asStr(json.getFieldOpt(BIG_INT_FIELD).get).map { bigint =>
              tla.int(BigInt(bigint))
            }
          } else {
            // We keep this case for the backwards compatibility with the older versions of ITF.
            // Apalache itself does not produce this case any longer.
            asInt(json).map { i => tla.int(BigInt(i)) }
          }

        case SeqT1(elemT) =>
          for {
            elems <- asSeq(json)
            args <- eitherSeq(
                elems.map { parseItfValueToTlaExpr(_, elemT) }
            )
          } yield {
            if (args.isEmpty) tla.emptySeq(elemT) else tla.seq(args: _*)
          }

        case RecT1(fieldTypes) =>
          val keys = fieldTypes.keySet
          for {
            fields <- json.allFieldsOpt.toRight(ItfFormatError(s"Record must be a JSON object."))
            missing = keys -- fields
            spurious = fields -- keys
            // The record type and value must declare the _same_ fields
            _ <- requirement(
                missing.isEmpty,
                ItfFormatError(
                    s"The following keys are present in the type, but not the value: ${missing.mkString(", ")}."),
            )
            _ <- requirement(
                spurious.isEmpty,
                ItfFormatError(
                    s"The following keys are present in the value, but not the type annotation: ${spurious.mkString(", ")}."),
            )
            recElems <-
              eitherSeq(
                  fields.toSeq.map { key =>
                    for {
                      _ <- requirement(
                          isValidIdentifier(key),
                          ItfContentError(s"Record key $key is not a valid TLA+ identifier."),
                      )
                      bi <- parseItfValueToTlaExpr(json.getFieldOpt(key).get, fieldTypes(key))
                    } yield key -> bi
                  }
              )
            // Records must contain at least 1 kv pair
            _ <- requirement(
                recElems.nonEmpty,
                ItfFormatError(s"Records may not be empty."),
            )
          } yield tla.rec(recElems: _*)

        case TupT1(elems @ _*) =>
          for {
            _ <- requirement(
                json.allFieldsOpt.contains(Set(TUP_FIELD)),
                ItfFormatError(s"Tuple-type annotated values must declare a \"$TUP_FIELD\" field."),
            )
            tupSeq <- asSeq(json.getFieldOpt(TUP_FIELD).get)
            // The declared tuple length must match the # of elements
            valLen = tupSeq.length
            typeLen = elems.length
            _ <- requirement(
                valLen == typeLen,
                ItfContentError(s"\"Tuple value and type have $valLen and $typeLen elements respectively.\""),
            )
            args <- eitherSeq(
                tupSeq.zip(elems).map { case (elemJson, elemT) =>
                  parseItfValueToTlaExpr(elemJson, elemT)
                }
            )
          } yield tla.tuple(args: _*)

        case SetT1(elemT) =>
          for {
            _ <- requirement(
                json.allFieldsOpt.contains(Set(SET_FIELD)),
                ItfFormatError(s"Set-type annotated values must declare a \"$SET_FIELD\" field."),
            )
            setSeq <- asSeq(json.getFieldOpt(SET_FIELD).get)
            args <- eitherSeq(
                setSeq.map { parseItfValueToTlaExpr(_, elemT) }
            )
            // Empty collections have special builder ctors
          } yield args match {
            case Seq() => tla.emptySet(elemT)
            case seq   => tla.enumSet(seq: _*)
          }

        case FunT1(argT, resT) =>
          for {
            _ <- requirement(
                json.allFieldsOpt.contains(Set(MAP_FIELD)),
                ItfFormatError(s"Function-type annotated values must declare a \"$MAP_FIELD\" field."),
            )
            funSeq <- asSeq(json.getFieldOpt(MAP_FIELD).get)
            // Since ITF functions are enumerated, we must construct a funAsSet, instead of a funDef.
            args <- eitherSeq(
                funSeq.map { pairArrayJson =>
                  for {
                    pairArray <- asSeq(pairArrayJson)
                    _ <- requirement(
                        pairArray.length == 2,
                        ItfFormatError(
                            s"Function entries must be 2-element arrays. Found entry with ${pairArray.length} elements."),
                    )
                    Seq(kJson, vJson) = pairArray
                    k <- parseItfValueToTlaExpr(kJson, argT)
                    v <- parseItfValueToTlaExpr(vJson, resT)
                  } yield tla.tuple(k, v)
                }
            )
          } yield {
            // Empty collections have special builder ctors
            val set =
              if (args.isEmpty) tla.emptySet(TupT1(argT, resT))
              else tla.enumSet(args: _*)

            // We leave it to the SetAsFun rule to handle key-duplication
            tla.setAsFun(set)
          }

        case _ =>
          Left(ItfContentError(s"Type $tt1 does not match any of the permitted ITF value types."))
      }
    }
  }

  /**
   * Check a requirement and produce an error as `Left(...)`; otherwise, produce `()`. This is meant to be used as
   * `_ <- requirement(b, e)` instead of `if (!b) throw e`.
   */
  private def requirement(condition: Boolean, errIfNotCond: ItfError): Either[ItfError, Unit] = {
    Either.cond(condition, (), errIfNotCond)
  }

  private def asStr(json: T): Either[ItfFormatError, String] = {
    try {
      Right(scalaAdapter.asStr(json))
    } catch {
      case e: JsonDeserializationError => Left(ItfFormatError(e.getMessage))
    }
  }

  private def asInt(json: T): Either[ItfFormatError, Int] = {
    try {
      Right(scalaAdapter.asInt(json))
    } catch {
      case e: JsonDeserializationError => Left(ItfFormatError(e.getMessage))
    }
  }

  private def asBool(json: T): Either[ItfFormatError, Boolean] = {
    try {
      Right(scalaAdapter.asBool(json))
    } catch {
      case e: JsonDeserializationError => Left(ItfFormatError(e.getMessage))
    }
  }

  private def asSeq(json: T): Either[ItfFormatError, Seq[T]] = {
    try {
      Right(scalaAdapter.asSeq(json))
    } catch {
      case e: JsonDeserializationError => Left(ItfFormatError(e.getMessage))
    }
  }

  private def eitherSeq[V](seq: Seq[Either[ItfError, V]]): Either[ItfError, Seq[V]] = {
    val lefts = seq.collect { case Left(x) => x }
    val rights = seq.collect { case Right(x) => x }
    lefts match {
      case Seq()  => Right(rights)
      case Seq(l) => Left(l)
      case _      => Left(MultipleErrors(lefts))
    }
  }

  // TLA+ identifiers must start with a letter or underscore, followed by any number of letters, digits, or underscores.
  private def isValidIdentifier(s: String): Boolean = s.matches("[A-Za-z_][A-Za-z0-9_]*")
}
