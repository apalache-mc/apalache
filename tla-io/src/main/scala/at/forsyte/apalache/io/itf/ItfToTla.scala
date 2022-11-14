package at.forsyte.apalache.io.itf

import at.forsyte.apalache.io.json.{JsonDeserializationError, JsonRepresentation, ScalaFactory}
import at.forsyte.apalache.io.lir.Trace
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.{ModelValueHandler, tla}

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

  // Since we want to use Either, but scalaFactory methods throw, we try-catch and wrap in Left/Right
  private def thrownToEither[K, V, E](eBuilder: String => E, method: K => V)(arg: K): Either[E, V] = try {
    Right(method(arg))
  } catch {
    case e: JsonDeserializationError => Left(eBuilder(e.getMessage))
  }

  private def asStr(json: T): Either[ItfFormatError, String] = thrownToEither(ItfFormatError, scalaFactory.asStr)(json)
  private def asInt(json: T): Either[ItfFormatError, Int] = thrownToEither(ItfFormatError, scalaFactory.asInt)(json)
  private def asBool(json: T): Either[ItfFormatError, Boolean] =
    thrownToEither(ItfFormatError, scalaFactory.asBool)(json)
  private def asSeq(json: T): Either[ItfFormatError, Seq[T]] = thrownToEither(ItfFormatError, scalaFactory.asSeq)(json)

  private def eitherSeq[V](seq: Seq[Either[ItfError, V]]): Either[ItfError, Seq[V]] = {
    val lefts = seq.collect { case Left(x) => x }
    val rights = seq.collect { case Right(x) => x }
    lefts match {
      case Seq()  => Right(rights)
      case Seq(l) => Left(l)
      case _      => Left(MultipleErrors(lefts))
    }
  }

  // A requirement, meant to be used as _ <- requirement(b,e). Either-approach replacement for `if (!b) throw e`
  private def requirement(condition: Boolean, errIfNotCond: ItfError): Either[ItfError, Unit] =
    Either.cond(condition, (), errIfNotCond)

  /**
   * Checks that the Apalache-specific ITF requirements are met, as defined in ADR15. If yes, returns a mapping from
   * variables to their types in a Right(_), or an error-wrapping Left(_) otherwise.
   */
  private[itf] def validateShapeAndGetTypes(json: T): Either[ItfError, Map[String, TlaType1]] = for {
    meta <- json
      .getFieldOpt(META_FIELD)
      .toRight(ItfFormatError(s"ITF JSON must declare a $META_FIELD field."))
    varTypes <- meta
      .getFieldOpt(VAR_TYPES_FIELD)
      .toRight(ItfFormatError(s"$META_FIELD must be an object with a $VAR_TYPES_FIELD field."))
    varTypesKeys <- varTypes.allFieldsOpt.toRight(ItfFormatError(s"$VAR_TYPES_FIELD must be an object."))
    vars <- json
      .getFieldOpt(VARS_FIELD)
      .toRight(ItfFormatError(s"ITF JSON must declare a $VARS_FIELD field."))
    varSeq <- asSeq(vars)
    varSet <- eitherSeq(varSeq.map(asStr)).map(_.toSet)
    _ <- {
      val untaggedVars = varSet -- varTypesKeys
      requirement(
          untaggedVars.isEmpty,
          ItfFormatError(s"Missing type annotations in $VAR_TYPES_FIELD for ${untaggedVars.mkString(", ")}."),
      )
    }
    _ <- {
      val spuriouslyTaggedVars = varTypesKeys -- varSet
      requirement(
          spuriouslyTaggedVars.isEmpty,
          ItfFormatError(s"Spurious type annotations in $VAR_TYPES_FIELD for ${spuriouslyTaggedVars.mkString(", ")}."),
      )
    }
    typeMapAsSeq <- eitherSeq(varTypesKeys.toSeq.map { k =>
      for {
        typeStringJson <- varTypes
          .getFieldOpt(k)
          .toRight(ItfFormatError(s"$VAR_TYPES_FIELD must contain an entry for $k."))
        typeString <- asStr(typeStringJson)
        tt1 <- thrownToEither(ItfContentError, DefaultType1Parser.parseType)(typeString)
      } yield k -> tt1
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

  // Note: attemptUnserializable + getOrElse is future-proof, and allows us to eventually case-match
  // unserializable values.

  // TODO: We currently don't check the key shape against any sort of pattern.
  // Technically, "_-?*+" is a valid record field, as far as this code is concerned.
  // We should change this to check against the valid TLA identifier pattern.
  private def isValidIdentifier(s: String): Boolean = true

  private[itf] def typeDrivenBuild(json: T, tt1: TlaType1): Either[ItfError, TBuilderInstruction] =
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
            raw <- asStr(json)
            // ConstT1-type literals must adhere to the pattern regex
            typeIndex <- ModelValueHandler
              .typeAndIndex(raw)
              .toRight(
                  ItfContentError(s"$raw is annotated as an uninterpreted literal, but has string form.")
              )
            (constT, idx) = typeIndex
            // The pattern-suffix must also match the declared type
            _ <- requirement(
                ct == constT,
                ItfContentError(s"$raw is annotated as $ct but has a $constT value."),
            )
          } yield tla.const(idx, constT)
        case IntT1 =>
          // Big integers are written as strings, not JS integers
          if (json.allFieldsOpt.contains(Set(BIG_INT_FIELD))) {
            asStr(json.getFieldOpt(BIG_INT_FIELD).get).map { bi =>
              tla.int(BigInt(bi))
            }
          } else asInt(json).map { i => tla.int(BigInt(i)) }

        case SeqT1(elemT) =>
          for {
            elems <- asSeq(json)
            args <- eitherSeq(
                elems.map { typeDrivenBuild(_, elemT) }
            )
          } yield
            if (args.isEmpty) tla.emptySeq(elemT)
            else tla.seq(args: _*)

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
                  fields.toSeq.map { k =>
                    for {
                      _ <- requirement(
                          isValidIdentifier(k),
                          ItfContentError(s"Record key $k is not a valid TLA+ identifier."),
                      )
                      bi <- typeDrivenBuild(json.getFieldOpt(k).get, fieldTypes(k))
                    } yield k -> bi
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
                ItfContentError("s\"Tuple value and type have $valLen and $typeLen elements respectively.\""),
            )
            args <- eitherSeq(
                tupSeq.zip(elems).map { case (elemJson, elemT) =>
                  typeDrivenBuild(elemJson, elemT)
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
                setSeq.map { typeDrivenBuild(_, elemT) }
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
                    k <- typeDrivenBuild(kJson, argT)
                    v <- typeDrivenBuild(vJson, resT)
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

  def getTrace(json: T): Either[Exception, Trace] = for {
    typesMap <- validateShapeAndGetTypes(json)
    varSet = typesMap.keySet
    statesJsonSeq <- json
      .getFieldOpt(STATES_FIELD)
      .toRight(ItfFormatError(s"ITF JSON must declare a $STATES_FIELD field."))
    states <- asSeq(statesJsonSeq)
    trace <- eitherSeq(states.map(stateJson =>
          for {
            varsInState <- stateJson.allFieldsOpt.toRight(ItfFormatError(s"State must be an object."))
            _ <- {
              val undeclared = (varsInState -- varSet) - META_FIELD // #meta is the only extra field allowed in states
              requirement(
                  undeclared.isEmpty,
                  ItfFormatError(s"Undeclared variable(s) present in state: ${undeclared.mkString(", ")}."),
              )
            }
            _ <- {
              val missing = varSet -- varsInState
              requirement(
                  missing.isEmpty,
                  ItfFormatError(s"Variable(s) missing from state: ${missing.mkString(", ")}."),
              )
            }
            mapSeq <- eitherSeq(
                typesMap.toSeq.map { case (varName, varT) =>
                  typeDrivenBuild(stateJson.getFieldOpt(varName).get, varT).map { bi =>
                    varName -> bi.build
                  }
                }
            )
          } yield mapSeq.toMap))
  } yield IndexedSeq.from(trace)
}
