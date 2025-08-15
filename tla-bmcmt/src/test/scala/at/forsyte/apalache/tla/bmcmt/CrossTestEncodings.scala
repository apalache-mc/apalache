package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.Checker.{CheckerResult, Error}
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.trex.{IncrementalExecutionContext, TransitionExecutorImpl}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import ch.qos.logback.classic.{Level, Logger}
import org.scalacheck.Arbitrary.arbitrary
import org.scalacheck.Gen
import org.scalacheck.Gen.{choose, const, listOf, lzy, nonEmptyListOf, oneOf, resize, sized}
import org.scalacheck.Prop.{forAllShrink, AnyOperators}
import org.scalacheck.Shrink.shrink
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.scalacheck.Checkers
import org.slf4j.LoggerFactory

import scala.annotation.nowarn

/**
 * Test encodings against each other, aka Nitpicker.
 *
 * Override [[AnyFunSuite.withFixture]] to set up SMT encodings used for oracle and verifier.
 *
 * This first generates a type `witnessType` and a set-valued expression `witnesses` of type `Set(witnessType)`. It then
 * checks the invariant of the following spec:
 *
 * {{{
 * ------ MODULE Oracle --------
 * EXTENDS Apalache, Integers
 * VARIABLES
 *   \* @type: ${witnessType};
 *   witness,
 *   \* @type: Bool;
 *   found
 *
 * Init ==
 *   /\ witness \in ${witnesses}
 *   /\ found \in BOOLEAN
 *
 * Next ==
 *   UNCHANGED <<witness, found>>
 *
 * NotFound ==
 *   ~found
 * ======================
 * }}}
 *
 * By checking the invariant `NotFound` of the spec `Oracle`, we obtain a value `witness` that belongs to the set
 * `witnesses`, if such a value exists. We call the SMT encoding used the "oracle encoding".
 *
 * We then feed the expression `witness` into the `Verifier` spec:
 *
 * {{{
 * ------ MODULE Verifier --------
 * EXTENDS Apalache, Integers
 * VARIABLES
 *   \* @type: ${witnessType};
 *   result,
 *   \* @type: Bool;
 *   found
 *
 * Init ==
 *   /\ result \in ${witnesses}
 *   /\ result = ${witness}
 *   /\ found \in BOOLEAN
 *
 * Next ==
 *   UNCHANGED <<result, found>>
 *
 * NotFound ==
 *   ~found
 * ======================
 * }}}
 *
 * When checking the invariant `NotFound` of the spec `Verifier` ''with a different encoding'', the "verifier encoding",
 * we can have two possible outcomes:
 *
 *   - There is a counterexample. We compare the value of `result` to witness. They should match. If they don't, there
 *     is a bug in one of the encodings.
 *   - There is no counterexample. There is a bug in one of the encodings.
 */

trait CrossTestEncodings extends AnyFunSuite with Checkers {
  // Override [[AnyFunSuite.withFixture]] to set the encodings.
  protected var oracleEncoding: SMTEncoding = _
  protected var verifierEncoding: SMTEncoding = _

  private val boolT = BoolT1
  private val boolSetT = SetT1(BoolT1)

  private val typeGen = new TlaType1Gen {
    // Override to avoid operators and rows.
    // TODO(#401): Enable rows, variants when supported by the model checker.
    override def genTypeTree: Gen[TlaType1] = lzy {
      sized { size =>
        if (size <= 1) genPrimitive
        else
          oneOf(
              genPrimitive,
              genSet,
              genSeq,
              genFun, /*genOper,*/ genTup,
              genRec, /*, genRowRec, genVariant, genRow*/
          )
      }
    }

    // Override to temporarily avoid sets of functions, see https://github.com/informalsystems/apalache/issues/1759.
    override def genSet: Gen[TlaType1] = sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size)
        // Don't produce sets of functions.
        // TODO(#1452): Re-enable sets of functions when we have better support.
        g <- resize(size / (s + 1), genTypeTree).suchThat(_ match {
          case FunT1(_, _) => false
          case _           => true
        })
      } yield SetT1(g)
    }

    // Override to avoid reals, constants, and typevar-typed expressions.
    override def genPrimitive: Gen[TlaType1] =
      oneOf(const(BoolT1), const(IntT1), const(StrT1) /*, const(RealT1), genConst, genVar*/ )
  }
  private val irGen = new IrGenerators {}

  private val renaming = new IncrementalRenaming(new IdleTracker)

  /**
   * Rewrite elem \in Set ~~> \E elem$selected \in Set: elem' := elem$selected.
   */
  private def rewriteElemInSet(elem: NameEx, set: TlaEx): TlaEx = {
    val elemT = elem.typeTag.asTlaType1()
    val selected = tla.name(elem.name + "$selected").as(elemT)
    tla
      .apalacheSkolem(tla.exists(selected, set, tla.assign(tla.prime(elem).as(elemT), selected).as(boolT)).as(boolT))
      .as(boolT)
  }

  /**
   * Facade for running bounded model-checking through [[SeqModelChecker]].
   *
   * @param moduleName
   *   name of the TLA+ module to check
   * @param variableDecls
   *   TLA+ variable declarations
   * @param initTrans
   *   init transition, see examples in [[getWitness]] and [[verify]]
   * @param nextTrans
   *   next transition, see examples in [[getWitness]] and [[verify]]
   * @param invExpr
   *   invariant to check
   * @param smtEncoding
   *   SMT encoding to use inside the model checker
   * @return
   *   either a checker result if a counterexample cannot be found after a single step, or the counterexample returned
   *   as VarNames -> Expressions binding in the initial state, i.e., after executing [[initTrans]].
   */
  private def modelCheckAndGetCex(
      moduleName: String,
      variableDecls: Seq[TlaDecl],
      initTrans: List[TlaEx],
      nextTrans: List[TlaEx],
      invExpr: TlaEx,
      smtEncoding: SMTEncoding): Either[CheckerResult, Map[String, TlaEx]] = {
    // prepare the invariant
    val invDecl = tla.declOp("Inv", invExpr).as(OperT1(Nil, BoolT1))
    val decls = variableDecls :+ invDecl
    val invariantsAndNegations = List((invExpr, tla.not(invExpr).as(BoolT1)))
    val verificationConditions = CheckerInputVC(invariantsAndNegations)

    val module = TlaModule(moduleName, decls)

    val checkerInput = new CheckerInput(module, initTrans, nextTrans, None, verificationConditions)
    val checkerParams = new ModelCheckerParams(checkerInput, 0)

    val solverContext =
      new Z3SolverContext(new SolverConfig(debug = false, profile = false, randomSeed = 0, smtEncoding = smtEncoding,
              z3StatsSec = 0))
    val rewriter: SymbStateRewriterImpl = smtEncoding match {
      case SMTEncoding.OOPSLA19  => new SymbStateRewriterImpl(solverContext, renaming)
      case SMTEncoding.Arrays    => new SymbStateRewriterImplWithArrays(solverContext, renaming)
      case SMTEncoding.FunArrays => new SymbStateRewriterImplWithFunArrays(solverContext, renaming)
    }

    val exeCtx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(checkerParams.consts, checkerParams.vars, exeCtx)

    // run the model checker with listener
    val listener = new CollectCounterexamplesModelCheckerListener()
    val mcCtx = ModelCheckerContext(checkerParams, checkerInput, trex, Seq(listener))
    val checker = new SeqModelChecker(mcCtx)

    // check the outcome
    checker.run() match {
      case Error(1, _) =>
        // extract witness expression from the counterexample
        assert(listener.counterExamples.length == 1) // () --(init transition)--> initial state
        val cex = listener.counterExamples.head.states
        val (_, binding) = cex.last // initial state binding
        Right(binding)

      case outcome => Left(outcome)
    }
  }

  private def formatOracleSpec(witnessType: TlaType1, witnesses: TlaEx): String = {
    s"""------ MODULE Oracle --------
      |EXTENDS Apalache, Integers
      |VARIABLES
      |  \\* @type: ${witnessType};
      |  witness,
      |  \\* @type: Bool;
      |  found
      |
      |Init ==
      |  /\\ witness \\in ${witnesses}
      |  /\\ found \\in BOOLEAN
      |
      |Next ==
      |  UNCHANGED <<witness, found>>
      |
      |NotFound ==
      |  ~found
      |======================
      |""".stripMargin
  }

  def formatVerifierSpec(witnessType: TlaType1, witnesses: TlaEx, witness: TlaEx): String = {
    s"""------ MODULE Verifier --------
      |EXTENDS Apalache, Integers
      |VARIABLES
      |  \\* @type: ${witnessType};
      |  result,
      |  \\* @type: Bool;
      |  found
      |
      |Init ==
      |  /\\ result \\in ${witnesses}
      |  /\\ result = ${witness}
      |  /\\ found \\in BOOLEAN
      |
      |Next ==
      |  UNCHANGED <<result, found>>
      |
      |NotFound ==
      |  ~found
      |======================
      |""".stripMargin
  }

  /**
   * Print an error message that no counterexample was found and fail the test.
   */
  private def failNoCex(outcome: CheckerResult, encoding: SMTEncoding, module: String) = {
    fail(s"Did not find a counter-example in 1 step, outcome was ${outcome}. " +
      s"Run `apalache-mc check --inv=NotFound --smt-encoding=${encoding}` on\n${module}")
  }

  /**
   * Return a witness TLA+ expression `witness` such that `witness` is of type `witnessType` and `witness \in
   * witnesses`.
   *
   * Runs the model checker to produce a value for `witness`, by requiring `witness \in ${witnesses}` in a TLA+ module
   * and forcing a counter-example.
   *
   * @param witnessType
   *   desired [[TlaType1]] for the witness.
   * @param witnesses
   *   TLA+ expression referring to a set of type `SetT1(witnessType)`.
   */
  private def getWitness(witnessType: TlaType1, witnesses: TlaEx): TlaEx = {
    // Module-level TLA+ variables.
    // We will force `result` = `witness` in `Init`.
    val witness = NameEx("witness")(Typed(witnessType))
    val witnessDecl = TlaVarDecl(witness.name)(witness.typeTag)
    val found = NameEx("found")(Typed(BoolT1))
    val foundDecl = TlaVarDecl(found.name)(found.typeTag)

    // Construct the `TlaModule`.
    // VARIABLES witness, found
    val variableDecls = List(witnessDecl, foundDecl)
    // Init == witness \in ${witnesses} /\ found \in BOOLEAN
    val initTrans = List(
        tla.and(rewriteElemInSet(witness, witnesses), rewriteElemInSet(found, tla.booleanSet().as(boolSetT))).as(boolT))
    // Next == UNCHANGED <<witness, found>>
    val nextTrans = List(tla
          .and(tla.assign(tla.prime(witness).as(witnessType), witness).as(boolT),
              tla.assign(tla.prime(found).as(boolT), found).as(boolT))
          .as(boolT))
    // NotFound == ~found
    val inv = tla.not(found).as(boolT)

    // Call the model checker.
    modelCheckAndGetCex("Oracle", variableDecls, initTrans, nextTrans, inv, oracleEncoding) match {
      case Left(outcome) =>
        failNoCex(outcome, oracleEncoding, formatOracleSpec(witnessType, witnesses))
      case Right(binding) =>
        // Extract witness expression from the counterexample.
        assert(binding.contains(witness.name))
        val witnessExpr = binding(witness.name)
        witnessExpr
    }
  }

  /**
   * Return a TLA+ expression `result` such that `result \in witnesses` and `result = witness` in the verifier encoding.
   *
   * Runs the model checker to produce a value for `result`, by requiring `result \in witnesses /\ result = ${witness}`
   * in a TLA+ module and forcing a counter-example.
   *
   * @param witness
   *   TLA+ expression to check. Should be generated by [[getWitness]].
   * @param witnesses
   *   TLA+ expression referring to a set such that `witness \in witnesses`. Should be generated by [[getWitness]].
   * @return
   *   The `result` expression.
   */
  private def verify(witness: TlaEx, witnesses: TlaEx): TlaEx = {
    // Module-level TLA+ variables.
    // We will force `result` = `witness` in `Init`.
    val witnessType = witness.typeTag.asTlaType1()
    val result = NameEx("result")(witness.typeTag)
    val resultDecl = TlaVarDecl(result.name)(witness.typeTag)
    val found = NameEx("found")(Typed(BoolT1))
    val foundDecl = TlaVarDecl(found.name)(found.typeTag)

    // Construct the `TlaModule`.
    // VARIABLES witness, found
    val variableDecls: Seq[TlaDecl] = Seq(resultDecl, foundDecl)
    // Init == result \in ${witnesses} /\ result = ${witness} /\ found \in BOOLEAN
    val initTrans = List(tla
          .and(rewriteElemInSet(result, witnesses), tla.eql(tla.prime(result).as(witnessType), witness).as(boolT),
              rewriteElemInSet(found, tla.booleanSet().as(SetT1(BoolT1))))
          .as(boolT))
    // Next == UNCHANGED <<result, found>>
    val nextTrans = List(tla
          .and(tla.assign(tla.prime(result).as(witnessType), result).as(boolT),
              tla.assign(tla.prime(found).as(boolT), found).as(boolT))
          .as(boolT))
    // NotFound == ~found
    val inv = tla.not(found).as(boolT)

    // Call the model checker.
    modelCheckAndGetCex("Verifier", variableDecls, initTrans, nextTrans, inv, verifierEncoding) match {
      case Left(outcome) =>
        failNoCex(outcome, verifierEncoding, formatVerifierSpec(witnessType, witnesses, witness))
      case Right(binding) =>
        assert(binding.contains(result.name))
        val resultExpr = binding(result.name)
        resultExpr
    }
  }

  /**
   * Generate TLA+ expressions of a given [[TlaType1]].
   *
   * @param witnessType
   *   [[TlaType1]] of the expression to generate.
   * @return
   *   A [[Gen]] for expressions of type [[witnessType]].
   */
  private def genWitness(witnessType: TlaType1): Gen[TlaEx] = lzy {
    witnessType match {
      case IntT1                => irGen.genInt
      case BoolT1               => irGen.genBool
      case StrT1                => irGen.genStr
      case SetT1(elemType)      => genWitnessSet(elemType)
      case tp @ SeqT1(elemType) =>
        for {
          elements <- listOf(genWitness(elemType))
        } yield tla.tuple(elements: _*).as(tp)
      case tp @ TupT1(elemTypes @ _*) =>
        for {
          elements <- Gen.sequence[Seq[TlaEx], TlaEx](elemTypes.map(genWitness(_)))
        } yield tla.tuple(elements: _*).as(tp)
      case tp @ RecT1(fieldTypes) =>
        for {
          fieldValues <- Gen.sequence[Seq[TlaEx], TlaEx](fieldTypes.values.map(genWitness(_)))
          fieldNames = fieldTypes.toSeq.map { case (name, _) => tla.str(name).as(StrT1) }
          namesAndSets = TlaOper.interleave(fieldNames, fieldValues)
        } yield OperEx(TlaFunOper.rec, namesAndSets: _*)(Typed(tp))
      case tp @ FunT1(arg, res) =>
        for {
          id <- Gen.identifier
          name = NameEx(id)(Typed(arg))
          set <- genWitnessSet(arg)
          res <- genWitness(res)
        } yield tla.funDef(res, name, set).as(tp)
      // TODO(#401): Enable rows, variants when supported by the model checker.
      case ConstT1(_) | OperT1(_, _) | RealT1 | RecRowT1(_) | RowT1(_, _) | SparseTupT1(_) | VarT1(_) | VariantT1(_) =>
        throw new IllegalArgumentException(
            s"Unsupported type ${witnessType}. Should have been filtered by the override in the declaration of 'CrossTestEncodings.typeGen'.")
    }
  }

  /**
   * Generate TLA+ expressions of type `Set(witnessType)`.
   *
   * @param witnessType
   *   Element [[TlaType1]] of the set expression to generate.
   * @return
   *   A [[Gen]] for expressions of type `Set(witnessType)`.
   */
  private def genWitnessSet(witnessesType: TlaType1): Gen[TlaEx] = lzy {
    witnessesType match {
      case tp @ BoolT1 =>
        for {
          arg <- arbitrary[Boolean]
          set <- oneOf(tla.booleanSet().as(SetT1(tp)), tla.enumSet(tla.bool(arg)).as(SetT1(tp)))
        } yield set
      // Temporarily avoid sets of function sets, see https://github.com/informalsystems/apalache/issues/1759.
      // TODO(#1452): Re-enable when we have better support.
      // case tp @ FunT1(arg, res) =>
      //  for {
      //    domain <- genWitnessSet(arg)
      //    codomain <- genWitnessSet(res)
      //  } yield tla.funSet(domain, codomain).as(SetT1(tp))
      case tp @ FunT1(_, _) =>
        for {
          elements <- nonEmptyListOf(genWitness(tp))
        } yield tla.enumSet(elements: _*).as(SetT1(tp))
      case tp =>
        for {
          elements <- nonEmptyListOf(genWitness(tp))
        } yield tla.enumSet(elements: _*).as(SetT1(tp))
    }
  }

  @nowarn("cat=deprecation&msg=Stream") // ScalaCheck's Shrink still uses Stream, which is deprecated since Scala 2.13.0
  private def shrinkType(tp: TlaType1): Stream[TlaType1] = tp match {
    case IntT1 | RealT1 | BoolT1 | StrT1 => Stream.empty
    case FunT1(arg, res)                 => Stream(arg, res)
    case SetT1(elem)                     => Stream(elem)
    case SeqT1(elem)                     => Stream(elem)
    case TupT1(elems @ _*)               =>
      Stream.concat(
          // shrink to one of the element types
          Stream(elems: _*),
          // tuples with a single element type shrunk, keeping the other types as-is
          elems.zipWithIndex.foldLeft(Stream.empty[TlaType1]) { case (acc, (tp, idx)) =>
            acc ++ shrink(tp).map(shrunkType => TupT1(elems.updated(idx, shrunkType): _*))
          },
          // tuples over a subset of the current element types
          Stream(shrink(elems).filterNot(_.isEmpty).map(elems => TupT1(elems: _*)): _*),
      )
    case RecT1(fieldTypes) =>
      Stream.concat(
          // shrink to one of the field types
          Stream(fieldTypes.values.toSeq: _*),
          // recursively shrink one record field type
          fieldTypes.foldLeft(Stream.empty[TlaType1]) { case (acc, (fieldName, tp)) =>
            acc ++ shrink(tp).map(shrunkType => RecT1(fieldTypes.updated(fieldName, shrunkType)))
          },
          // records with a subset of the current field types
          Stream(shrink(fieldTypes).filterNot(_.isEmpty).map(elems => RecT1(elems)): _*),
      )
    // TODO(#401): Enable rows, variants when supported by the model checker.
    case ConstT1(_) | OperT1(_, _) | RecRowT1(_) | RowT1(_, _) | SparseTupT1(_) | VarT1(_) | VariantT1(_) =>
      throw new IllegalArgumentException(s"Shrinking unsupported type ${tp}. Should be disabled in type generator.")
  }

  @nowarn("cat=deprecation&msg=Stream") // ScalaCheck's Shrink still uses Stream, which is deprecated since Scala 2.13.0
  private def shrinkEx(ex: TlaEx): Stream[TlaEx] = ex match {
    case OperEx(TlaSetOper.enumSet, args @ _*) =>
      Stream(shrink(args).filterNot(_.isEmpty).map(elems => tla.enumSet(elems: _*).as(ex.typeTag.asTlaType1())): _*)
    // TODO: Shrink further operators. For now, the main obstacle to interpreting the bugs uncovered by this class
    // is that the expression generator produces sets of more elements than necessary.
    case _ => Stream.empty
  }

  // TODO(#1668): Regularly run the encodings comparison.
  // Ignore this test until all bugs are fixed.
  ignore("encodings are consistent") {
    // TODO(#1666): Loggers in SeqModelChecker produce a lot of output; divert logger output.
    // Disable logger output as long as this test is `ignore`.
    LoggerFactory.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME).asInstanceOf[Logger].setLevel(Level.OFF)

    val prop = forAllShrink(typeGen.genType1 :| "witness type", shrinkType) { witnessType =>
      forAllShrink(genWitnessSet(witnessType) :| "witnesses set", shrinkEx) { witnesses =>
        // Uncomment for debugging:
        // println(s"Looking for witness of type ${witnessType} in set ${witnesses}")
        val witness = getWitness(witnessType, witnesses)
        // println(s"Verifying witness=${witness}")
        val result = verify(witness, witnesses)
        result ?= witness
      }.viewSeed("witnesses set")
    }.viewSeed("witness type")
    // To reproduce:
    //   }.useSeed("witnesses set", Seed.fromBase64("<base64 seed>").get).viewSeed("witnesses set")
    // }.useSeed("witness type", Seed.fromBase64("<base 64 seed>").get).viewSeed("witness type")
    check(prop, minSuccessful(1000), minSize(2), sizeRange(7))
  }

}
