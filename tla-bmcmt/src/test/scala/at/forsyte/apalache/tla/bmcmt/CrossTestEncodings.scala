package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Checker.Error
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.bmcmt.trex.{IncrementalExecutionContext, TransitionExecutorImpl}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.scalatest.funsuite.AnyFunSuite

/**
 * Test encodings against each other. Override [[AnyFunSuite.withFixture]] to set up SMT encodings used for oracle and
 * verifier.
 *
 * This first generates a type `witnessType` and a set-valued expression `witnesses` of type `Set(witnessType)`. It then
 * checks the invariant of the following spec:
 *
 * {{{
 * ------ MODULE Oracle --------
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

trait CrossTestEncodings extends AnyFunSuite {
  // Override [[AnyFunSuite.withFixture]] to set the encodings.
  protected var oracleEncoding: SMTEncoding = _
  protected var verifierEncoding: SMTEncoding = _

  // TODO: Use PBT to generate these. Issue: https://github.com/informalsystems/apalache/issues/1639
  private val witnessType = IntT1()
  private val witnesses = tla.intSet().as(SetT1(witnessType))
  private val types = Map("w" -> witnessType, "b" -> BoolT1(), "o" -> OperT1(Nil, BoolT1()))

  /**
   * Rewrite elem \in Set ~~> \E elem$selected \in Set: elem' := elem$selected.
   */
  private def rewriteElemInSet(elem: NameEx, set: TlaEx): TlaEx = {
    val selected = tla.name(elem.name + "$selected").typed(types, "w")
    tla
      .apalacheSkolem(tla.exists(selected, set, tla.assign(tla.prime(elem) ? "w", selected) ? "b") ? "b")
      .typed(types, "b")
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
   *   a counterexample returned as VarNames -> Expressions binding in the initial state, i.e., after executing
   *   [[initTrans]].
   */
  private def modelCheckAndGetCex(
      moduleName: String,
      variableDecls: Seq[TlaDecl],
      initTrans: List[TlaEx],
      nextTrans: List[TlaEx],
      invExpr: TlaEx,
      smtEncoding: SMTEncoding): Map[String, TlaEx] = {
    // prepare the invariant
    val invDecl = tla.declOp("Inv", invExpr ? "b").typed(types, "o")
    val decls = variableDecls :+ invDecl
    val invariantsAndNegations = List((invExpr, tla.not(invExpr).as(BoolT1())))
    val verificationConditions = CheckerInputVC(invariantsAndNegations)

    val module = TlaModule(moduleName, decls)

    val checkerInput = new CheckerInput(module, initTrans, nextTrans, None, verificationConditions)
    val checkerParams = new ModelCheckerParams(checkerInput, 0)

    val solverContext = RecordingSolverContext.createZ3(None, SolverConfig.default)
    val rewriter: SymbStateRewriterImpl = smtEncoding match {
      case `oopsla19Encoding` => new SymbStateRewriterImpl(solverContext)
      case `arraysEncoding`   => new SymbStateRewriterImplWithArrays(solverContext)
    }

    val ctx = new IncrementalExecutionContext(rewriter)
    val trex = new TransitionExecutorImpl(checkerParams.consts, checkerParams.vars, ctx)

    // run the model checker with listener
    val listener = new CollectCounterexamplesModelCheckerListener()
    val checker = new SeqModelChecker(checkerParams, checkerInput, trex, Seq(listener))

    // check the outcome
    val outcome = checker.run()
    assert(Error(1) == outcome)

    // extract witness expression from the counterexample
    assert(listener.counterExamples.length == 1) // () --(init transition)--> initial state
    val cex = listener.counterExamples.head.path
    val (binding, _) = cex.last // initial state binding
    binding
  }

  /**
   * Return a witness TLA+ expression (generated through model-checking the `Oracle` spec with the oracle encoding, see
   * [[CrossTestEncodings]]).
   */
  private def getWitness: TlaEx = {
    val witness = NameEx("witness")(Typed(witnessType))
    val witnessDecl = TlaVarDecl(witness.name)(witness.typeTag)
    val found = NameEx("found")(Typed(BoolT1()))
    val foundDecl = TlaVarDecl(found.name)(found.typeTag)

    // Construct the `TlaModule`.
    // VARIABLES witness, found
    val variableDecls = List(witnessDecl, foundDecl)
    // Init == witness \in ${witnesses} /\ found \in BOOLEAN
    val initTrans =
      List(tla
            .and(rewriteElemInSet(witness, witnesses), rewriteElemInSet(found, tla.booleanSet().as(SetT1(BoolT1()))))
            .typed(types, "b"))
    // Next == UNCHANGED <<witness, found>>
    val nextTrans = List(tla
          .and(tla.assign(tla.prime(witness) ? "w", witness) ? "b", tla.assign(tla.prime(found) ? "b", found) ? "b")
          .typed(types, "b"))
    // NotFound == ~found
    val inv = tla.not(found).typed(types, "b")

    // Call the model checker.
    val binding = modelCheckAndGetCex("Oracle", variableDecls, initTrans, nextTrans, inv, oracleEncoding)

    // Extract witness expression from the counterexample.
    assert(binding.contains(witness.name))
    val witnessExpr = binding(witness.name)
    witnessExpr
  }

  /**
   * Return a TLA+ expression `result` such that `result = witness` in the verifier encoding.
   *
   * This will force `result = ${witness}` in a TLA+ module and run the model checker to produce a value for `result`.
   *
   * @param witness
   *   TLA+ expression to check, should be generated by [[getWitness]].
   * @return
   *   The `result` expression.
   */
  private def verify(witness: TlaEx): TlaEx = {
    witness.typeTag.asTlaType1()

    // Module-level TLA+ variables.
    // We will force `result` = `witness` in `Init`.
    val result = NameEx("result")(witness.typeTag)
    val resultDecl = TlaVarDecl(result.name)(witness.typeTag)
    val found = NameEx("found")(Typed(BoolT1()))
    val foundDecl = TlaVarDecl(found.name)(found.typeTag)

    // Construct the `TlaModule`.
    // VARIABLES witness, found
    val variableDecls: Seq[TlaDecl] = Seq(resultDecl, foundDecl)
    // Init == result \in ${witnesses} /\ result = ${witness} /\ found \in BOOLEAN
    val initTrans = List(tla
          .and(rewriteElemInSet(result, witnesses), tla.eql(tla.prime(result) ? "w", witness) ? "b",
              rewriteElemInSet(found, tla.booleanSet().as(SetT1(BoolT1()))))
          .typed(types, "b"))
    // Next == UNCHANGED <<result, found>>
    val nextTrans = List(tla
          .and(tla.assign(tla.prime(result) ? "w", result) ? "b", tla.assign(tla.prime(found) ? "b", found) ? "b")
          .typed(types, "b"))
    // NotFound == ~found
    val inv = tla.not(found).typed(types, "b")

    // Call the model checker.
    val binding = modelCheckAndGetCex("Verifier", variableDecls, initTrans, nextTrans, inv, verifierEncoding)
    assert(binding.contains(result.name))
    val resultExpr = binding(result.name)
    resultExpr
  }

  test("encodings are consistent") {
    val witness = getWitness
    val result = verify(witness)
    assert(result == witness)
  }
}
