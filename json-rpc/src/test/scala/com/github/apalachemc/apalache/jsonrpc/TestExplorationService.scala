package com.github.apalachemc.apalache.jsonrpc

import at.forsyte.apalache.io.ConfigManager
import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.prop.TableFor2
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.ScalaCheckPropertyChecks

import scala.collection.immutable.SortedSet

@RunWith(classOf[JUnitRunner])
class TestExplorationService extends AnyFunSuite with BeforeAndAfter with ScalaCheckPropertyChecks {
  private val spec1 =
    """---- MODULE Inc ----
      |EXTENDS Integers
      |VARIABLE
      |  \* @type: Int;
      |  x
      |Init == I:: x = 0
      |Next ==
      |  \/ A:: x < 3  /\ x' = x + 1
      |  \/ B:: x > -3 /\ x' = x - 1
      |Inv1 == I1:: x >= -3
      |Inv2 == I2:: x <= 3
      |Inv3 == I3:: x /= 0
      |Inv4 == I4:: x' - x = 1 \/ x' - x = -1
      |View == (x = 0)
      |=====================
      """.stripMargin

  private var service: ExplorationService = _

  before {
    val config = ConfigManager("{common.command: 'server'}")
    service = new ExplorationService(config)
  }

  test("load spec") {
    service.loadSpec(LoadSpecParams(sources = Seq(spec1))) match {
      case Right(LoadSpecResult(sessionId, _, params)) =>
        assert(sessionId.nonEmpty, "Session ID should not be empty")
        assert(params.initTransitions.size == 1, "Should have one initial transition")
        assert(params.initTransitions == Seq(SpecEntryMetadata(index = 0, labels = SortedSet("I"))))
        assert(params.nextTransitions.size == 2, "Should have two next transitions")
        assert(params.nextTransitions == Seq(SpecEntryMetadata(index = 0, labels = SortedSet("A")),
            SpecEntryMetadata(index = 1, labels = SortedSet("B"))))
        assert(params.stateInvariants.isEmpty, "Should have no state invariants")
        assert(params.actionInvariants.isEmpty, "Should have no action invariants")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("load spec multiple times") {
    // load the same spec multiple times to make sure that the order of transitions is stable
    val firstSpec =
      service.loadSpec(LoadSpecParams(sources = Seq(spec1))) match {
        case Right(LoadSpecResult(_, _, params)) =>
          params
        case Right(result) =>
          fail(s"Unexpected result: $result")
        case Left(error) =>
          fail(s"Failed to load specification: $error")
      }

    for (i <- 1 to 20) {
      val nextSpec =
        service.loadSpec(LoadSpecParams(sources = Seq(spec1))) match {
          case Right(LoadSpecResult(_, _, params)) =>
            params
          case Right(result) =>
            fail(s"Unexpected result: $result")
          case Left(error) =>
            fail(s"Failed to load specification: $error")
        }
      assert(firstSpec.initTransitions == nextSpec.initTransitions, s"Initial transitions differ on iteration $i")
      assert(firstSpec.nextTransitions == nextSpec.nextTransitions, s"Next transitions differ on iteration $i")
      assert(firstSpec.stateInvariants == nextSpec.stateInvariants, s"State invariants differ on iteration $i")
      assert(firstSpec.actionInvariants == nextSpec.actionInvariants, s"Action invariants differ on iteration $i")
    }
  }

  test("load spec with invariants") {
    service.loadSpec(LoadSpecParams(sources = Seq(spec1), invariants = List("Inv1", "Inv2", "Inv3", "Inv4"))) match {
      case Right(LoadSpecResult(sessionId, _, params)) =>
        assert(sessionId.nonEmpty, "Session ID should not be empty")
        assert(params.initTransitions.size == 1, "Should have one initial transition")
        assert(params.nextTransitions.size == 2, "Should have two next transitions")
        val meta1 = SpecEntryMetadata(index = 0, labels = SortedSet("I1"))
        val meta2 = SpecEntryMetadata(index = 1, labels = SortedSet("I2"))
        val meta3 = SpecEntryMetadata(index = 2, labels = SortedSet("I3"))
        assert(params.stateInvariants.size == 3, "Should have 3 invariants")
        assert(params.stateInvariants == Seq(meta1, meta2, meta3))
        assert(params.actionInvariants.size == 1, "Should have 1 action invariant")
        val meta4 = SpecEntryMetadata(index = 0, labels = SortedSet("I4"))
        assert(params.actionInvariants == Seq(meta4))
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("load spec with a view") {
    service.loadSpec(LoadSpecParams(sources = Seq(spec1), exports = List("View"))) match {
      case Right(LoadSpecResult(sessionId, _, params)) =>
        assert(sessionId.nonEmpty, "Session ID should not be empty")
        assert(params.initTransitions.size == 1, "Should have one initial transition")
        assert(params.nextTransitions.size == 2, "Should have two next transitions")
        assert(params.stateInvariants.isEmpty, "Should have 0 state invariants")
        assert(params.actionInvariants.isEmpty, "Should have 0 action invariants")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to load specification: $error")
    }
  }

  test("dispose spec") {
    service.loadSpec(LoadSpecParams(sources = Seq(spec1))) match {
      case Right(LoadSpecResult(sessionId, _, _)) =>
        service.disposeSpec(DisposeSpecParams(sessionId)) match {
          case Right(DisposeSpecResult(newSessionId)) =>
            assert(newSessionId == sessionId, "Session ID should remain the same after disposal")
          case Right(result) =>
            fail(s"Unexpected result: $result")
          case Left(error) =>
            fail(s"Failed to dispose specification: $error")
        }
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to load specification for disposal: $error")
    }
  }

  test("assume transition 0") {
    val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1))).toOption.get
    service.assumeTransition(AssumeTransitionParams(sessionId = specResult.sessionId, transitionId = 0)) match {
      case Right(AssumeTransitionResult(newSessionId, _, transitionId, status)) =>
        assert(newSessionId == specResult.sessionId, "Session ID should remain the same after assuming transition")
        assert(transitionId == 0, "Transition ID should match the assumed transition")
        assert(status == AssumptionStatus.ENABLED, "Transition should be enabled after assumption")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to assume transition: $error")
    }
  }

  test("next step") {
    val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1))).toOption.get
    assert(service
          .assumeTransition(AssumeTransitionParams(sessionId = specResult.sessionId, transitionId = 0))
          .isRight, "Assuming transition 0 should succeed")
    service.nextStep(NextStepParams(sessionId = specResult.sessionId)) match {
      case Right(NextStepResult(newSessionId, _, newStepNo)) =>
        assert(newSessionId == specResult.sessionId, "Session ID should remain the same after next step")
        assert(newStepNo == 1, "Step number should be 1 after the first step")
      case Left(error) =>
        fail(s"Failed to proceed to the next step: $error")
    }
  }

  test("sequence 0-0-0-0-0 (disabled)") {
    val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1))).toOption.get
    val sessionId = specResult.sessionId
    val params = AssumeTransitionParams(sessionId = sessionId, transitionId = 0, checkEnabled = true)
    // Init$0 is enabled, Next$0 is enabled 3 times, and then disabled
    for (_ <- 0 until 4) {
      service.assumeTransition(params) match {
        case Right(AssumeTransitionResult(newSessionId, _, transitionId, status)) =>
          assert(newSessionId == sessionId, "Session ID should remain the same after assuming transition")
          assert(transitionId == 0, "Transition ID should match the assumed transition")
          assert(status == AssumptionStatus.ENABLED, "Transition should be enabled")
          assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)

        case Left(error) =>
          fail(s"Failed to assume transition: $error")
      }
    }
    service.assumeTransition(params) match {
      case Right(AssumeTransitionResult(newSessionId, _, transitionId, status)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after assuming transition")
        assert(transitionId == 0, "Transition ID should match the assumed transition")
        assert(status == AssumptionStatus.DISABLED, "Transition should be disabled")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to assume transition: $error")
    }
  }

  test("sequence 0-0-0-1-1-0") {
    val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1))).toOption.get
    val sessionId = specResult.sessionId
    val t0 = AssumeTransitionParams(sessionId = sessionId, transitionId = 0, checkEnabled = true)
    val t1 = AssumeTransitionParams(sessionId = sessionId, transitionId = 1, checkEnabled = true)
    for (_ <- 0 until 3) {
      assert(service.assumeTransition(t0).isRight)
      assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)
    }
    for (_ <- 0 until 2) {
      assert(service.assumeTransition(t1).isRight)
      assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)
    }
    service.assumeTransition(t0) match {
      case Right(AssumeTransitionResult(newSessionId, _, transitionId, status)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after assuming transition")
        assert(transitionId == 0, "Transition ID should match the assumed transition")
        assert(status == AssumptionStatus.ENABLED, "Transition should be enabled")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to assume transition: $error")
    }
  }

  test("assumeTransition; nextStep; assumeState") {
    val valueAndStatusTable: TableFor2[Int, AssumptionStatus.T] =
      Table(("x", "status"), (0, AssumptionStatus.ENABLED), (1, AssumptionStatus.DISABLED),
          (2, AssumptionStatus.DISABLED), (100, AssumptionStatus.DISABLED))

    forAll(valueAndStatusTable) { (valueOfX: Int, expectedStatus: AssumptionStatus.T) =>
      val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1))).toOption.get
      assert(service
            .assumeTransition(AssumeTransitionParams(sessionId = specResult.sessionId, transitionId = 0))
            .isRight, "Assuming transition 0 should succeed")
      assert(service.nextStep(NextStepParams(sessionId = specResult.sessionId)).isRight, "Next step should succeed")
      // parse equalities into JsonNode
      val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
      val equalitiesJson = mapper.readTree(s"""{ "x": { "#bigint": "$valueOfX" } }""")

      service.assumeState(AssumeStateParams(sessionId = specResult.sessionId, equalitiesJson)) match {
        case Right(AssumeStateResult(newSessionId, _, status)) =>
          assert(newSessionId == specResult.sessionId, "Session ID should remain the same after assuming state")
          assert(status == expectedStatus, s"Expected context status to be $expectedStatus, found $status")
        case Right(result) =>
          fail(s"Unexpected result: $result")
        case Left(error) =>
          fail(s"Failed to assume state: $error")
      }
    }
  }

  test("sequence 0-0-0 then query") {
    val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1), exports = List("View"))).toOption.get
    val sessionId = specResult.sessionId
    val t0 = AssumeTransitionParams(sessionId = sessionId, transitionId = 0, checkEnabled = true)
    for (_ <- 0 until 3) {
      assert(service.assumeTransition(t0).isRight)
      assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)
    }
    service
      .query(QueryParams(sessionId = sessionId, kinds = List(QueryKind.TRACE, QueryKind.OPERATOR),
              operator = "View")) match {
      case Right(QueryResult(newSessionId, trace, expr)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after querying")
        assert(expr.toString == """false""", "View should be false at x=3")
        assert(!trace.isNull, "Trace should not be empty")
        val states = trace.get("states")
        assert(states.size() == 3)
        assert(states.get(0).toString == """{"#meta":{"index":0},"x":{"#bigint":"0"}}""")
        assert(states.get(1).toString == """{"#meta":{"index":1},"x":{"#bigint":"1"}}""")
        assert(states.get(2).toString == """{"#meta":{"index":2},"x":{"#bigint":"2"}}""")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to query: $error")
    }
  }

  test("query to construct model") {
    val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1), exports = List("View"))).toOption.get
    val sessionId = specResult.sessionId
    service.query(QueryParams(sessionId = sessionId, kinds = List(QueryKind.TRACE))) match {
      case Right(QueryResult(newSessionId, trace, expr)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after querying")
        assert(expr.isNull, "Expr should be null")
        assert(!trace.isNull, "Trace should not be empty")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to query: $error")
    }
  }

  test("sequence 0-0-0 then nextModel x 2") {
    val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1), exports = List("View"))).toOption.get
    val sessionId = specResult.sessionId
    val t0 = AssumeTransitionParams(sessionId = sessionId, transitionId = 0, checkEnabled = true)
    for (_ <- 0 until 3) {
      assert(service.assumeTransition(t0).isRight)
      assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)
    }
    // the first call to nextModel gives us "false"
    service.nextModel(NextModelParams(sessionId = sessionId, operator = "View")) match {
      case Right(NextModelResult(newSessionId, oldValue, hasOld, hasNext)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after nextModel")
        assert(oldValue.toString == """false""", "View should be false at x=3")
        assert(hasOld == NextModelStatus.TRUE, "There is old model")
        assert(hasNext == NextModelStatus.FALSE, "There is no next model")

      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to query: $error")
    }
  }

  test("sequence 0-0-0-0-rollback-0-0-0-0") {
    val specResult = service.loadSpec(LoadSpecParams(sources = Seq(spec1))).toOption.get
    val sessionId = specResult.sessionId
    val params = AssumeTransitionParams(sessionId = sessionId, transitionId = 0, checkEnabled = true)
    // Init$0 is enabled, Next$0 is enabled 3 times
    for (_ <- 0 until 4) {
      service.assumeTransition(params) match {
        case Right(AssumeTransitionResult(newSessionId, _, transitionId, status)) =>
          assert(newSessionId == sessionId, "Session ID should remain the same after assuming transition")
          assert(transitionId == 0, "Transition ID should match the assumed transition")
          assert(status == AssumptionStatus.ENABLED, "Transition should be enabled")
          assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)

        case Left(error) =>
          fail(s"Failed to assume transition: $error")
      }
    }
    // We should not be able to assume transition 0 again
    service.assumeTransition(params) match {
      case Right(AssumeTransitionResult(newSessionId, _, transitionId, status)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after assuming transition")
        assert(transitionId == 0, "Transition ID should match the assumed transition")
        assert(status == AssumptionStatus.DISABLED, "Transition should be disabled")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to assume transition: $error")
    }
    // Now we roll back to the snapshot right after loading the spec.
    // As a result, we should be able to assume transition 0 four times again.
    // We have to be careful to recover the snapshot only once.
    val rollbackParams = RollbackParams(sessionId = sessionId, snapshotId = specResult.snapshotId)
    assert(service.rollback(rollbackParams).isRight, s"Rollback to ${specResult.snapshotId} should succeed")

    val paramsRecover = AssumeTransitionParams(sessionId = sessionId, transitionId = 0, checkEnabled = true)
    // Init$0
    assert(service.assumeTransition(paramsRecover).map(_.status == AssumptionStatus.ENABLED) == Right(true),
        "After recovery, transition 0 should be enabled")
    assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)
    // Next$0 three times
    for (i <- 1 until 4) {
      assert(service.assumeTransition(params).map(_.status == AssumptionStatus.ENABLED) == Right(true),
          s"Transition 0 is disabled when i=$i")
      assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)
    }
  }

  test("Inv3 is violated after Init but not after Init; Next$1") {
    val specResult = service
      .loadSpec(LoadSpecParams(sources = Seq(spec1), invariants = List("Inv1", "Inv2", "Inv3", "Inv4")))
      .toOption
      .get
    val sessionId = specResult.sessionId
    val init = AssumeTransitionParams(sessionId = sessionId, transitionId = 0, checkEnabled = true)
    val next1 = AssumeTransitionParams(sessionId = sessionId, transitionId = 1, checkEnabled = true)
    assert(service.assumeTransition(init).isRight)
    assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)
    // Inv3 is violated right after Init
    service.checkInvariant(CheckInvariantParams(sessionId = sessionId, invariantId = 2)) match {
      case Right(CheckInvariantResult(newSessionId, invariantStatus, traceNode)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after checking invariants")
        assert(invariantStatus == InvariantStatus.VIOLATED, "Inv3 should be violated")
        val states = traceNode.get("states")
        assert(states.size() == 1)
        assert(states.get(0).toString == """{"#meta":{"index":0},"x":{"#bigint":"0"}}""")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to check invariants: $error")
    }
    // Inv1 is not violated right after Init
    service.checkInvariant(CheckInvariantParams(sessionId = sessionId, invariantId = 0)) match {
      case Right(CheckInvariantResult(newSessionId, invariantStatus, trace)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after checking invariants")
        assert(invariantStatus == InvariantStatus.SATISFIED, "Inv1 should be violated")
        assert(trace.isNull, "There should be no trace when the invariant is satisfied")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to check invariants: $error")
    }
    // apply Next$1
    assert(service.assumeTransition(next1).isRight)
    assert(service.nextStep(NextStepParams(sessionId = sessionId)).isRight)
    // Inv3 is not violated after Next$1
    service.checkInvariant(CheckInvariantParams(sessionId = sessionId, invariantId = 2)) match {
      case Right(CheckInvariantResult(newSessionId, invariantStatus, trace)) =>
        assert(newSessionId == sessionId, "Session ID should remain the same after checking invariants")
        assert(invariantStatus == InvariantStatus.SATISFIED, "Inv3 should be satisfied")
        assert(trace.isNull, "There should be no trace when the invariant is satisfied")
      case Right(result) =>
        fail(s"Unexpected result: $result")
      case Left(error) =>
        fail(s"Failed to check invariants: $error")
    }
  }
}
