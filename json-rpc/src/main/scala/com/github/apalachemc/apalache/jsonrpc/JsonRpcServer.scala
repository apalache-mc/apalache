package com.github.apalachemc.apalache.jsonrpc

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options.Algorithm.Remote
import at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig
import at.forsyte.apalache.infra.passes.options.OptionGroup.{HasCheckerPreds, WithCheckerPreds}
import at.forsyte.apalache.infra.passes.options.SMTEncoding.OOPSLA19
import at.forsyte.apalache.infra.passes.options.{Config, SourceOption}
import at.forsyte.apalache.infra.tlc.config.InitNextSpec
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.io.itf.ItfJsonToTla
import at.forsyte.apalache.io.json.jackson.{JacksonRepresentation, ScalaFromJacksonAdapter}
import at.forsyte.apalache.io.lir.{ItfCounterexampleWriter, Trace}
import at.forsyte.apalache.tla.bmcmt.ModelCheckerContext
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import at.forsyte.apalache.tla.bmcmt.passes.BoundedCheckerPassImpl
import at.forsyte.apalache.tla.bmcmt.trex.IncrementalExecutionContextSnapshot
import at.forsyte.apalache.tla.bmcmt.util.TlaExUtil
import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.lir.TypedPredefs._
import com.fasterxml.jackson.databind.node.{NullNode, ObjectNode}
import com.fasterxml.jackson.databind.{JsonNode, ObjectMapper}
import com.fasterxml.jackson.module.scala.DefaultScalaModule
import com.google.inject.Injector
import com.typesafe.scalalogging.LazyLogging
import jakarta.servlet.annotation.WebServlet
import jakarta.servlet.http.{HttpServlet, HttpServletRequest, HttpServletResponse}
import org.eclipse.jetty.server.Server
import org.eclipse.jetty.servlet.{ServletContextHandler, ServletHolder}

import java.io.StringReader
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.locks.{Lock, ReentrantLock}
import java.util.concurrent.{LinkedBlockingQueue, ThreadPoolExecutor, TimeUnit}
import scala.collection.concurrent.TrieMap
import scala.collection.immutable
import scala.collection.immutable.SortedSet
import scala.util.Try

/**
 * An error that can occur in the exploration service.
 * @param code
 *   error code, typically a JSON-RPC error code
 * @param message
 *   a human-readable error message
 */
case class ServiceError(code: Int, message: String)

/**
 * A transition exploration service.
 * @param config
 *   the service configuration, typically, constructed with [[at.forsyte.apalache.io.ConfigManager]].
 *
 * @author
 *   Igor Konnov, 2025
 */
class ExplorationService(config: Try[Config.ApalacheConfig]) extends LazyLogging {
  // Guice injector instantiated for each session. This injector contains objects that are
  // configured via CheckerModule. Instead of doing model checking, it just prepares
  // ModelCheckerContext in the `remote` mode. We are using TrieMap to allow concurrent reads and updates.
  private val sessions: TrieMap[String, Injector] = TrieMap.empty
  // A lock for each session, to avoid concurrent access to the same context.
  private val sessionLocks: TrieMap[String, Lock] = TrieMap.empty
  // A counter for generating session IDs.
  private val lastSessionId: AtomicInteger = new AtomicInteger(0)
  // A snapshot manager.
  private val snapshots: CheckerSnapshotsPerSession = new CheckerSnapshotsPerSession()
  // Shared Jackson mapper for JSON serialization/deserialization.
  private val mapper: ObjectMapper = new ObjectMapper().registerModule(DefaultScalaModule)

  /**
   * A trivial health check.
   * @return
   *   `{ "status": "OK" }`
   */
  def health(): Either[ServiceError, ExplorationServiceResult] =
    Right(HealthCheckResult("OK"))

  /**
   * Loads a specification based on the provided parameters.
   * @param params
   *   parsed loading parameters
   * @return
   */
  def loadSpec(params: LoadSpecParams): Either[ServiceError, LoadSpecResult] = {
    val sessionId = lastSessionId.incrementAndGet().toHexString
    logger.info(s"Session $sessionId: Loading specification with ${params.sources.length} sources.")
    val options = createConfigFromParams(params).get
    // call the parser
    val passChainExecutor = PassChainExecutor(new CheckerModule(options))
    passChainExecutor.run() match {
      case Left(failure) =>
        Left(ServiceError(failure.exitCode, s"Failed to load specification: $failure"))

      case Right(_) =>
        // Successfully loaded the spec, we can access the module later
        sessions.put(sessionId, passChainExecutor.injector)
        sessionLocks.put(sessionId, new ReentrantLock())

        // get the singleton instance of BoundedModelCheckerPass from checker
        val checkerModule = passChainExecutor.injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        val checkerInput = checkerContext.checkerInput
        // initialize CONSTANTS
        checkerInput.constInitPrimed.foreach { expr =>
          checkerContext.trex.initializeConstants(expr)
        }
        // propagate constraints from ASSUME(...)
        checkerInput.rootModule.assumeDeclarations.foreach { d =>
          checkerContext.trex.assertState(d.body)
        }
        // save the snapshot of the checker context
        val snapshotId = snapshots.takeSnapshot(sessionId, checkerContext)

        // produce the specification parameters for remote exploration
        val specParameters = SpecParameters(
            initTransitions = checkerInput.initTransitions.zipWithIndex.map { case (e, i) =>
              SpecEntryMetadata(index = i, labels = SortedSet(TlaExUtil.findLabels(e): _*))
            },
            nextTransitions = checkerInput.nextTransitions.zipWithIndex.map { case (e, i) =>
              SpecEntryMetadata(index = i, labels = SortedSet(TlaExUtil.findLabels(e): _*))
            },
            stateInvariants = checkerInput.verificationConditions.stateInvariantsAndNegations.zipWithIndex.map {
              case ((e, _), i) => SpecEntryMetadata(index = i, labels = SortedSet(TlaExUtil.findLabels(e): _*))
            },
            actionInvariants = checkerInput.verificationConditions.actionInvariantsAndNegations.zipWithIndex.map {
              case ((e, _), i) => SpecEntryMetadata(index = i, labels = SortedSet(TlaExUtil.findLabels(e): _*))
            },
        )

        logger.info(s"Session=$sessionId Step=0 Snapshot=$snapshotId: Specification ready")

        Right(LoadSpecResult(sessionId, snapshotId, specParameters))
    }
  }

  /**
   * Dispose a previously loaded specification by its session ID.
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[DisposeSpecResult]]
   */
  def disposeSpec(params: DisposeSpecParams): Either[ServiceError, DisposeSpecResult] =
    sessions.get(params.sessionId) match {
      case Some(injector) =>
        // immediately remove the session, so the other threads would not start anything on it
        sessions.remove(params.sessionId)
        snapshots.remove(params.sessionId)
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext
        // lock on the checker context, so we do not access the SMT context concurrently
        withLock(params.sessionId) {
          checkerContext.foreach(_.trex.dispose())
        }
        sessionLocks.remove(params.sessionId)
        logger.info(s"Session ${params.sessionId}: Disposed.")
        Right(DisposeSpecResult(params.sessionId))

      case None =>
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: ${params.sessionId}"))
    }

  /**
   * Prepare a symbolic transition in the solver context.
   *
   * @param params
   *   the parameters object that contains the session ID and the transition ID
   * @return
   *   either an error or [[AssumeTransitionResult]]
   */
  def assumeTransition(params: AssumeTransitionParams): Either[ServiceError, AssumeTransitionResult] = {
    val sessionId = params.sessionId
    val transitionId = params.transitionId

    for {
      _ <- getCheckerContext(sessionId)
      _ <- Either.cond(transitionId >= 0, (),
          ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Invalid transition ID: $transitionId must be non-negative"))
      result <- withSessionLock(sessionId) { checkerContext =>
        // take a snapshot of the current context
        val snapshotBeforeId = snapshots.takeSnapshot(sessionId, checkerContext)
        // the step number might have changed after recovery, so we re-fetch the transitions
        val stepNo = checkerContext.trex.stepNo
        val transitions = if (stepNo == 0) {
          checkerContext.checkerInput.initTransitions
        } else {
          checkerContext.checkerInput.nextTransitions
        }
        if (transitionId < 0 || transitionId >= transitions.size) {
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                  s"Invalid transition ID: $transitionId not in [0, ${transitions.size})"))
        } else {
          val actionExpr = transitions(transitionId)
          // Upload the transition into the SMT context.
          // It returns the result of a simple check that does not check satisfiability.
          val isApplicable = checkerContext.trex.prepareTransition(transitionId, actionExpr)
          if (!isApplicable) {
            snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
            logger.info(
                s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: transition $transitionId DISABLED")
            Right(AssumeTransitionResult(sessionId, snapshotBeforeId, transitionId, AssumptionStatus.DISABLED))
          } else {
            // assume that this transition takes place
            checkerContext.trex.assumeTransition(transitionId)
            val snapshotAfterId = snapshots.takeSnapshot(sessionId, checkerContext)
            if (!params.checkEnabled) {
              // if we do not check satisfiability, we assume that the transition is enabled
              logger.info(
                  s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId UNKNOWN")
              Right(AssumeTransitionResult(sessionId, snapshotAfterId, transitionId, AssumptionStatus.UNKNOWN))
            } else {
              // check satisfiability
              Right(checkerContext.trex.sat(params.timeoutSec) match {
                case Some(isSat) =>
                  if (!isSat) {
                    snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
                  }
                  val status = if (isSat) AssumptionStatus.ENABLED else AssumptionStatus.DISABLED
                  val returnedSnapshotId = if (isSat) snapshotAfterId else snapshotBeforeId
                  logger.info(
                      s"Session=$sessionId Step=$stepNo Snapshot=$returnedSnapshotId: transition $transitionId $status")
                  AssumeTransitionResult(sessionId, returnedSnapshotId, transitionId, status)

                case None =>
                  // in case of timeout or unknown, we do not roll back the context, but return unknown
                  logger.info(
                      s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId UNKNOWN")
                  AssumeTransitionResult(sessionId, snapshotAfterId, transitionId, AssumptionStatus.UNKNOWN)
              })
            }
          }
        }
      }
    } yield result
  }

  /**
   * Rollback to a previously saved snapshot.
   *
   * @param params
   *   the parameters object that contains the session ID and the snapshot ID
   * @return
   *   either an error or [[RollbackResult]]
   */
  def rollback(params: RollbackParams): Either[ServiceError, RollbackResult] =
    withSessionLock(params.sessionId) { checkerContext =>
      val recovered = snapshots.recoverSnapshot(params.sessionId, checkerContext, params.snapshotId)
      if (recovered) {
        Right(RollbackResult(params.sessionId, params.snapshotId))
      } else {
        Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                s"Snapshot not found: ${params.snapshotId} in session ${params.sessionId}"))
      }
    }

  /**
   * Compact the current symbolic trace by extracting the last concrete state, reverting to a given snapshot, and
   * asserting the extracted state values as equality constraints.
   *
   * This effectively replaces a long symbolic trace with a single concrete state, resetting the solver complexity.
   *
   * @param params
   *   the parameters object that contains the session ID, the snapshot ID to revert to, and the timeout
   * @return
   *   either an error or [[CompactResult]]
   */
  def compact(params: CompactParams): Either[ServiceError, CompactResult] = {
    val sessionId = params.sessionId

    for {
      checkerContext <- getCheckerContext(sessionId)
      varTypes = checkerContext.checkerInput.rootModule.varDeclarations
        .map(d => d.name -> d.typeTag.asTlaType1())
        .toMap
      result <- withSessionLock(sessionId) { checkerContext =>
        // 1. Ensure the current context is satisfiable so we can decode a model
        checkerContext.trex.sat(params.timeoutSec) match {
          case Some(false) =>
            Left(ServiceError(JsonRpcCodes.INTERNAL_ERROR, "Cannot compact: current context is unsatisfiable"))

          case None =>
            Left(ServiceError(JsonRpcCodes.INTERNAL_ERROR,
                    "Cannot compact: satisfiability check timed out or returned unknown"))

          case Some(true) =>
            // 2. Decode the execution and extract the last state
            val decodedPath = checkerContext.trex.decodedExecution().path
            if (decodedPath.isEmpty) {
              Left(ServiceError(JsonRpcCodes.INTERNAL_ERROR, "Cannot compact: decoded execution path is empty"))
            } else {
              val lastState = decodedPath.last.assignments

              // 3. Revert to the given snapshot
              val recovered = snapshots.recoverSnapshot(sessionId, checkerContext, params.snapshotId)
              if (!recovered) {
                Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                        s"Snapshot not found: ${params.snapshotId} in session $sessionId"))
              } else {
                // 4. Build a synthetic transition that assigns each state variable to its decoded value.
                //    This creates proper variable bindings via the standard prepareTransition flow,
                //    unlike assertState which requires existing bindings.
                val assignmentExprs = lastState.map { case (varName, valueExpr) =>
                  tla.assign(tla.prime(tla.name(varName, varTypes(varName))), tla.unchecked(valueExpr))
                }.toSeq
                val syntheticTransition = tla.and(assignmentExprs: _*).build

                checkerContext.trex.prepareTransition(0, syntheticTransition)
                checkerContext.trex.assumeTransition(0)
                checkerContext.trex.nextState()

                // 5. Take a new snapshot
                val newSnapshotId = snapshots.takeSnapshot(sessionId, checkerContext)
                logger.info(
                    s"Session=$sessionId Snapshot=$newSnapshotId: Compacted trace by reverting to ${params.snapshotId}")

                Right(CompactResult(sessionId, newSnapshotId))
              }
            }
        }
      }
    } yield result
  }

  /**
   * Switch to the next step.
   *
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[NextStepResult]]
   */
  def nextStep(params: NextStepParams): Either[ServiceError, NextStepResult] =
    withSessionLock(params.sessionId) { checkerContext =>
      val stepBeforeNo = checkerContext.trex.stepNo
      checkerContext.trex.nextState()
      val stepAfterNo = checkerContext.trex.stepNo
      val snapshotId = snapshots.takeSnapshot(params.sessionId, checkerContext)
      logger.info(
          s"Session=${params.sessionId} Step=$stepAfterNo Snapshot=$snapshotId: Switched from step $stepBeforeNo")
      Right(NextStepResult(params.sessionId, snapshotId, stepAfterNo))
    }

  /**
   * Assume state constraints in the solver context.
   *
   * @param params
   *   the parameters object that contains the session ID and the transition ID
   * @return
   *   either an error or [[AssumeStateResult]]
   */
  def assumeState(params: AssumeStateParams): Either[ServiceError, AssumeStateResult] = {
    val sessionId = params.sessionId

    for {
      checkerContext <- getCheckerContext(sessionId)
      // parse the JSON value into a state
      varTypes = checkerContext.checkerInput.rootModule.varDeclarations
        .map(d => d.name -> d.typeTag.asTlaType1())
        .toMap
      equalities <- new ItfJsonToTla(ScalaFromJacksonAdapter)
        .parseState(varTypes, new JacksonRepresentation(params.equalities))
        .left
        .map(msg => ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Failed to parse the state: $msg"))
      result <- withSessionLock(sessionId) { checkerContext =>
        // take a snapshot of the current context
        val snapshotBeforeId = snapshots.takeSnapshot(sessionId, checkerContext)
        // upload the equalities into the SMT context
        equalities.foreach { case (varName, valueExpr) =>
          checkerContext.trex.assertState(tla.eql(tla.name(varName, varTypes(varName)), tla.unchecked(valueExpr)).build)
        }
        // take a snapshot after assuming the state
        val snapshotAfterId = snapshots.takeSnapshot(sessionId, checkerContext)
        // check whether the context is still satisfiable
        val stepNo = checkerContext.trex.stepNo
        if (!params.checkEnabled) {
          // if we do not check satisfiability, we assume that the transition is enabled
          logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: assumeState UNKNOWN")
          Right(AssumeStateResult(sessionId, snapshotAfterId, AssumptionStatus.UNKNOWN))
        } else {
          // check satisfiability
          Right(checkerContext.trex.sat(params.timeoutSec) match {
            case Some(isSat) =>
              if (!isSat) {
                snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
              }
              val status = if (isSat) AssumptionStatus.ENABLED else AssumptionStatus.DISABLED
              val returnedSnapshotId = if (isSat) snapshotAfterId else snapshotBeforeId
              logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$returnedSnapshotId: assumeState $status")
              AssumeStateResult(sessionId, returnedSnapshotId, status)

            case None =>
              // in case of timeout or unknown, we do not roll back the context, but return unknown
              logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: assumeState UNKNOWN")
              AssumeStateResult(sessionId, snapshotAfterId, AssumptionStatus.UNKNOWN)
          })
        }
      }
    } yield result
  }

  /**
   * Check the invariants against the current SMT context.
   * @param params
   *   checking parameters
   * @return
   *   either an error or the checking result
   */
  def checkInvariant(params: CheckInvariantParams): Either[ServiceError, CheckInvariantResult] = {
    val sessionId = params.sessionId
    val invariantId = params.invariantId

    for {
      checkerContext <- getCheckerContext(sessionId)
      // check the invariant IDs, so we don't have to waste compute on obvious errors
      _ <- {
        val nStateInvs = checkerContext.checkerInput.verificationConditions.stateInvariantsAndNegations.size
        val nActionInvs = checkerContext.checkerInput.verificationConditions.actionInvariantsAndNegations.size
        if (params.kind == InvariantKind.STATE && invariantId >= nStateInvs) {
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                  s"Invalid invariant ID: state invariant $invariantId not in [0, $nStateInvs)"))
        } else if (params.kind == InvariantKind.ACTION && invariantId >= nActionInvs) {
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                  s"Invalid invariant ID: action invariant $invariantId not in [0, $nActionInvs)"))
        } else {
          Right(())
        }
      }
      result <- withSessionLock(sessionId) { checkerContext =>
        // take a snapshot of the current context
        val snapshotBeforeId = snapshots.takeSnapshot(sessionId, checkerContext)
        // if it's too early to check a state or action invariant, return SATISFIED
        val stepNo = checkerContext.trex.stepNo
        if (stepNo == 0 || (stepNo == 1 && params.kind == InvariantKind.ACTION)) {
          // stepNo == 0 => Init has not been applied, so no state invariant can be violated
          // stepNo == 1 => only Init has been applied, so no action invariant can be violated
          logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: invariant $invariantId SATISFIED")
          Right(CheckInvariantResult(sessionId, InvariantStatus.SATISFIED, NullNode.getInstance()))
        } else {
          // extract the corresponding invariant negation
          val notInvExpr = params.kind match {
            case InvariantKind.STATE =>
              checkerContext.checkerInput.verificationConditions.stateInvariantsAndNegations(invariantId)._2
            case InvariantKind.ACTION =>
              checkerContext.checkerInput.verificationConditions.actionInvariantsAndNegations(invariantId)._2
          }
          // assert the negation of the invariant
          checkerContext.trex.assertState(notInvExpr)
          // ...and check whether the negation is satisfiable
          val (status, jsonTrace) = checkerContext.trex.sat(params.timeoutSec) match {
            case Some(true)  => (InvariantStatus.VIOLATED, getTraceInJson(checkerContext, params.timeoutSec))
            case Some(false) => (InvariantStatus.SATISFIED, NullNode.getInstance())
            case None        => (InvariantStatus.UNKNOWN, NullNode.getInstance())
          }
          // recover the snapshot
          snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
          logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: invariant $invariantId $status")
          Right(CheckInvariantResult(sessionId, status, jsonTrace))
        }
      }
    } yield result
  }

  /**
   * Query for values.
   *
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[QueryResult]]
   */
  def query(params: QueryParams): Either[ServiceError, QueryResult] =
    withSessionLock(params.sessionId) { checkerContext =>
      val traceInJson =
        if (params.kinds.contains(QueryKind.TRACE)) getTraceInJson(checkerContext, params.timeoutSec)
        else NullNode.getInstance()
      val stateInJson =
        if (params.kinds.contains(QueryKind.STATE)) getLastStateInJson(checkerContext, params.timeoutSec)
        else NullNode.getInstance()
      for {
        viewInJson <-
          if (!params.kinds.contains(QueryKind.OPERATOR)) Right(NullNode.getInstance(): JsonNode)
          else
            getViewInJson(checkerContext, params.operator, params.timeoutSec).left.map(msg =>
              ServiceError(JsonRpcCodes.INTERNAL_ERROR, msg))
      } yield QueryResult(params.sessionId, trace = traceInJson, state = stateInJson, operatorValue = viewInJson)
    }

  /**
   * Try switching to the next model, if it exists.
   *
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[NextModelResult]]
   */
  def nextModel(params: NextModelParams): Either[ServiceError, NextModelResult] =
    withSessionLock(params.sessionId) { checkerContext =>
      findOperator(checkerContext, params.operator).left
        .map(msg => ServiceError(JsonRpcCodes.INVALID_PARAMS, msg))
        .map { decl =>
          checkerContext.trex.evaluate(params.timeoutSec, decl.body) match {
            case None =>
              // the current context is UNSAT (or timed out)
              NextModelResult(params.sessionId, oldValue = NullNode.instance, hasOld = NextModelStatus.FALSE,
                  hasNext = NextModelStatus.FALSE)

            case Some(oldTlaExpr) =>
              val assertion = tla.not(tla.eql(tla.unchecked(decl.body), tla.unchecked(oldTlaExpr))).build
              checkerContext.trex.assertState(assertion)
              val hasNext = checkerContext.trex
                .sat(params.timeoutSec)
                .map(isSat => if (isSat) NextModelStatus.TRUE else NextModelStatus.FALSE)
                .getOrElse(NextModelStatus.UNKNOWN)

              // Serialize the old operator value to JSON
              val oldValueInJson = ujsonToJackson(ItfCounterexampleWriter.exprToJson(oldTlaExpr))
              NextModelResult(params.sessionId, oldValue = oldValueInJson, hasOld = NextModelStatus.TRUE,
                  hasNext = hasNext)
          }
        }
    }

  /**
   * Execute a sequence of stateful operations under a single session lock.
   *
   * @param params
   *   apply-in-order parameters
   * @return
   *   ordered per-step results; execution stops at the first failing step
   */
  def applyInOrder(params: ApplyInOrderParams): Either[ServiceError, ApplyInOrderResult] = {
    val parser = new JsonParameterParser(mapper)
    val sessionId = params.sessionId

    withSessionLock(sessionId) { _ =>
      // Process steps sequentially, stopping at the first failure.
      val callResults = params.calls.foldLeft(List.empty[ApplyInOrderCallResult]) { (acc, call) =>
        // If a previous call failed, skip remaining calls and return the accumulated results.
        if (acc.exists(!_.ok)) {
          acc
        } else {
          val paramsNode = call.params.deepCopy[JsonNode]()
          paramsNode.asInstanceOf[ObjectNode].put("sessionId", sessionId)
          val oneCallResult = dispatchStep(parser, call.method, paramsNode) match {
            case Left(error) =>
              val errorNode = mapper.createObjectNode()
              errorNode.put("code", error.code)
              errorNode.put("message", error.message)
              ApplyInOrderCallResult(ok = false, method = call.method, error = errorNode)
            case Right(result) =>
              ApplyInOrderCallResult(
                  ok = true,
                  method = call.method,
                  result = mapper.valueToTree[JsonNode](result),
              )
          }
          acc :+ oneCallResult
        }
      }

      Right(ApplyInOrderResult(callResults))
    }
  }

  private def dispatchStep(
      parser: JsonParameterParser,
      method: String,
      paramsNode: JsonNode): Either[ServiceError, ExplorationServiceResult] = {

    def dispatch[P](
        parse: JsonNode => Either[String, P]
      )(handle: P => Either[ServiceError,
            _ <: ExplorationServiceResult]): Either[ServiceError, ExplorationServiceResult] =
      parse(paramsNode).left
        .map(msg => ServiceError(JsonRpcCodes.INVALID_PARAMS, msg))
        .flatMap(handle)

    method match {
      case "assumeTransition" => dispatch(parser.parseAssumeTransition)(assumeTransition)
      case "assumeState"      => dispatch(parser.parseAssumeState)(assumeState)
      case "nextStep"         => dispatch(parser.parseNextStep)(nextStep)
      case "query"            => dispatch(parser.parseQuery)(query)
      case "checkInvariant"   => dispatch(parser.parseCheckInvariant)(checkInvariant)
      case "nextModel"        => dispatch(parser.parseNextModel)(nextModel)
      case "rollback"         => dispatch(parser.parseRollback)(rollback)
      case "compact"          => dispatch(parser.parseCompact)(compact)
      case _ => Left(ServiceError(JsonRpcCodes.INVALID_REQUEST, s"Unsupported applyInOrder method: $method"))
    }
  }

  /**
   * Extract a trace from the transition executor and serialize it to Jackson JSON.
   *
   * @return
   *   a JSON-encoded trace
   */
  private def getTraceInJson(
      checkerContext: ModelCheckerContext[IncrementalExecutionContextSnapshot],
      timeoutSec: Int): JsonNode =
    checkerContext.trex.sat(timeoutSec) match {
      case Some(true) =>
        // extract the trace
        // We do not extract any labels. The remote client should be able to reconstruct them from the transition IDs,
        // as reported by loadSpec.
        val path = checkerContext.trex.decodedExecution().path
        val counterexample = Trace(checkerContext.checkerInput.rootModule, path.map(_.assignments).toIndexedSeq,
            path.map(_ => SortedSet[String]()).toIndexedSeq, ())
        // Serialize the counterexample to JSON
        val ujsonTrace =
          ItfCounterexampleWriter.mkJson(checkerContext.checkerInput.rootModule, counterexample.states)
        ujsonToJackson(ujsonTrace)

      case _ =>
        // no trace or unknown
        NullNode.getInstance()
    }

  /**
   * Extract only the last state from the transition executor and serialize it to Jackson JSON.
   *
   * @return
   *   a JSON-encoded last state
   */
  private def getLastStateInJson(
      checkerContext: ModelCheckerContext[IncrementalExecutionContextSnapshot],
      timeoutSec: Int): JsonNode =
    checkerContext.trex.sat(timeoutSec) match {
      case Some(true) =>
        val path = checkerContext.trex.decodedExecution().path
        val counterexample = Trace(checkerContext.checkerInput.rootModule, path.map(_.assignments).toIndexedSeq,
            path.map(_ => SortedSet[String]()).toIndexedSeq, ())
        if (counterexample.states.isEmpty) {
          NullNode.getInstance()
        } else {
          // Merge constInit and varInit for the first state, consistent with mkJson
          val state0 = counterexample.states match {
            case constInit +: Seq()          => constInit
            case constInit +: initState +: _ => constInit ++ initState
            case _                           => Map.empty[String, at.forsyte.apalache.tla.lir.TlaEx]
          }
          val mappedStates = state0 +: counterexample.states.drop(2)
          val lastIndex = mappedStates.length - 1
          val ujsonState = ItfCounterexampleWriter.stateToJson(mappedStates.last, lastIndex)
          ujsonToJackson(ujsonState)
        }

      case _ =>
        NullNode.getInstance()
    }

  private def getViewInJson(
      checkerContext: ModelCheckerContext[IncrementalExecutionContextSnapshot],
      operatorName: String,
      timeoutSec: Int): Either[String, JsonNode] =
    findOperator(checkerContext, operatorName).flatMap { decl =>
      checkerContext.trex.evaluate(timeoutSec, decl.body) match {
        case None =>
          val msg = s"Failed to evaluate $operatorName within $timeoutSec seconds"
          logger.warn(msg)
          Left(msg)

        case Some(tlaExpr) =>
          Right(ujsonToJackson(ItfCounterexampleWriter.exprToJson(tlaExpr)))
      }
    }

  private def findOperator(
      checkerContext: ModelCheckerContext[IncrementalExecutionContextSnapshot],
      name: String): Either[String, TlaOperDecl] =
    checkerContext.checkerInput.persistentDecls.get(name) match {
      case None =>
        val msg = s"Operator not found: $name"
        logger.warn(msg)
        Left(msg)

      case Some(decl) if decl.formalParams.nonEmpty =>
        val msg = s"Operators with arguments are not supported yet: $name has ${decl.formalParams.size} parameters"
        logger.warn(msg)
        Left(msg)

      case Some(decl) =>
        Right(decl)
    }

  /**
   * Produce a configuration from the parameters of the loadSpec method.
   * @param params
   *   specification parameters
   * @return
   *   the configuration for spawning a CheckerModule
   */
  private def createConfigFromParams(params: LoadSpecParams): Try[HasCheckerPreds] = {
    // pack the sources into the config
    val source = SourceOption.StringSource(params.sources.head, params.sources.tail)
    val input = config.get.input.copy(source = Some(source))
    val configWithInput = config.get.copy(input = input, output = config.get.output.copy(output = None))
    WithCheckerPreds(configWithInput)
      .map { cfg =>
        // We do not need to set the checker options, as we do not run the model checker.
        // We just prepare the context for the remote mode.
        // Most of the options are irrelevant, as the remote algorithm does its own exploration.
        cfg.copy(
            checker = cfg.checker.copy(
                algo = Remote,
                smtEncoding = OOPSLA19,
                // TODO: propagate the tuning options from LoadSpecParams
                tuning = immutable.Map[String, String](),
                discardDisabled = false,
                noDeadlocks = true,
                maxError = 1,
                // TODO: propagate from LoadSpecParams
                timeoutSmtSec = 0,
            ),
            // TODO: add other options
            predicates = cfg.predicates.copy(
                behaviorSpec = InitNextSpec(params.init, params.next),
                invariants = params.invariants,
                persistent = params.exports,
            ),
        )
      }
  }

  /** Convert a UJSON value to Jackson's JsonNode. */
  private def ujsonToJackson(ujsonValue: ujson.Value): JsonNode =
    mapper.readTree(new StringReader(ujsonValue.render()))

  /** Look up the session's checker context, or return a ServiceError. */
  private def getCheckerContext(
      sessionId: String): Either[ServiceError, ModelCheckerContext[IncrementalExecutionContextSnapshot]] =
    sessions.get(sessionId) match {
      case Some(injector) =>
        Right(injector.getInstance(classOf[BoundedCheckerPassImpl]).modelCheckerContext.get)
      case None =>
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: $sessionId"))
    }

  /**
   * Acquire the session lock, re-validate the session, retrieve the checker context, and execute the callback. This
   * eliminates the repeated validate-lock-revalidate pattern.
   */
  private def withSessionLock[T](
      sessionId: String
    )(callback: ModelCheckerContext[IncrementalExecutionContextSnapshot] => Either[ServiceError,
          T]): Either[ServiceError, T] =
    for {
      _ <- getCheckerContext(sessionId) // validate session exists before locking
      result <- withLock(sessionId) {
        // re-validate after acquiring the lock (session may have been disposed concurrently)
        getCheckerContext(sessionId).flatMap(callback)
      }
    } yield result

  // call the callback under the lock for the given session ID
  private def withLock[T](sessionId: String)(callback: => T): T = {
    val lock = sessionLocks(sessionId)
    lock.lock()
    try {
      callback
    } finally {
      lock.unlock()
    }
  }
}

/**
 * A simple JSON-RPC servlet that handles requests for the exploration service.
 * @param service
 *   exploration service that processes the exploration logic
 */
@WebServlet(urlPatterns = Array("/rpc"), asyncSupported = true)
class JsonRpcServlet(service: ExplorationService) extends HttpServlet with LazyLogging {

  /** The maximum number of threads to allow in the pool */
  private val MAX_POOL_SIZE = 1024

  /**
   * When the number of threads is greater than the core, this is the maximum time that excess idle threads will wait
   * for new tasks before terminating.
   */
  private val KEEP_ALIVE_SEC = 60L

  // Our own bounded pool, to avoid blocking Jetty threads
  private val executor = new ThreadPoolExecutor(
      // The core pool size is about the number of the logical cores.
      // Since most tasks are CPU-bound (z3), we do not need more threads.
      Runtime.getRuntime.availableProcessors(),
      MAX_POOL_SIZE,
      KEEP_ALIVE_SEC,
      TimeUnit.SECONDS,
      new LinkedBlockingQueue[Runnable](MAX_POOL_SIZE),
      (r: Runnable) => {
        val t = new Thread(r, "rpc-compute-pool")
        t.setDaemon(true)
        t
      },
  )
  logger.info(s"Created thread pool with core pool size ${Runtime.getRuntime.availableProcessors()}, " +
    s"max pool size $MAX_POOL_SIZE, keep alive $KEEP_ALIVE_SEC sec")
  // data mapper for JSON serialization/deserialization
  // using Jackson with Scala module for better compatibility with case classes
  private val mapper = new ObjectMapper().registerModule(DefaultScalaModule)

  override def doPost(req: HttpServletRequest, resp: HttpServletResponse): Unit = {
    // Start an asynchronous task, as some of the SMT-related requests may take hours:
    val async = req.startAsync
    async.setTimeout(0) // 0 = no timeout
    val runnable: Runnable = () => {
      try {
        val responseJson = processRequest(req)
        resp.setContentType("application/json")
        val writer = resp.getWriter
        mapper.writeValue(writer, responseJson)
        writer.flush()
      } catch {
        case ex: Exception =>
          logger.error("Failed to process the request", ex)
          resp.setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR)
      } finally {
        async.complete()
      }
    }
    // submit the task to our pool, so Jetty can continue serving other requests
    executor.submit(runnable)
  }

  private def processRequest(req: HttpServletRequest): ObjectNode = {
    val requestJson = mapper.readTree(req.getInputStream)
    val method = requestJson.path("method").asText()
    val paramsNode = requestJson.path("params")
    val id = requestJson.path("id")
    val parser = new JsonParameterParser(mapper)

    // Build JSON-RPC response
    val responseJson = mapper.createObjectNode()
    responseJson.put("jsonrpc", "2.0")
    responseJson.set("id", id)

    def dispatch[P](
        parse: JsonNode => Either[String, P]
      )(handle: P => Either[ServiceError,
            _ <: ExplorationServiceResult]): Either[ServiceError, ExplorationServiceResult] =
      parse(paramsNode).left
        .map(msg => ServiceError(JsonRpcCodes.INVALID_PARAMS, msg))
        .flatMap(handle)

    val errorOrResult: Either[ServiceError, ExplorationServiceResult] =
      try {
        method match {
          case "health"           => service.health()
          case "loadSpec"         => dispatch(parser.parseLoadSpec)(service.loadSpec)
          case "disposeSpec"      => dispatch(parser.parseDisposeSpec)(service.disposeSpec)
          case "rollback"         => dispatch(parser.parseRollback)(service.rollback)
          case "assumeTransition" => dispatch(parser.parseAssumeTransition)(service.assumeTransition)
          case "assumeState"      => dispatch(parser.parseAssumeState)(service.assumeState)
          case "nextStep"         => dispatch(parser.parseNextStep)(service.nextStep)
          case "checkInvariant"   => dispatch(parser.parseCheckInvariant)(service.checkInvariant)
          case "query"            => dispatch(parser.parseQuery)(service.query)
          case "nextModel"        => dispatch(parser.parseNextModel)(service.nextModel)
          case "compact"          => dispatch(parser.parseCompact)(service.compact)
          case "applyInOrder"     => dispatch(parser.parseApplyInOrder)(service.applyInOrder)
          case _                  => Left(ServiceError(JsonRpcCodes.METHOD_NOT_FOUND, s"Method not found: $method"))
        }
      } catch {
        case ex: Exception =>
          Left(ServiceError(JsonRpcCodes.INTERNAL_ERROR, s"Internal error: ${ex.getMessage}"))
      }

    errorOrResult match {
      case Left(error)   => responseJson.set[JsonNode]("error", mapper.valueToTree[JsonNode](error))
      case Right(result) => responseJson.set[JsonNode]("result", mapper.valueToTree[JsonNode](result))
    }

    responseJson
  }
}

object JsonRpcServerApp {
  def run(config: Try[ApalacheConfig], port: Int): Unit = {
    val server = new Server(port)
    val context = new ServletContextHandler(ServletContextHandler.SESSIONS)
    context.setContextPath("/")
    server.setHandler(context)

    val service = new ExplorationService(config)
    context.addServlet(new ServletHolder(new JsonRpcServlet(service)), "/rpc")

    server.start()
    println(s"JSON-RPC server running on http://localhost:$port/rpc")
    server.join()
  }

  def main(args: Array[String]): Unit = {
    val port = if (args.nonEmpty) args(0).toInt else 8822
    val cfg = ConfigManager("{common.command: 'server'}")
    run(cfg, port)
  }
}
