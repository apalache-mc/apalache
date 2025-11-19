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
import java.net.InetSocketAddress
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
        return Left(ServiceError(failure.exitCode, s"Failed to load specification: $failure"))
      case Right(_) =>
        // Successfully loaded the spec, we can access the module later
        sessions.put(sessionId, passChainExecutor.injector)
        sessionLocks.put(sessionId, new ReentrantLock())
    }
    // get the singleton instance of BoundedModelCheckerPass from checker
    val checkerModule = passChainExecutor.injector.getInstance(classOf[BoundedCheckerPassImpl])
    val checkerContext = checkerModule.modelCheckerContext.get
    val checkerInput = checkerContext.checkerInput
    // initialize CONSTANTS
    if (checkerContext.checkerInput.constInitPrimed.isDefined) {
      checkerContext.trex.initializeConstants(checkerContext.checkerInput.constInitPrimed.get)
    }
    // propagate constraints from ASSUME(...)
    checkerContext.checkerInput.rootModule.assumeDeclarations.foreach { d =>
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

  /**
   * Dispose a previously loaded specification by its session ID.
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[DisposeSpecResult]]
   */
  def disposeSpec(params: DisposeSpecParams): Either[ServiceError, DisposeSpecResult] = {
    val result =
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

    result
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
    // validate the input parameters
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        // we can only check obvious issues with transition ID here, as the step number
        // may change after snapshot recovery
        if (transitionId < 0) {
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Invalid transition ID: $transitionId must be non-negative"))
        } else {
          Right(checkerContext)
        }

      case None =>
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: $sessionId"))
    }

    // Prepare the transition. Make sure that we do not update the SMT context concurrently.
    validationResult
      .map { checkerContext =>
        withLock(params.sessionId) {
          if (!sessions.contains(params.sessionId)) {
            return Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND,
                    s"Session not found: ${params.sessionId}"))
          }
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
            return Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                    s"Invalid transition ID: $transitionId not in [0, ${transitions.size})"))
          }
          val actionExpr = transitions(transitionId)
          // Upload the transition into the SMT context.
          // It returns the result of a simple check that does not check satisfiability.
          val isApplicable = checkerContext.trex.prepareTransition(transitionId, actionExpr)
          if (!isApplicable) {
            snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
            logger.info(
                s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: transition $transitionId DISABLED")
            AssumeTransitionResult(sessionId, snapshotBeforeId, transitionId, AssumptionStatus.DISABLED)
          } else {
            // assume that this transition takes place
            checkerContext.trex.assumeTransition(transitionId)
            val snapshotAfterId = snapshots.takeSnapshot(sessionId, checkerContext)
            if (!params.checkEnabled) {
              // if we do not check satisfiability, we assume that the transition is enabled
              logger.info(
                  s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId UNKNOWN")
              AssumeTransitionResult(sessionId, snapshotAfterId, transitionId, AssumptionStatus.UNKNOWN)
            } else {
              // check satisfiability
              checkerContext.trex.sat(params.timeoutSec) match {
                case Some(isSat) =>
                  if (!isSat) {
                    snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
                  }
                  val status = if (isSat) AssumptionStatus.ENABLED else AssumptionStatus.DISABLED
                  val returnedSnapshotId = if (!isSat) snapshotBeforeId else snapshotAfterId
                  logger.info(
                      s"Session=$sessionId Step=$stepNo Snapshot=$returnedSnapshotId: transition $transitionId $status")
                  AssumeTransitionResult(sessionId, returnedSnapshotId, transitionId, status)
                case None =>
                  // in case of timeout or unknown, we do not roll back the context, but return unknown
                  logger.info(
                      s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: transition $transitionId UNKNOWN")
                  AssumeTransitionResult(sessionId, snapshotAfterId, transitionId, AssumptionStatus.UNKNOWN)
              }
            }
          }
        }
      }
  }

  /**
   * Rollback to a previously saved snapshot.
   *
   * @param params
   *   the parameters object that contains the session ID and the snapshot ID
   * @return
   *   either an error or [[RollbackResult]]
   */
  def rollback(params: RollbackParams): Either[ServiceError, RollbackResult] = {
    val sessionId = params.sessionId
    // validate the input parameters
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        Right(checkerContext)

      case None =>
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: $sessionId"))
    }

    // Perform a rollback.
    validationResult
      .flatMap { checkerContext =>
        withLock(params.sessionId) {
          if (!sessions.contains(params.sessionId)) {
            return Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND,
                    s"Session not found: ${params.sessionId}"))
          }
          // try to recover the snapshot
          val recovered = snapshots.recoverSnapshot(sessionId, checkerContext, params.snapshotId)
          if (recovered) {
            Right(RollbackResult(sessionId, params.snapshotId))
          } else {
            Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                    s"Snapshot not found: ${params.snapshotId} in session $sessionId"))
          }
        }
      }
  }

  /**
   * Switch to the next step.
   *
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[NextStepResult]]
   */
  def nextStep(params: NextStepParams): Either[ServiceError, NextStepResult] = {
    val sessionId = params.sessionId
    // validate the input parameters under the global lock
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        Right(checkerContext)

      case None =>
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: $sessionId"))
    }

    // Roll to the next step. Make sure that we do not update the SMT context concurrently.
    withLock(params.sessionId) {
      validationResult
        .map { checkerContext =>
          {
            if (!sessions.contains(params.sessionId)) {
              return Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND,
                      s"Session not found: ${params.sessionId}"))
            }
            val stepBeforeNo = checkerContext.trex.stepNo
            checkerContext.trex.nextState()
            val stepAfterNo = checkerContext.trex.stepNo
            val snapshotId = snapshots.takeSnapshot(sessionId, checkerContext)
            logger.info(s"Session=$sessionId Step=$stepAfterNo Snapshot=$snapshotId: Switched from step $stepBeforeNo")
            NextStepResult(sessionId, snapshotId, stepAfterNo)
          }
        }
    }
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
    // validate the input parameters
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        // parse the JSON value into a state
        val varTypes =
          checkerContext.checkerInput.rootModule.varDeclarations
            .map(d => d.name -> d.typeTag.asTlaType1())
            .toMap
        new ItfJsonToTla(ScalaFromJacksonAdapter)
          .parseState(varTypes, new JacksonRepresentation(params.equalities)) match {
          case Right(equalities) =>
            Right((checkerContext, varTypes, equalities))
          case Left(msg) =>
            Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, s"Failed to parse the state: $msg"))
        }

      case None =>
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: $sessionId"))
    }

    // Upload the equalities. Make sure that we do not update the SMT context concurrently.
    validationResult
      .map { case (checkerContext, varTypes, equalities) =>
        withLock(params.sessionId) {
          if (!sessions.contains(params.sessionId)) {
            return Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND,
                    s"Session not found: ${params.sessionId}"))
          }
          // take a snapshot of the current context
          val snapshotBeforeId = snapshots.takeSnapshot(sessionId, checkerContext)
          // upload the equalities into the SMT context
          for ((varName, valueExpr) <- equalities) {
            checkerContext.trex.assertState(
                tla.eql(tla.name(varName, varTypes(varName)), tla.unchecked(valueExpr)).build)
          }
          // take a snapshot after assuming the state
          val snapshotAfterId = snapshots.takeSnapshot(sessionId, checkerContext)
          // check whether the context is still satisfiable
          val stepNo = checkerContext.trex.stepNo
          if (!params.checkEnabled) {
            // if we do not check satisfiability, we assume that the transition is enabled
            logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: assumeState UNKNOWN")
            AssumeStateResult(sessionId, snapshotAfterId, AssumptionStatus.UNKNOWN)
          } else {
            // check satisfiability
            checkerContext.trex.sat(params.timeoutSec) match {
              case Some(isSat) =>
                if (!isSat) {
                  snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
                }
                val status = if (isSat) AssumptionStatus.ENABLED else AssumptionStatus.DISABLED
                val returnedSnapshotId = if (!isSat) snapshotBeforeId else snapshotAfterId
                logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$returnedSnapshotId: assumeState $status")
                AssumeStateResult(sessionId, returnedSnapshotId, status)

              case None =>
                // in case of timeout or unknown, we do not roll back the context, but return unknown
                logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotAfterId: assumeState UNKNOWN")
                AssumeStateResult(sessionId, snapshotAfterId, AssumptionStatus.UNKNOWN)
            }
          }
        }
      }
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
    // validate the input parameters
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        // check the invariant IDs, so we don't have to waste compute on obvious errors
        val nStateInvs = checkerContext.checkerInput.verificationConditions.stateInvariantsAndNegations.size
        val nActionInvs = checkerContext.checkerInput.verificationConditions.actionInvariantsAndNegations.size
        if (params.kind == InvariantKind.STATE && invariantId >= nStateInvs) {
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                  s"Invalid invariant ID: state invariant $invariantId not in [0, $nStateInvs)"))
        } else if (params.kind == InvariantKind.ACTION && invariantId >= nActionInvs) {
          Left(ServiceError(JsonRpcCodes.INVALID_PARAMS,
                  s"Invalid invariant ID: action invariant $invariantId not in [0, $nActionInvs)"))
        } else {
          Right(checkerContext)
        }

      case None =>
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: $sessionId"))
    }

    // Check the invariant
    withLock(params.sessionId) {
      validationResult.map { checkerContext =>
        if (!sessions.contains(params.sessionId)) {
          return Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND,
                  s"Session not found: ${params.sessionId}"))
        }
        // take a snapshot of the current context
        val snapshotBeforeId = snapshots.takeSnapshot(sessionId, checkerContext)
        // if it's too early to check a state or action invariant, return SATISFIED
        val stepNo = checkerContext.trex.stepNo
        if (stepNo == 0 || stepNo == 1 && params.kind == InvariantKind.ACTION) {
          // stepNo == 0 => Init has not been applied, so no state invariant can be violated
          // stepNo == 1 => only Init has been applied, so no action invariant can be violated
          logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: invariant $invariantId SATISFIED")
          return Right(CheckInvariantResult(sessionId, InvariantStatus.SATISFIED, NullNode.getInstance()))
        }
        // extract the corresponding invariant negation
        val notInvExpr =
          if (params.kind == InvariantKind.STATE) {
            // state invariant
            checkerContext.checkerInput.verificationConditions.stateInvariantsAndNegations(invariantId)._2
          } else {
            // action invariant
            checkerContext.checkerInput.verificationConditions.actionInvariantsAndNegations(invariantId)._2
          }
        // assert the negation of the invariant
        checkerContext.trex.assertState(notInvExpr)
        // ...and check whether the negation is satisfiable
        val (status, jsonTrace) =
          checkerContext.trex.sat(params.timeoutSec) match {
            case Some(isSat) =>
              if (isSat) {
                (InvariantStatus.VIOLATED, getTraceInJson(checkerContext, params.timeoutSec))
              } else {
                (InvariantStatus.SATISFIED, NullNode.getInstance())
              }

            case None =>
              (InvariantStatus.UNKNOWN, NullNode.getInstance())
          }
        // recover the snapshot
        snapshots.recoverSnapshot(sessionId, checkerContext, snapshotBeforeId)
        logger.info(s"Session=$sessionId Step=$stepNo Snapshot=$snapshotBeforeId: invariant $invariantId $status")
        CheckInvariantResult(sessionId, status, jsonTrace)
      }
    }
  }

  /**
   * Query for values.
   *
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[QueryResult]]
   */
  def query(params: QueryParams): Either[ServiceError, QueryResult] = {
    val sessionId = params.sessionId
    // validate the input parameters under the global lock
    val validationResult = sessions.get(sessionId) match {
      case Some(injector) =>
        // get the checker context from the injector
        val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
        val checkerContext = checkerModule.modelCheckerContext.get
        Right(checkerContext)

      case None =>
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: $sessionId"))
    }

    // Roll to the next step. Make sure that we do not update the SMT context concurrently.
    withLock(params.sessionId) {
      validationResult.map { checkerContext =>
        if (!sessions.contains(params.sessionId)) {
          return Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND,
                  s"Session not found: ${params.sessionId}"))
        }

        val traceInJson =
          if (params.kinds.contains(QueryKind.TRACE)) {
            getTraceInJson(checkerContext, params.timeoutSec)
          } else {
            NullNode.getInstance()
          }
        val viewInJson =
          if (!params.kinds.contains(QueryKind.OPERATOR)) {
            NullNode.getInstance()
          } else {
            getViewInJson(checkerContext, params.operator, params.timeoutSec) match {
              case Right(json) => json
              case Left(msg)   => return Left(ServiceError(JsonRpcCodes.INTERNAL_ERROR, msg))
            }
          }
        QueryResult(sessionId, trace = traceInJson, operatorValue = viewInJson)
      }
    }
  }

  /**
   * Try switching to the next model, if it exists.
   *
   * @param params
   *   the parameters object that contains the session ID
   * @return
   *   either an error or [[NextModelResult]]
   */
  def nextModel(params: NextModelParams): Either[ServiceError, NextModelResult] = {
    val sessionId = params.sessionId
    // validate the input parameters under the global lock
    val checkerContext =
      sessions.get(sessionId) match {
        case Some(injector) =>
          // get the checker context from the injector
          val checkerModule = injector.getInstance(classOf[BoundedCheckerPassImpl])
          val checkerContext = checkerModule.modelCheckerContext.get
          checkerContext

        case None =>
          return Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: $sessionId"))
      }

    // Roll to the next step. Make sure that we do not update the SMT context concurrently.
    withLock(params.sessionId) {
      if (!sessions.contains(params.sessionId)) {
        Left(ServiceError(JsonRpcCodes.SERVER_ERROR_SESSION_NOT_FOUND, s"Session not found: ${params.sessionId}"))
      } else {
        val decl = findOperator(checkerContext, params.operator) match {
          case Left(msg) => return Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, msg))
          case Right(d)  => d
        }

        checkerContext.trex.evaluate(params.timeoutSec, decl.body) match {
          case None =>
            // the current context is UNSAT (or timed out)
            Right(NextModelResult(sessionId, oldValue = NullNode.instance, hasOld = NextModelStatus.FALSE,
                    hasNext = NextModelStatus.FALSE))

          case Some(oldTlaExpr) =>
            val assertion = tla.not(tla.eql(tla.unchecked(decl.body), tla.unchecked(oldTlaExpr))).build
            checkerContext.trex.assertState(assertion)
            val hasNext =
              checkerContext.trex
                .sat(params.timeoutSec)
                .map(isSat => if (isSat) NextModelStatus.TRUE else NextModelStatus.FALSE)
                .getOrElse(NextModelStatus.UNKNOWN)

            // Serialize the old operator value to JSON
            val ujsonExpr = ItfCounterexampleWriter.exprToJson(oldTlaExpr)
            // Convert UJSON to Jackson's JsonNode.
            val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
            val oldValueInJson = mapper.readTree(new StringReader(ujsonExpr.render()))
            Right(NextModelResult(sessionId, oldValue = oldValueInJson, hasOld = NextModelStatus.TRUE,
                    hasNext = hasNext))
        }
      }
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
      timeoutSec: Int): JsonNode = {
    checkerContext.trex.sat(timeoutSec) match {
      case Some(isSat) =>
        if (!isSat) {
          // no trace
          NullNode.getInstance()
        } else {
          // extract the trace
          // We do not extract any labels. The remote client should be able to reconstruct them from the transition IDs,
          // as reported by loadSpec.
          val path = checkerContext.trex.decodedExecution().path
          val counterexample = Trace(checkerContext.checkerInput.rootModule, path.map(_.assignments).toIndexedSeq,
              path.map(_ => SortedSet[String]()).toIndexedSeq, ())
          // Serialize the counterexample to JSON
          val ujsonTrace =
            ItfCounterexampleWriter.mkJson(checkerContext.checkerInput.rootModule, counterexample.states)
          // Unfortunately, ujsonTrace is in UJSON, and we need Jackson's JsonNode.
          new ObjectMapper().registerModule(DefaultScalaModule).readTree(new StringReader(ujsonTrace.render()))
        }

      case None =>
        // unknown
        NullNode.getInstance()
    }
  }

  private def getViewInJson(
      checkerContext: ModelCheckerContext[IncrementalExecutionContextSnapshot],
      operatorName: String,
      timeoutSec: Int): Either[String, JsonNode] = {
    findOperator(checkerContext, operatorName)
      .flatMap(decl => {
        checkerContext.trex.evaluate(timeoutSec, decl.body) match {
          case None =>
            val msg = s"Failed to evaluate $operatorName within $timeoutSec seconds"
            logger.warn(msg)
            Left(msg)

          case Some(tlaExpr) =>
            // Serialize the counterexample to JSON
            val ujsonExpr = ItfCounterexampleWriter.exprToJson(tlaExpr)
            // Convert UJSON to Jackson's JsonNode.
            val mapper = new ObjectMapper().registerModule(DefaultScalaModule)
            Right(mapper.readTree(new StringReader(ujsonExpr.render())))
        }
      })
  }

  private def findOperator(
      checkerContext: ModelCheckerContext[IncrementalExecutionContextSnapshot],
      name: String): Either[String, TlaOperDecl] = {
    checkerContext.checkerInput.persistentDecls.get(name) match {
      case None =>
        val msg = "Operator not found: " + name
        logger.warn(msg)
        Left(msg)

      case Some(decl) =>
        val paramsCount = decl.formalParams.size
        if (paramsCount > 0) {
          val msg = s"Operators with arguments are not supported yet: $name has $paramsCount parameters"
          logger.warn(msg)
          Left(msg)
        } else {
          Right(decl)
        }
    }
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
      .map(cfg => {
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
      })
  }

  // call the callback under the lock for the given session ID
  private def withLock[T](sessionId: String)(callback: => T) = {
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
  val MAX_POOL_SIZE = 1024

  /**
   * When the number of threads is greater than the core, this is the maximum time that excess idle threads will wait
   * for new tasks before terminating.
   */
  val KEEP_ALIVE_SEC = 60L

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
  logger.info("Created thread pool with core pool size %d, max pool size %d, keep alive %d sec"
        .format(Runtime.getRuntime.availableProcessors(), MAX_POOL_SIZE, KEEP_ALIVE_SEC))
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
    val input = req.getInputStream
    val requestJson = mapper.readTree(input)

    val method = requestJson.path("method").asText()
    val paramsNode = requestJson.path("params")
    val id = requestJson.path("id")

    // Build JSON-RPC response
    val responseJson = mapper.createObjectNode()
    responseJson.put("jsonrpc", "2.0")
    responseJson.set("id", id)

    val errorOrResult: Either[ServiceError, ExplorationServiceResult] =
      try {
        // Dispatch methods manually
        method match {
          case "loadSpec" =>
            new JsonParameterParser(mapper)
              .parseLoadSpec(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.loadSpec(serviceParams))

          case "disposeSpec" =>
            new JsonParameterParser(mapper)
              .parseDisposeSpec(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.disposeSpec(serviceParams))

          case "rollback" =>
            new JsonParameterParser(mapper)
              .parseRollback(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.rollback(serviceParams))

          case "assumeTransition" =>
            new JsonParameterParser(mapper)
              .parseAssumeTransition(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.assumeTransition(serviceParams))

          case "assumeState" =>
            new JsonParameterParser(mapper)
              .parseAssumeState(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.assumeState(serviceParams))

          case "nextStep" =>
            new JsonParameterParser(mapper)
              .parseNextStep(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.nextStep(serviceParams))

          case "checkInvariant" =>
            new JsonParameterParser(mapper)
              .parseCheckInvariant(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.checkInvariant(serviceParams))

          case "query" =>
            new JsonParameterParser(mapper)
              .parseQuery(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.query(serviceParams))

          case "nextModel" =>
            new JsonParameterParser(mapper)
              .parseNextModel(paramsNode)
              .fold(errorMessage => Left(ServiceError(JsonRpcCodes.INVALID_PARAMS, errorMessage)),
                  serviceParams => service.nextModel(serviceParams))

          case _ =>
            Left(ServiceError(JsonRpcCodes.METHOD_NOT_FOUND, s"Method not found: $method"))
        }
      } catch {
        case ex: Exception =>
          Left(ServiceError(JsonRpcCodes.INTERNAL_ERROR, s"Internal error: ${ex.getMessage}"))
      }

    errorOrResult match {
      case Left(error) =>
        responseJson.set[JsonNode]("error", mapper.valueToTree[JsonNode](error))

      case Right(result) =>
        responseJson.set[JsonNode]("result", mapper.valueToTree[JsonNode](result))
    }

    responseJson
  }
}

object JsonRpcServerApp {
  def run(config: Try[ApalacheConfig], hostname: String, port: Int): Unit = {
    val server = new Server(new InetSocketAddress(hostname, port))
    val context = new ServletContextHandler(ServletContextHandler.SESSIONS)
    context.setContextPath("/")
    server.setHandler(context)

    val service = new ExplorationService(config)
    context.addServlet(new ServletHolder(new JsonRpcServlet(service)), "/rpc")

    server.start()
    println(s"JSON-RPC server running on http://$hostname:$port/rpc")
    server.join()
  }

  def main(args: Array[String]): Unit = {
    val hostname = if (args.length >= 1) args(0) else "localhost"
    val port = if (args.length >= 2) args(1).toInt else 8822
    val cfg = ConfigManager("{common.command: 'server'}")
    run(cfg, hostname, port)
  }
}
