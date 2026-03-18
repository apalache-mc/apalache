package com.github.apalachemc.apalache.jsonrpc

import com.fasterxml.jackson.core.TreeNode
import com.fasterxml.jackson.databind.ObjectMapper

/**
 * A parser for JSON parameters used in the JSON-RPC server.
 * @param mapper
 *   An instance of ObjectMapper for converting JSON values.
 */
class JsonParameterParser(mapper: ObjectMapper) {
  private val applyInOrderMethods = Set(
      "assumeTransition",
      "assumeState",
      "nextStep",
      "query",
      "checkInvariant",
      "nextModel",
      "rollback",
      "compact",
  )

  /**
   * Parses the parameters for loading a specification.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or a [[LoadSpecParams]] instance
   */
  def parseLoadSpec(params: TreeNode): Either[String, LoadSpecParams] = {
    try {
      val specParams = mapper.treeToValue(params, classOf[LoadSpecParams])

      if (specParams.sources.isEmpty) {
        return Left("loadSpec parameters must be non-empty.")
      }

      val decodedSources = specParams.sources.map { base64Content =>
        val decodedContent = java.util.Base64.getDecoder.decode(base64Content)
        new String(decodedContent, "UTF-8")
      }

      Right(specParams.copy(sources = decodedSources))
    } catch {
      case e: Exception =>
        Left(s"Parse error in loadSpec: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for disposing a session.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or a [[DisposeSpecParams]] instance
   */
  def parseDisposeSpec(params: TreeNode): Either[String, DisposeSpecParams] = {
    try {
      val disposeParams = mapper.treeToValue(params, classOf[DisposeSpecParams])
      if (disposeParams.sessionId.isEmpty) {
        return Left("disposeSpec parameters must contain a non-empty sessionId.")
      }
      Right(disposeParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in disposeSpec: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for preparing a transition.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or an [[AssumeTransitionParams]] instance
   */
  def parseAssumeTransition(params: TreeNode): Either[String, AssumeTransitionParams] = {
    try {
      val assumeParams = mapper.treeToValue(params, classOf[AssumeTransitionParams])
      if (assumeParams.sessionId.isEmpty) {
        return Left("assumeTransition parameters must contain a non-empty sessionId.")
      }
      if (assumeParams.transitionId < 0) {
        return Left("assumeTransition parameters must contain a non-negative transitionId.")
      }
      Right(assumeParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in assumeTransition: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for assuming state constraints.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or an [[AssumeStateParams]] instance
   */
  def parseAssumeState(params: TreeNode): Either[String, AssumeStateParams] = {
    try {
      val assumeParams = mapper.treeToValue(params, classOf[AssumeStateParams])
      if (assumeParams.sessionId.isEmpty) {
        return Left("assumeState parameters must contain a non-empty sessionId.")
      }
      Right(assumeParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in assumeState: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for rolling back to an earlier snapshot.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or a [[RollbackParams]] instance
   */
  def parseRollback(params: TreeNode): Either[String, RollbackParams] = {
    try {
      val assumeParams = mapper.treeToValue(params, classOf[RollbackParams])
      if (assumeParams.sessionId.isEmpty) {
        return Left("rollback parameters must contain a non-empty sessionId.")
      }
      if (assumeParams.snapshotId < 0) {
        return Left("rollback parameters must contain a non-negative snapshotId.")
      }
      Right(assumeParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in rollback: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for compacting the symbolic trace.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or a [[CompactParams]] instance
   */
  def parseCompact(params: TreeNode): Either[String, CompactParams] = {
    try {
      val compactParams = mapper.treeToValue(params, classOf[CompactParams])
      if (compactParams.sessionId.isEmpty) {
        return Left("compact parameters must contain a non-empty sessionId.")
      }
      if (compactParams.snapshotId < 0) {
        return Left("compact parameters must contain a non-negative snapshotId.")
      }
      Right(compactParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in compact: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for switching to the next step.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or a [[NextStepParams]] instance
   */
  def parseNextStep(params: TreeNode): Either[String, NextStepParams] = {
    try {
      val applyParams = mapper.treeToValue(params, classOf[NextStepParams])
      if (applyParams.sessionId.isEmpty) {
        return Left("nextStep parameters must contain a non-empty sessionId.")
      }
      Right(applyParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in nextStep: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for checking invariants.
   * @param node
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or a [[CheckInvariantParams]] instance
   */
  def parseCheckInvariant(node: TreeNode): Either[String, CheckInvariantParams] = {
    try {
      val invParams = mapper.treeToValue(node, classOf[CheckInvariantParams])
      if (invParams.sessionId.isEmpty) {
        return Left("checkInvariant parameters must contain a non-empty sessionId.")
      }
      if (invParams.invariantId < 0) {
        return Left("invariantId must be non-negative.")
      }
      if (invParams.kind != InvariantKind.STATE && invParams.kind != InvariantKind.ACTION) {
        return Left("kind must be either 'STATE' or 'ACTION'.")
      }
      Right(invParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in checkInvariant: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for querying the symbolic context.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or a [[QueryParams]] instance
   */
  def parseQuery(params: TreeNode): Either[String, QueryParams] = {
    try {
      val applyParams = mapper.treeToValue(params, classOf[QueryParams])
      if (applyParams.sessionId.isEmpty) {
        return Left("nextStep parameters must contain a non-empty `sessionId`.")
      }
      if (applyParams.kinds.isEmpty) {
        return Left("query parameters must contain a non-empty `kinds` array.")
      }
      if (applyParams.kinds.exists(k => k != QueryKind.OPERATOR && k != QueryKind.TRACE)) {
        return Left(s"Field `kinds` may contain only: ${QueryKind.OPERATOR} or ${QueryKind.TRACE}.")
      }
      if (applyParams.kinds.contains(QueryKind.OPERATOR) && applyParams.operator == "") {
        return Left(s"Field `operator` must be provided when `kinds` contains '${QueryKind.OPERATOR}'.")
      }
      Right(applyParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in nextStep: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for switching to the next model.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or a [[NextModelParams]] instance
   */
  def parseNextModel(params: TreeNode): Either[String, NextModelParams] = {
    try {
      val applyParams = mapper.treeToValue(params, classOf[NextModelParams])
      if (applyParams.sessionId.isEmpty) {
        return Left("nextStep parameters must contain a non-empty `sessionId`.")
      }
      if (applyParams.operator == "") {
        return Left(s"Field `operator` must be provided.")
      }
      Right(applyParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in nextStep: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for applying several stateful calls in order.
   * @param params
   *   the `params` field from a JSON-RPC request
   * @return
   *   either an error message or an [[ApplyInOrderParams]] instance
   */
  def parseApplyInOrder(params: TreeNode): Either[String, ApplyInOrderParams] = {
    try {
      val applyParams = mapper.treeToValue(params, classOf[ApplyInOrderParams])
      if (applyParams.sessionId.isEmpty) {
        return Left("applyInOrder parameters must contain a non-empty sessionId.")
      }
      if (applyParams.calls.isEmpty) {
        return Left("applyInOrder parameters must contain a non-empty calls array.")
      }
      applyParams.calls.foreach { step =>
        if (!applyInOrderMethods.contains(step.method)) {
          return Left(s"Unsupported applyInOrder method: ${step.method}.")
        }
        if (step.params == null || !step.params.isObject) {
          return Left(s"Parameters for applyInOrder step '${step.method}' must be a JSON object.")
        }
      }
      Right(applyParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in applyInOrder: ${e.getMessage}")
    }
  }
}
