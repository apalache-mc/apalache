package com.github.apalachemc.apalache.jsonrpc

import com.fasterxml.jackson.core.TreeNode
import com.fasterxml.jackson.databind.ObjectMapper

/**
 * A parser for JSON parameters used in the JSON-RPC server.
 * @param mapper
 *   An instance of ObjectMapper for converting JSON values.
 */
class JsonParameterParser(mapper: ObjectMapper) {

  /**
   * Parses the parameters for loading a specification. The expected format is a JSON object with a "sources" field,
   * which is a sequence of pairs, where each pair consists of a name and a base64-encoded content.
   * @param params
   *   The "params" field from a JSON-RPC request, expected to be a TreeNode.
   * @return
   *   Either an error message or a [[LoadSpecParams]] instance containing the parsed sources.
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

      Right(LoadSpecParams(decodedSources))
    } catch {
      case e: Exception =>
        Left(s"Parse error in loadSpec: ${e.getMessage}")
    }
  }

  /**
   * Parses the parameters for disposing a session in the JSON-RPC server.
   * @param params
   *   The "params" field from a JSON-RPC request, expected to be a TreeNode.
   * @return
   *   Either an error message or a [[DisposeSpecParams]] instance containing the parsed sources.
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
   * Parses the parameters for preparing a transition in the JSON-RPC server.
   * @param params
   *   The "params" field from a JSON-RPC request, expected to be a TreeNode.
   * @return
   *   Either an error message or a [[AssumeTransitionParams]] instance containing the parsed sources.
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
   * Parses the parameters for switching to the next step.
   * @param params
   *   The "params" field from a JSON-RPC request, expected to be a TreeNode.
   * @return
   *   Either an error message or a [[NextStepParams]] instance containing the parsed sources.
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
   * Parses the parameters for checking invariants against the symbolic state.
   * @param node tree node representing the JSON method parameters
   * @return Either an error message or a [[CheckInvariantParams]] instance containing the parsed sources.
   */
  def parseCheckInvariant(node: TreeNode): Either[String, CheckInvariantParams] = {
    try {
      val invParams = mapper.treeToValue(node, classOf[CheckInvariantParams])
      if (invParams.sessionId.isEmpty) {
        return Left("checkInvariant parameters must contain a non-empty sessionId.")
      }
      if (invParams.stateInvariantIds.exists(_ < 0)) {
        return Left("stateInvariantIds parameters must contain non-negative identifiers.")
      }
      if (invParams.actionInvariantIds.exists(_ < 0)) {
        return Left("actionInvariantIds parameters must contain non-negative identifiers.")
      }
      if (invParams.traceInvariantIds.exists(_ < 0)) {
        return Left("traceInvariantIds parameters must contain non-negative identifiers.")
      }
      Right(invParams)
    } catch {
      case e: Exception =>
        Left(s"Parse error in checkInvariant: ${e.getMessage}")
    }
  }
}
