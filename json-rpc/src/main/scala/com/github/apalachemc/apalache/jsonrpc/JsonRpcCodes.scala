package com.github.apalachemc.apalache.jsonrpc

/**
 * JSON-RPC error codes.
 *
 * See: https://www.jsonrpc.org/specification
 */
object JsonRpcCodes {
  /** Parse error - Invalid JSON was received by the server. An error occurred on the server while parsing the JSON text. */
  val PARSE_ERROR = -32700

  /** Invalid Request - The JSON sent is not a valid Request object. */
  val INVALID_REQUEST = -32600

  /** Method not found - The method does not exist / is not available. */
  val METHOD_NOT_FOUND = -32601

  /** Invalid params - Invalid method parameter(s). */
  val INVALID_PARAMS = -32602

  /** Internal error - Internal JSON-RPC error. */
  val INTERNAL_ERROR = -32603

  /**
   * The minimal value of server error codes (-32099).
   * Server error codes are reserved for implementation-defined server-errors (-32000 to -32099).
   */
  val SERVER_ERROR_MIN = -32099

  /**
   * The maximal value of server error codes (-32000).
   * Server error codes are reserved for implementation-defined server-errors (-32000 to -32099).
   */
  val SERVER_ERROR_MAX = -32000
}
