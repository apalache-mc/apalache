package com.github.apalachemc.apalache.jsonrpc

import com.fasterxml.jackson.core.TreeNode
import com.fasterxml.jackson.databind.ObjectMapper

/**
 * Parameters for loading a specification in the JSON-RPC server.
 * @param sources
 *   A sequence of pairs, where each pair consists of a name and a base64-encoded content. The first element corresponds
 *   to the root module.
 */
case class LoadSpecParams(sources: Seq[(String, String)])

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
   *   Either an error message or a LoadSpecParams instance containing the parsed sources.
   */
  def parseLoadSpec(params: TreeNode): Either[String, LoadSpecParams] = {
    // Convert LoadSpecParams to class
    try {
      val specParams = mapper.treeToValue(params, classOf[LoadSpecParams])

      if (specParams.sources.isEmpty) {
        return Left("loadSpec parameters must be non-empty.")
      }

      val decodedSources = specParams.sources.map { case (name, base64Content) =>
        val decodedContent = java.util.Base64.getDecoder.decode(base64Content)
        (name, new String(decodedContent, "UTF-8"))
      }

      Right(LoadSpecParams(decodedSources))
    } catch {
      case e: Exception =>
        Left(s"Parse error in loadSpec: ${e.getMessage}")
    }
  }
}
