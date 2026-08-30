package org.apalachemc.integration.framework

import at.forsyte.apalache.tla.Tool

/** Runs Tool with deterministic console logging in a child JVM. */
object ForkedToolMain {
  /** Runs Tool without console decoration and exits with Tool's exit code. */
  def main(arguments: Array[String]): Unit = {
    val exitCode = Tool.run(arguments)
    System.exit(exitCode)
  }
}
