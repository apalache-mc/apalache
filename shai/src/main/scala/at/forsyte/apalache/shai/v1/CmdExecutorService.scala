package at.forsyte.apalache.shai.v1

import at.forsyte.apalache.shai.v1.cmdExecutor.ZioCmdExecutor
import zio.{Semaphore, ZEnv}
import com.typesafe.scalalogging.Logger

/**
 * Provides the [[CmdExecutorService]]
 *
 * ==Overview==
 *
 * The [[CmdExecutorService]] exposes an RPC interface to execute Apalache's CLI subcommand, thus enabling clients to
 * utilize much of Apalache's CLI functionality with the benefit of structured configuration, input, and output and
 * avoiding the repeated startup costs of the JVM.
 *
 * [[CmdExecutorService]] is meant to be registered with the [[RpcServer]], and should not need to be used directly.
 */

class CmdExecutorService(parserSemaphore: Semaphore, logger: Logger) extends ZioCmdExecutor.ZCmdExecutor[ZEnv, Any] {

  // TODO These will be used when we start adding the RPC calls
  val _todo = (parserSemaphore, logger)
}
