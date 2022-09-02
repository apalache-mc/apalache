package at.forsyte.apalache.shai.v1

import zio._
import zio.test._

// Since all of our RPC services need to run with shared resources in order to
// ensure that they can share the semaphore that guarnatees sequential access to
// the parser. Thus, all test cases for the various test cases are run together
// with the same shared layers.
object RpcServerSpec extends DefaultRunnableSpec {
  val tests = TransExplorerTestCases.tests

  def spec = suite("RpcServerSpec")(tests: _*)
    // Create the single shared service for use in our tests, allowing us to run
    // all tests as if they were against the same service. This accurately
    // reflects our usage, since only one server instance will ever be running
    // in an Apalache process at a time.
    .provideSomeLayerShared[ZEnv](RpcServer.createTransExplorerService.toLayer)
}
