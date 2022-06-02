package at.forsyte.apalache.shai.v1

import at.forsyte.apalache.shai.v1.transExplorer.ZioTransExplorer.TransExplorerClient
import io.grpc.ManagedChannelBuilder
import zio.{console, _}
import scalapb.zio_grpc.ZManagedChannel

object ClientApp extends zio.App {

  val clientLayer: Layer[Throwable, TransExplorerClient] =
    TransExplorerClient.live(
        ZManagedChannel(
            ManagedChannelBuilder.forAddress("localhost", RpcServer.port).usePlaintext()
        )
    )

  def todo(args: List[String]): ZIO[TransExplorerClient with ZEnv, Throwable, Unit] = for {
    _ <- console.putStrLn(args.mkString(", "))
  } yield ()

  final def run(args: List[String]) =
    todo(args).provideCustomLayer(clientLayer).exitCode
}
