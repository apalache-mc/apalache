package at.forsyte.apalache.tla.tracee

import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.infra.passes.options.SourceOption._
import at.forsyte.apalache.io.itf.ItfJsonToTla
import at.forsyte.apalache.io.json.JsonDeserializationError
import at.forsyte.apalache.io.json.ujsonimpl.{ScalaFromUJsonAdapter, UJsonRepresentation, UJsonToTlaViaBuilder}
import at.forsyte.apalache.io.lir.TypeTagReader
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.tracee.TraceReader.{ApalacheJson, ITFJson, TraceJson}

import scala.util.{Failure, Success, Try}

/**
 * Reads an ITF-format or an ApalacheJson-format trace into a TLAIR trace, with an intermediate UJson representation.
 *
 * The intermediate representation wraps the underlying JSON object with a [[TraceReader.TraceJson]] wrapper, so the
 * methods know whether to expect the shape of ITF or of ApalacheJson.
 *
 * The wrapper can either immediately be passed to [[convert]], or read via e.g. [[getTraceLength]], if we don't need to
 * convert the full contents of the JSON.
 *
 * @author
 *   Jure Kukovec
 */
class UJsonTraceReader(sourceStoreOpt: Option[SourceStore], tagReader: TypeTagReader) extends TraceReader[UJsonRepresentation] {
  private val builder = new UJsonToTlaViaBuilder(sourceStoreOpt)(tagReader)
  private val itfToTla = new ItfJsonToTla[UJsonRepresentation](ScalaFromUJsonAdapter)

  type TraceUJson = TraceJson[UJsonRepresentation]

  // Rethrow as JsonDeserializationError if unable to read
  private def tryRead(readable: ujson.Readable): UJsonRepresentation = Try(ujson.read(readable)) match {
    case Success(ujsonVal)  => UJsonRepresentation(ujsonVal)
    case Failure(exception) =>
      throw new JsonDeserializationError(s"Unable to read $readable as JSON.", exception)
  }

  override def read(source: SourceOption): TraceUJson = source match {
    case FileSource(f, Format.Json)      => ApalacheJson(tryRead(f))
    case FileSource(f, Format.Itf)       => ITFJson(tryRead(f))
    case StringSource(s, _, Format.Json) => ApalacheJson(tryRead(s))
    case StringSource(s, _, Format.Itf)  => ITFJson(tryRead(s))
    case src => throw new IllegalArgumentException(s"Tried to load state from an invalid source: $src.")
  }

  override def convert(traceJson: TraceUJson): StateSeq = traceJson match {
    case ITFJson(json)      => convertITF(json)
    case ApalacheJson(json) => convertApalacheJson(json)
  }

  override def getTraceLength(traceJson: TraceUJson): Int = traceJson match {
    case ITFJson(json)      => getLengthITF(json)
    case ApalacheJson(json) => getLengthApalacheJson(json)
  }

  private def getLengthITF(json: UJsonRepresentation): Int =
    json.getFieldOpt("states").map(seqJSON => ScalaFromUJsonAdapter.asSeq(seqJSON).length).getOrElse {
      throw new JsonDeserializationError(s"Provided JSON does not comply with the ITF format.")
    }

  private def convertITF(json: UJsonRepresentation): StateSeq = itfToTla.parseTrace(json) match {
    case Right(trace) => trace
    case Left(err)    => throw err
  }

  private def kvFromAssignment(ex: TlaEx): (String, TlaEx) = ex match {
    case OperEx(TlaOper.eq, NameEx(name), rhs) => name -> rhs
    case _ => throw new JsonDeserializationError(s"Cannot read variable assignment from $ex.")
  }

  private def convertApalacheJson(json: UJsonRepresentation): StateSeq = {
    val operDecls = for {
      modules <- json.getFieldOpt("modules")
      decls <- ScalaFromUJsonAdapter.asSeq(modules).head.getFieldOpt("declarations")
    } yield {
      // drop CInit (head) and Inv (last)
      ScalaFromUJsonAdapter.asSeq(decls).tail.dropRight(1).toIndexedSeq.map { decl =>
        builder.asTlaDecl(decl).asInstanceOf[TlaOperDecl]
      }
    }
    // From an indexed sequence of declarations, create a sequence of State-maps.
    operDecls
      .map { decls =>
        decls.map { decl =>
          decl.body match {
            // Edge case: single-var specs
            case OperEx(TlaOper.eq, NameEx(name), rhs) => Map(name -> rhs)
            // general conjunctive case
            case OperEx(TlaBoolOper.and, args @ _*) =>
              Map(args.map(kvFromAssignment): _*)
            // malformed JSON case
            case body =>
              throw new JsonDeserializationError(s"Cannot read state from $body.")
          }
        }
      }
      .getOrElse {
        throw new JsonDeserializationError(s"Trace JSON is incorrectly formatted.")
      }
  }

  private def getLengthApalacheJson(json: UJsonRepresentation): Int = {
    val lenOpt = for {
      modules <- json.getFieldOpt("modules")
      decls <- ScalaFromUJsonAdapter.asSeq(modules).head.getFieldOpt("declarations")
    } yield ScalaFromUJsonAdapter.asSeq(decls).length - 2 // we need len-2 for CInit (head) and Inv (last)

    lenOpt.getOrElse {
      throw new JsonDeserializationError(s"Provided JSON does not comply with the Apalache JSON format.")
    }
  }
}
