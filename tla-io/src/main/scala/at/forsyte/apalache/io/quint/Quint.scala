package at.forsyte.apalache.io.quint

import at.forsyte.apalache.tla.lir._
import com.typesafe.scalalogging.LazyLogging

import scala.util.Try

class Quint(moduleData: QuintOutput) extends LazyLogging {
  private val nameGen = new QuintNameGen

  def translate(quintExp: QuintEx): Try[TlaEx] = new QuintExprConverter(moduleData.table, moduleData.types, nameGen).convert(quintExp)
}

object Quint {
  def toTla(readable: ujson.Readable): Try[TlaModule] = for {
    quintOutput <- QuintOutput.read(readable)
    module = quintOutput.modules(0) // the flattened main module
    nameGen = new QuintNameGen      // name generator, reused across the entire spec
    declarations <- Try {
      // For each quint declaration, we need to try converting it to
      // a TlaDecl, and if it is a nullary operator, we need to add its
      // name to our set of nullary operators.
      // See the comment on `NullaryOpReader` for an explanation of the latter.
      val accumulatedNullarOpNames = Set[String]()
      val accumulatedTlaDecls = List[TlaDecl]()
      // Translate all definitions from the quint module
      module.defs
        .foldLeft((accumulatedNullarOpNames, accumulatedTlaDecls)) {
          // Accumulate the converted definition and the name of the operator, of it is nullary
          case ((nullaryOps, tlaDecls), quintDef) =>
            val translator = new QuintExprConverter(quintOutput.table, quintOutput.types, nameGen)
            translator.tlaDef(quintDef).run(nullaryOps) match {
              case None =>
                // Couldn't convert the declaration (e.g., for a type declaration) so ignore it
                (nullaryOps, tlaDecls)
              case Some((None, tlaDecl)) =>
                // Converted a non-nullary operator declaration
                (nullaryOps, tlaDecl :: tlaDecls)
              case Some((Some(nullOp), tlaDecl)) =>
                // Converted a nullary operator declaration, record the nullary op name
                (nullaryOps + nullOp, tlaDecl :: tlaDecls)
            }
        }
        ._2 // Just take the resulting TlaDecls
        .reverse // Return the declarations to their original order
    }
  } yield TlaModule(module.name, declarations)
}
