package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.store.{AnnotationStore, createAnnotationStore}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, OperParam, TlaDecl, TlaEx, TlaModule, TlaOperDecl}
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite

trait SanyImporterTestBase extends AnyFunSuite with BeforeAndAfter {
  protected var sourceStore: SourceStore = _
  protected var annotationStore: AnnotationStore = _
  protected var sanyImporter: SanyImporter = _

  before {
    sourceStore = new SourceStore
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
  }

  // assert that all declarations have source information
  def expectSourceInfoInDefs(module: TlaModule): Unit = {
    def assertForDecl(decl: TlaDecl): Unit = {
      assert(
          sourceStore.contains(decl.ID),
          s"(No source location for declaration $decl.name)",
      )
    }

    def collectDefs: TlaEx => Seq[TlaDecl] = {
      case LetInEx(body, defs @ _*) =>
        collectDefs(body) ++ defs.flatMap { d =>
          collectDefs(d.body)
        }

      case OperEx(_, args @ _*) =>
        args flatMap collectDefs

      case _ =>
        List()
    }

    for (decl <- module.declarations) {
      assertForDecl(decl)
      decl match {
        case operDecl: TlaOperDecl =>
          collectDefs(operDecl.body) foreach assertForDecl

        case _ => ()
      }
    }
  }

  def expectOperDecl(
      name: String, params: List[OperParam], body: TlaEx,
  ): (TlaDecl => Unit) = {
    case d: TlaOperDecl =>
      assert(name == d.name)
      assert(params == d.formalParams)
      assert(body == d.body)
      // the source location of the definition body has been saved
      assert(
          sourceStore.contains(d.body.ID),
          s"(Source location of the definition body ${d.body.ID} is not stored)",
      )
      // the source location of the definition has been saved
      assert(
          sourceStore.contains(d.ID),
          s"(Source of the definition ${d.name} is not stored)",
      )

    case d @ _ =>
      fail("Expected a TlaOperDecl, found: " + d)
  }

  def findAndExpectOperDecl(
      mod: TlaModule, name: String, params: List[OperParam], body: TlaEx,
  ): Unit = {
    mod.declarations.find {
      _.name == name
    } match {
      case Some(d: TlaOperDecl) =>
        expectOperDecl(name, params, body)(d)

      case _ =>
        fail("Expected a TlaDecl")
    }
  }
}
