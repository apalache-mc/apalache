package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes._
import at.forsyte.apalache.tla.assignments.passes.{AssignmentPass, AssignmentPassImpl}
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, ExprGradeStoreImpl, FreeExistentialsStore, FreeExistentialsStoreImpl}
import at.forsyte.apalache.tla.imp.passes.{SanyParserPass, SanyParserPassImpl}
import com.google.inject.AbstractModule
import com.google.inject.name.Names

/**
  * A configuration that binds all the passes from the parser to the checker.
  *
  * @author Igor Konnov
  */
class CheckerModule extends AbstractModule {
  override def configure(): Unit = {
    // the options singleton
    bind(classOf[PassOptions])
      .to(classOf[WriteablePassOptions])
    // stores
    bind(classOf[FreeExistentialsStore])
      .to(classOf[FreeExistentialsStoreImpl])
    bind(classOf[ExprGradeStore])
      .to(classOf[ExprGradeStoreImpl])
    // SanyParserPassImpl is the default implementation of SanyParserPass
    bind(classOf[SanyParserPass])
      .to(classOf[SanyParserPassImpl])
    // and it also the initial pass for PassChainExecutor
    bind(classOf[Pass])
      .annotatedWith(Names.named("InitialPass"))
      .to(classOf[SanyParserPass])
    // the next pass after SanyParserPass is AssignmentPass
    bind(classOf[AssignmentPass])
      .to(classOf[AssignmentPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterParser"))
      .to(classOf[AssignmentPass])
    // the next pass after AssignmentPass is GradePass
    bind(classOf[GradePass])
      .to(classOf[GradePassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterAssignment"))
      .to(classOf[GradePass])
    // the next pass after GradePass is SimpleSkolemizationPass
    bind(classOf[SimpleSkolemizationPass])
      .to(classOf[SimpleSkolemizationPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterGrade"))
      .to(classOf[SimpleSkolemizationPass])
    // the next pass after SimpleSkolemizationPass is BoundedCheckerPass
    bind(classOf[BoundedCheckerPass])
      .to(classOf[BoundedCheckerPassImpl])
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterSkolem"))
      .to(classOf[BoundedCheckerPass])
    // the final pass is TerminalPass
    bind(classOf[Pass])
      .annotatedWith(Names.named("AfterChecker"))
      .to(classOf[TerminalPass])
  }

}
