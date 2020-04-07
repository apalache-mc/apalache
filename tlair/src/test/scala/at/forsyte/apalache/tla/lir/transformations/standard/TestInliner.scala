package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.TestingPredefs
import org.scalatest.FunSuite
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker

class TestInliner extends FunSuite with TestingPredefs {

  test("Inlining with recursion: Operators"){
    val operName = "Foo"
    val limitDecl = tla.declOp( InlinerOfUserOper.UNFOLD_TIMES_PREFIX + operName, 5 )
    val defaultDecl = tla.declOp( InlinerOfUserOper.UNFOLD_DEFAULT_PREFIX + operName, 0 )

    val fooDecl = tla.declOp(
      operName,
      tla.ite(
        tla.le( n_x, 0 ),
        0,
        tla.appOp( tla.name( operName ), tla.minus( n_x, 1 ) )
      ),
      "x"
    )
    fooDecl.isRecursive = true

    val decls = Seq(limitDecl,defaultDecl, fooDecl )
    val bm = BodyMapFactory.makeFromDecls( decls )

    val ex = tla.appDecl( fooDecl, 10 )

    // Check for absence of exceptions
    InlinerOfUserOper(bm, new IdleTracker)(ex)
  }

  test("Inlining with recursion: Functions"){
    // recursive functions get parsed as recursive operators
    val fnName = "Foo"
    val domain = tla.dotdot(1, 10)

    val limitDecl = tla.declOp( InlinerOfUserOper.UNFOLD_TIMES_PREFIX + fnName, 5 )
    val defaultDecl = tla.declOp( InlinerOfUserOper.UNFOLD_DEFAULT_PREFIX + fnName,
      tla.funDef( 1, n_y, domain )
    )


    val fooDecl = tla.declOp(
      fnName,
      tla.funDef(
        tla.ite(
          tla.le( n_x, 0 ),
          0,
          tla.appFun( tla.appOp( tla.name( fnName ) ), tla.minus( n_x, 1 ) )
        ),
        n_x,
        domain
      )
    )
    fooDecl.isRecursive = true

    val decls = Seq(limitDecl,defaultDecl, fooDecl )
    val bm = BodyMapFactory.makeFromDecls( decls )

    val ex = tla.appFun( tla.appDecl( fooDecl ), 10 )

    // Check for absence of exceptions
    InlinerOfUserOper(bm, new IdleTracker)(ex)
  }

}
