package at.forsyte.apalache.tla.imp.src

import at.forsyte.apalache.tla.lir.EnvironmentHandlerGenerator
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner


@RunWith(classOf[JUnitRunner])
class TestSourceStore extends FunSuite {
  test("basic add and find") {
    val store = new SourceStore()
    val environmentHandler = EnvironmentHandlerGenerator.makeEH
    val ex = environmentHandler.identify(tla.int(1))
    val loc = SourceLocation("root", SourceRegion(1, 2, 3, 4))
    store.addRec(ex, loc)
    val foundLoc = store.find(ex.safeId)
    assert(loc == foundLoc.get)
  }

  test("recursive add and find") {
    val store = new SourceStore()
    val environmentHandler = EnvironmentHandlerGenerator.makeEH
    val int1 = tla.int(1)
    val set = environmentHandler.identify(tla.enumSet(int1))
    val loc = SourceLocation("root", SourceRegion(1, 2, 3, 4))
    store.addRec(set, loc)
    val foundLoc = store.find(set.safeId)
    assert(loc == foundLoc.get)
    val foundLoc2 = store.find(int1.safeId)
    assert(loc == foundLoc2.get)
  }

  test("locations are not overwritten") {
    val store = new SourceStore()
    val environmentHandler = EnvironmentHandlerGenerator.makeEH
    val int1 = tla.int(1)
    val set = environmentHandler.identify(tla.enumSet(int1))
    val set2 = environmentHandler.identify(tla.enumSet(set))
    val loc1 = SourceLocation("tada", SourceRegion(100, 200, 300, 400))
    store.addRec(int1, loc1)
    val loc2 = SourceLocation("root", SourceRegion(1, 2, 3, 4))
    store.addRec(set2, loc2)
    assert(loc2 == store.find(set2.safeId).get)
    assert(loc2 == store.find(set.safeId).get)
    assert(loc1 == store.find(int1.safeId).get)
  }
}
