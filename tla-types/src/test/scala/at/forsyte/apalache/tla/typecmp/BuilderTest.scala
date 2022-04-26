package at.forsyte.apalache.tla.typecmp

import at.forsyte.apalache.tla.typecheck.etc.TypeVarPool
import org.junit.runner.RunWith
import org.scalatest.{AppendedClues, BeforeAndAfter}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatestplus.junit.JUnitRunner
import org.scalatestplus.scalacheck.Checkers

@RunWith(classOf[JUnitRunner])
trait BuilderTest extends AnyFunSuite with BeforeAndAfter with Checkers with AppendedClues with Matchers {
  var varPool = new TypeVarPool()
  var sigGen = new SignatureHandler(varPool)
  var builder = new ScopedBuilder(varPool)

  before {
    varPool = new TypeVarPool()
    sigGen = new SignatureHandler(varPool)
    builder = new ScopedBuilder(varPool)
  }
}
