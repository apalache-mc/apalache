package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir._
import org.scalacheck.Prop.forAll
import org.scalatest.prop.Checkers
import org.scalatest.{BeforeAndAfter, FunSuite}

/**
 * Tests for DeepCopy using Scalacheck.
 *
 * @author Igor Konnov
 */
class TestDeepCopy extends FunSuite with BeforeAndAfter with Checkers {
  private def equalExCopies: (TlaEx, TlaEx) => Boolean = {
    case (l @ ValEx(lval), r @ ValEx(rval)) =>
      l.ID != r.ID && lval == rval && l.typeTag == r.typeTag

    case (l @ NameEx(lname), r @ NameEx(rname)) =>
      l.ID != r.ID && lname == rname && l.typeTag == r.typeTag

    case (l @ OperEx(lop, largs @ _*), r @ OperEx(rop, rargs @ _*)) =>
      l.ID != r.ID &&
        lop == rop &&
        l.typeTag == r.typeTag &&
        largs.length == rargs.length &&
        largs.zip(rargs).forall(equalExCopies.tupled)

    case (l @ LetInEx(lbody, ldefs @ _*), r @ LetInEx(rbody, rdefs @ _*)) =>
      equalExCopies(lbody, rbody) &&
        l.ID != r.ID &&
        l.typeTag == r.typeTag &&
        ldefs.length != rdefs.length &&
        ldefs
          .zip(rdefs)
          .forall(equalDeclCopies.tupled)

    case _ => false
  }

  private def equalDeclCopies: (TlaDecl, TlaDecl) => Boolean = {
    case (l @ TlaConstDecl(lname), r @ TlaConstDecl(rname)) =>
      l.ID != r.ID && lname == rname && l.typeTag == r.typeTag

    case (l @ TlaVarDecl(lname), r @ TlaVarDecl(rname)) =>
      l.ID != r.ID && lname == rname && l.typeTag == r.typeTag

    case (l @ TlaAssumeDecl(lbody), r @ TlaAssumeDecl(rbody)) =>
      l.ID != r.ID && equalExCopies(lbody, rbody) && l.typeTag == r.typeTag

    case (l @ TlaTheoremDecl(lname, lbody), r @ TlaTheoremDecl(rname, rbody)) =>
      l.ID != r.ID &&
        lname == rname &&
        equalExCopies(lbody, rbody) &&
        l.typeTag == r.typeTag

    case (l @ TlaOperDecl(lname, lparams, lbody), r @ TlaOperDecl(rname, rparams, rbody)) =>
      l.ID != r.ID &&
        lname == rname &&
        lparams == rparams &&
        equalExCopies(lbody, rbody) &&
        l.isRecursive == r.isRecursive &&
        l.typeTag == r.typeTag

    case _ => false
  }

  test("deep copy replicates expressions and declarations but not their identifiers") {
    val gens = new IrGenerators {
      override val maxArgs: Int = 10
    }

    val prop = {
      def exGen(ctx: gens.UserContext) = gens.genTlaEx(gens.simpleOperators ++ gens.setOperators)(ctx)

      forAll(gens.genTlaDecl(exGen)(gens.emptyContext)) { input =>
        val output = DeepCopy(new IdleTracker()).deepCopyDecl(input)
        equalDeclCopies(input, output)
      }
    }

    check(prop, minSuccessful(1000), sizeRange(10))
  }
}
