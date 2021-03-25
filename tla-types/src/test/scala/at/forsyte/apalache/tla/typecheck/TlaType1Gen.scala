package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.{
  BoolT1, ConstT1, FunT1, IntT1, OperT1, RealT1, RecT1, SeqT1, SetT1, StrT1, TlaType1, TupT1, VarT1
}
import org.scalacheck.Arbitrary.arbitrary
import org.scalacheck.Gen
import org.scalacheck.Gen.{choose, const, identifier, listOfN, lzy, oneOf, posNum, resize, sized}

// Generators for the case classes of TlaType1
trait TlaType1Gen {
  def genConst: Gen[TlaType1] =
    for {
      str <- identifier
    } yield ConstT1(str.toUpperCase())

  def genVar: Gen[TlaType1] =
    for {
      i <- posNum[Int]
      // produce an absolute value. Note that Math.abs(Integer.MIN_VALUE) = Integer.MIN_VALUE, so use max(0, abs(i)).
    } yield VarT1(i)

  def genPrimitive: Gen[TlaType1] =
    oneOf(const(BoolT1()), const(IntT1()), const(StrT1()), const(RealT1()), genConst, genVar)

  def genSet: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size)
        g <- resize(size / (s + 1), genTypeTree)
      } yield SetT1(g)
    }

  def genSeq: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size)
        g <- resize(size / (s + 1), genTypeTree)
      } yield SeqT1(g)
    }

  def genFun: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size - 1)
        arg <- resize(s, genTypeTree)
        res <- resize(s, genTypeTree)
      } yield FunT1(arg, res)
    }

  def genOper: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size - 1)
        elem = resize(s, genTypeTree)
        args <- listOfN(s, elem)
        res <- resize(s, genTypeTree)
      } yield OperT1(args, res)
    }

  def genTup: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size - 1)
        elem = resize(s, genTypeTree)
        args <- listOfN(s + 1, elem) // no empty tuples
      } yield TupT1(args: _*)
    }

  def genRec: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size)
        elem = resize(s - 1, genTypeTree)
        keys <- listOfN(s, identifier)
        values <- listOfN(s, elem)
      } yield RecT1(keys.zip(values): _*)
    }

  // generate the term tree -- a recursive data structure
  def genTypeTree: Gen[TlaType1] = lzy {
    sized { size =>
      if (size <= 1) {
        // end of recursion
        genPrimitive
      } else {
        // We may produce deeper trees.
        // NOTE: we do not generate sparse tuples, as they cannot appear in user's annotations.
        oneOf(genPrimitive, genSet, genSeq, genFun, genOper, genTup, genRec)
      }
    }
  }

  // this is the generator for arbitrary types, including nested ones
  def genType1: Gen[TlaType1] = genTypeTree
}
