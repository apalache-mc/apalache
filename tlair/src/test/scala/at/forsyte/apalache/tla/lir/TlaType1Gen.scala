package at.forsyte.apalache.tla.lir

import org.scalacheck.Gen
import org.scalacheck.Gen.{choose, const, identifier, listOfN, lzy, oneOf, posNum, resize, sized, some}

import scala.collection.immutable.SortedMap

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

  def genPrimitiveMono: Gen[TlaType1] =
    oneOf(const(BoolT1), const(IntT1), const(StrT1), const(RealT1), genConst)

  def genPrimitive: Gen[TlaType1] =
    oneOf(genPrimitiveMono, genVar)

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
        s <- choose(0, Math.max(size - 1, 0))
        g <- resize(s, genTypeTree)
      } yield SeqT1(g)
    }

  def genFun: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, Math.max(size - 1, 0))
        arg <- resize(s, genTypeTree)
        res <- resize(s, genTypeTree)
      } yield FunT1(arg, res)
    }

  def genOper: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, Math.max(size - 1, 0))
        elem = resize(s, genTypeTree)
        args <- listOfN(s, elem)
        res <- resize(s, genTypeTree)
      } yield OperT1(args, res)
    }

  def genTup: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, Math.max(size - 1, 0))
        elem = resize(s, genTypeTree)
        args <- listOfN(s + 1, elem) // no empty tuples
      } yield TupT1(args: _*)
    }

  def genRec: Gen[TlaType1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // min=1 to prevent empty records
        s <- choose(1, Math.max(size, 1))
        // use resize to decrease the depth of the elements (as terms)
        elem = resize(s - 1, genTypeTree)
        keys <- listOfN(s, identifier)
        values <- listOfN(s, elem)
      } yield RecT1(keys.zip(values): _*)
    }

  def genRow: Gen[RowT1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size)
        elem = resize(s - 1, genTypeTree)
        keys <- listOfN(s, identifier)
        values <- listOfN(s, elem)
        varNo <- choose(0, 25)
        optVar <- some(VarT1(varNo))
      } yield RowT1(SortedMap(keys.zip(values): _*), optVar)
    }

  def genRowRec: Gen[RecRowT1] = {
    for {
      row <- genRow
    } yield RecRowT1(row)
  }

  def genVariantOption: Gen[RecRowT1] = {
    for {
      // use resize to decrease the depth of the elements (as terms)
      row <- genRow
    } yield RecRowT1(RowT1(SortedMap(row.fieldTypes.toSeq: _*), row.other))
  }

  def genVariant: Gen[VariantT1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size)
        elem = resize(s - 1, genVariantOption)
        keys <- listOfN(s, identifier)
        values <- listOfN(s, elem)
        varNo <- choose(0, 25)
        optVar <- some(VarT1(varNo))
      } yield VariantT1(RowT1(SortedMap(keys.zip(values): _*), optVar))
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
        oneOf(genPrimitive, genSet, genSeq, genFun, genOper, genTup, genRec, genRowRec, genVariant, genRow)
      }
    }
  }

  // this is the generator for arbitrary types, including nested ones
  def genType1: Gen[TlaType1] = genTypeTree
}
