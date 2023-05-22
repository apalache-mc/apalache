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

  // Only monomorphic types for the values we support in the model checker (i.e., not for reals)
  def genSupportedPrimitiveMono: Gen[TlaType1] =
    oneOf(const(BoolT1), const(IntT1), const(StrT1), genConst)

  def genPrimitiveMono: Gen[TlaType1] =
    oneOf(genSupportedPrimitiveMono, const(RealT1))

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
        // Record keys must be unique, so we generate a Set
        keys <- Gen.containerOfN[Set, String](s, identifier).map(_.toList)
        values <- listOfN(s, elem)
      } yield RecT1(keys.zip(values): _*)
    }

  val genRowVar: Gen[Option[VarT1]] =
    choose(0, 25).flatMap(varNo => some(VarT1(varNo)))

  def genRow: Gen[RowT1] =
    sized { size => // use 'sized' to control the depth of the generated term
      for {
        // use resize to decrease the depth of the elements (as terms)
        s <- choose(0, size)
        elem = resize(s - 1, genTypeTree)
        // Record keys must be unique, so we generate a Set
        keys <- Gen.containerOfN[Set, String](s, identifier).map(_.toList)
        values <- listOfN(s, elem)
        optVar <- genRowVar
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
        optVar <- genRowVar
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
        oneOf(
            genPrimitive,
            genSet,
            genSeq,
            genFun,
            genOper,
            genTup,
            genRec,
            genRowRec,
            genVariant,
            genRow,
        )
      }
    }
  }

  // this is the generator for arbitrary types, including nested ones
  def genType1: Gen[TlaType1] = genTypeTree
}

/**
 * Generators for the case classes of TlaType1's that are
 *
 *   - first-class -- meaning they can occur in any expression, which is not true of operator
 *   - constructable -- meaning the types are concrete, since parametric types do not correspond to first-class values
 *   - checkable -- meaning their values are supported in our bsmc, unlike TLA's Real
 *   - non-deprecated -- we still plan forward maintenance of the type
 *
 * The specific tydes we exclude are:
 *
 *   - RealT1
 *   - RecT1 (deprecated in favor of RecRowT1)
 *   - VarT1 (abstract)
 *   - Open row typed records (abstract)
 *   - RowT1 (this is not a type)
 *   - OperT (not a values)
 */
trait TlaType1ConcreteGen extends TlaType1Gen {
  override val genRowVar = Gen.const(None)
  override def genTypeTree: Gen[TlaType1] = lzy {
    sized { size =>
      if (size <= 1) {
        // end of recursion
        genSupportedPrimitiveMono
      } else {
        oneOf(
            genSupportedPrimitiveMono,
            genSet,
            genSeq,
            genFun,
            genTup,
            genRowRec,
            genVariant,
        )
      }
    }
  }
}
