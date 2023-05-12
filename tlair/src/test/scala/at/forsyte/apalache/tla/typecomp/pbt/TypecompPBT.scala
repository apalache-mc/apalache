package at.forsyte.apalache.tla.typecomp.pbt

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import org.scalacheck.Arbitrary
import org.scalacheck.Gen

/** Utilities for property based testing using well-typed terms via the typed builder. */
object TypecompPBT {

  /** Generators for [TBuilderInstruction]s */
  object GenTBuilderInstruction {
    import Arbitrary.arbitrary
    type T = TBuilderInstruction

    lazy val contreteTlaType1: Gen[TlaType1] = (new TlaType1ConcreteGen {}).genType1

    /**
     * Generate a TBuilderInstruction by recursing thru the given type
     *
     * Instructions are not supported for values of the following "types":
     *
     *   - RealT1: not supported in apalache
     *   - OperT1: not values
     *   - VarT1: TODO should generate an arbitrary expression
     *   - RecT1: deprecated
     *   - RowT1 : shouldn't actually be a type
     *   - SparseTupT1 : TODO
     *
     * NOTE: The generated instruction will not have any shadowed names internally, but if a builder instance is
     * supplied, shadowing is possible.
     *
     * @param typ
     *   The type of term of which to generate a builder
     * @param builder
     *   Optionally and implicitly, the builder instance to use. If no builder instance is provided, each generated
     *   expression is constructed as if it were in an independent scope.
     */
    def ofType(typ: TlaType1)(implicit builder: ScopedBuilder = new ScopedBuilder()): Gen[T] = {
      // Used to ensure generated names are unique within the generated term
      var nameCounter = 0

      def genName(t: TlaType1): Gen[T] =
        Gen.identifier.map { n =>
          val uniqueName = s"${n}${nameCounter}"
          nameCounter += 1
          builder.name(uniqueName, t)
        }

      // TODO: add support for empty list
      def genSet(typ: TlaType1): Gen[T] = Gen.nonEmptyListOf(genInstr(typ)).map(elems => builder.enumSet(elems: _*))

      // Generate a TBuilderInstruction
      def genInstr(typ: TlaType1): Gen[T] = Gen.lzy {
        typ match {
          case BoolT1         => arbitrary[Boolean].map(builder.bool)
          case IntT1          => arbitrary[BigInt].map(builder.int)
          case StrT1          => arbitrary[String].map(builder.str)
          case t @ ConstT1(_) => Gen.alphaStr.map(pre => builder.const(s"${pre}", t))
          case SetT1(t)       => genSet(t)
          case SeqT1(t)       =>
            // TODO: add support for empty seq
            Gen.nonEmptyListOf(genInstr(t)).map(elems => builder.seq(elems: _*))
          case t: TupT1 =>
            for {
              args <- Gen.sequence[Seq[T], T](t.elems.map(genInstr))
            } yield builder.tuple(args: _*)
          // `None` because genTlaType1 only generates closed row types
          case RecRowT1(RowT1(fieldTypes, None)) =>
            fieldTypes.map { case (field, typ) => genInstr(typ).map(v => (field, v)) } match {
              case Nil    => Gen.fail // No possible value for the empty record
              case fields => Gen.sequence[Seq[(String, T)], (String, T)](fields).map(fs => builder.rowRec(None, fs: _*))
            }
          // `None` because genTlaType1 only generates closed row types
          case t @ VariantT1(RowT1(fieldTypes, None)) =>
            fieldTypes.map { case (tag, typ) =>
              genInstr(typ).map(arg => builder.variant(tag, arg, t))
            }.toList match {
              case Nil            => Gen.fail // No possible value for the empty variant
              case v :: Nil       => v // Just one variant option
              case v0 :: v1 :: vs => Gen.oneOf(v0, v1, vs: _*)
            }
          case FunT1(argT, resT) =>
            for {
              vName <- genName(argT)
              dom <- genSet(argT)
              res <- genInstr(resT)
            } yield builder.funDef(res, (vName, dom))
          case VariantT1(RowT1(_, Some(_))) | RecRowT1(RowT1(_, Some(_))) =>
            // Does not correspond to a concrete term
            // TODO: In future can generate arbitrary rows to fill in the vars here
            Gen.fail
          case RealT1 | _: OperT1 | _: VarT1 | _: RecT1 | _: RowT1 | _: SparseTupT1 =>
            // TlaType1ConcreteGen should ensure these these types should never be createc
            throw new IllegalArgumentException(
                s"Type ${typ.getClass().getSimpleName()} is not supported in PBT generation but given type ${typ}")
        }
      }

      genInstr(typ)
    }

    lazy val instr: Gen[T] = for {
      typ <- contreteTlaType1
      inst <- ofType(typ)
    } yield inst

    val typeVar: Gen[String] = Gen.alphaLowerChar.map(_.toString)

    val rowVar = Gen.some(typeVar)
    lazy val genRecordFields = for {
      // We need to generate unique names for record fields
      fieldNames <- Gen.nonEmptyContainerOf[Set, String](Gen.identifier)
      fields <- Gen.sequence[Seq[(String, TBuilderInstruction)], (String, TBuilderInstruction)](
          fieldNames.map(n => Gen.zip(Gen.const(n), instr)))
    } yield fields
  }

  /** Implicit arbitrary instances for [TBuilderInstruction]s */
  object ArbTBuilderInstruction {
    implicit val argContreteTlaType1: Arbitrary[TlaType1] = Arbitrary(GenTBuilderInstruction.contreteTlaType1)
    implicit val arbTBuilderInstruction: Arbitrary[TBuilderInstruction] = Arbitrary(GenTBuilderInstruction.instr)
  }
}
