package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, FunT1, IntT1, StrT1, TlaType1, TupT1}

/**
 * TlaType1ToSortConverter helps convert between TlaType1 types and Sort values.
 *
 * @author
 *   Jure Kukovec
 */
object TlaType1ToSortConverter {

  def sortFromType(tt: TlaType1): Sort = tt match {
    case IntT1                        => IntSort
    case BoolT1                       => BoolSort
    case StrT1                        => UninterpretedSort(tt.toString)
    case ConstT1(name)                => UninterpretedSort(name)
    case FunT1(TupT1(args @ _*), res) => FunctionSort(sortFromType(res), args.map(sortFromType): _*)
    case FunT1(arg, res)              => FunctionSort(sortFromType(res), sortFromType(arg))
    case _                            => throw new IllegalArgumentException(s"Type $tt not permitted in VMT")
  }
}
