package at.forsyte.apalache.tla.typecomp

import at.forsyte.apalache.tla.lir.{
  BoolT1, ConstT1, FunT1, IntT1, OperParam, OperT1, RealT1, RecRowT1, RecT1, RowT1, SeqT1, SetT1, SparseTupT1, StrT1,
  TlaType1, TupT1, VarT1, VariantT1,
}

object ParamUtil {

  type TypedParam = (OperParam, TlaType1)

  /**
   * Evaluates whether a parameter type satisfies the type restrictions on operator parameters in TLA+.
   *
   * Parameters of TLA+ operators must:
   *   - have a non-operator type, unless they are (syntactically) marked higher-order (HO)
   *   - have a top-level operator type (OperT1) if they are marked HO
   *   - not contain `OperT1` in the type's syntax-tree in either case, except possibly at the root (if HO). In
   *     particular, a parameter to a HO operator with an `OperT1` type may not be HO itself.
   */
  def isAcceptableParamType(canContainOper: Boolean): TlaType1 => Boolean = {
    case FunT1(arg, res)         => isAcceptableParamType(false)(arg) && isAcceptableParamType(false)(res)
    case SetT1(elem)             => isAcceptableParamType(false)(elem)
    case SeqT1(elem)             => isAcceptableParamType(false)(elem)
    case TupT1(elems @ _*)       => elems.forall(isAcceptableParamType(false))
    case SparseTupT1(fieldTypes) => fieldTypes.values.forall(isAcceptableParamType(false))
    case RecT1(fieldTypes)       => fieldTypes.values.forall(isAcceptableParamType(false))
    case OperT1(args, res) =>
      if (canContainOper)
        args.nonEmpty &&
        args.forall(isAcceptableParamType(false)) &&
        isAcceptableParamType(false)(res)
      else false
    case RowT1(fieldTypes, _) => fieldTypes.values.forall(isAcceptableParamType(false))
    case RecRowT1(row)        => isAcceptableParamType(false)(row)
    case VariantT1(row)       => isAcceptableParamType(false)(row)
    case IntT1 | StrT1 | BoolT1 | RealT1 | VarT1(_) | ConstT1(_) => true
  }

  /**
   * Throws if parameters don't satisfy [[isAcceptableParamType]]. Permits operator types iff the parameter arity is
   * positive.
   */
  def validateParamType(tp: TypedParam): Unit = {
    val (OperParam(name, arity), tt) = tp
    if (!isAcceptableParamType(canContainOper = arity > 0)(tt))
      throw new TBuilderTypeException(
          s"Parameter $name type $tt and arity $arity are inconsistent. Parameters have operator types iff their arity is positive."
      )
  }

  /**
   * Determines the parameter arity, if the type is an operator type. We distinguish nullary operators from
   * non-operators in this method.
   */
  def typeAsOperArity(tt: TlaType1): Option[Int] = tt match {
    case OperT1(args, _) => Some(args.size)
    case _               => None
  }

  /**
   * Operator parameter with type information. Checks that parameters have permissible types.
   */
  def param(name: String, tt: TlaType1): TypedParam = {
    val arityOpt = typeAsOperArity(tt)
    // operator parameters may not be nullary operators
    if (arityOpt.contains(0))
      throw new TBuilderTypeException(s"Parameter $name may not have a nullary operator type $tt.")
    val arity = arityOpt.getOrElse(0) // 0 here means not-an-operator
    val ret = (OperParam(name, arity), tt)
    validateParamType(ret)
    ret
  }

}
