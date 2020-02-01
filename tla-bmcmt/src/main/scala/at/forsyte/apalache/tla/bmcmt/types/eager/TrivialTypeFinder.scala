package at.forsyte.apalache.tla.bmcmt.types.eager

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, BoolTheory, IntTheory}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef.{TlaBoolSet, TlaIntSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt, TlaStr}
import com.google.inject.Singleton

import scala.collection.immutable.{Map, SortedMap}

/**
  * <p>An eager type finder that propagates types from the leaves to the root.
  * As it can easily fail to find a type, the user has to write type annotations.
  * In contrast, to our first type inference approach, this engine is not trying to be
  * smart at all, and it is not doing any form of unification.</p>
  *
  * <p>This class assumes that some pre-processing has been made:</p>
  *
  * <ol>
  *  <li>The definitions of all user-defined operators have been expanded (no recursive operators),</li>
  *  <li>All variable names are unique, including the bound variables.</li>
  * </ol>
  *
  * <p>TrivialTypeFinder implements TransformationListener, so it propagates type annotations on the expressions
  * after modifications.</p>
  *
  * @author Igor Konnov
  */
@Singleton
class TrivialTypeFinder extends TypeFinder[CellT] with TransformationListener {
  private var varTypes: SortedMap[String, CellT] = SortedMap()
  private var typeAnnotations: Map[UID, CellT] = Map()
  private var errors: Seq[TypeInferenceError] = Seq()

  /**
    * Get the types of the variables that are computed by inferAndSave. The method must return the types of
    * the global variables (VARIABLE and CONSTANT) and it may return types of the bound variables.
    *
    * @return a mapping of names to types
    */
  override def getVarTypes: SortedMap[String, CellT] = varTypes

  /**
    * Restore variable types from a map.
    *
    * @param newVarTypes a mapping of names to types
    */
  override def setVarTypes(newVarTypes: SortedMap[String, CellT]): Unit = {
    varTypes = newVarTypes
  }

  /**
    * Forget all computed types and introduce types for the variables. You can call inferAndSave after that.
    *
    * @param newVarTypes types of the global variables (VARIABLE and CONSTANT)
    */
  override def reset(newVarTypes: Map[String, CellT]): Unit = {
    varTypes = SortedMap(newVarTypes.toSeq: _*)
    typeAnnotations = Map()
    errors = Seq()
  }

  /**
    * Record the cell name and its type.
    *
    * @param cell an arena cell
    */
  def extendWithCellType(cell: ArenaCell): Unit = {
    varTypes += cell.toString -> cell.cellType
  }

  override def onTransformation(originalEx: TlaEx, newEx: TlaEx): Unit = {
    typeAnnotations.get(originalEx.ID) match {
        // propagate type annotations
      case Some(tp) => typeAnnotations += newEx.ID -> tp
      case _ => ()
    }
  }

  /**
    * Given a TLA+ expression, reconstruct the types and store them in an internal storage.
    * If the expression is not well-typed, diagnostic messages can be accessed with getTypeErrors.
    * The main goal of this method is to assign types to the free and bound variables
    * as we do not consider operators. (We allow nullary LET-IN operators though).
    *
    * @param expr a TLA+ expression.
    * @return Some(type), if successful, and None otherwise
    */
  override def inferAndSave(expr: TlaEx): Option[CellT] = {
    // This class implements a very simple form of type inference from bottom to top.
    // As soon as we cannot infer types, we complain that the type annotations are not good enough.
    expr match {
      // LET A == ... IN
      // LET B == ... IN
      // ...
      // IN Z
      case letIn @ LetInEx(body, defs @ _*) =>
        def inferDefResultType(d: TlaOperDecl): Unit = {
          if (d.formalParams.nonEmpty) {
            // This is a critical error in our code, which is not a type inference error
            throw new IllegalStateException(s"Found a non-constant LET-IN definition ${d.name}, which should have been expanded")
          } else {
            val resT = inferAndSave(d.body)
            // Bind the let name to the computed type of the result.
            // XXX: It is not a type of a variable, which may confuse the model checker.
            varTypes += d.name -> resT.getOrElse(UnknownT())
          }
        }

        defs foreach inferDefResultType
        inferAndSave(body) // body may use the types of the let definitions

      // x' = e
      // x' \in S
      case OperEx(BmcOper.assign, OperEx(TlaActionOper.prime, NameEx(varName)), rhs) =>
        def assignTypeAndReturnBool(assignedType: CellT): Option[CellT] = {
          val primedVar = varName + "'"
          if (varTypes.contains(primedVar)) {
            if (varTypes(primedVar) != assignedType) {
              val e = new TypeInferenceError(expr,
                "Assigning a type %s, while assigned type %s earlier"
                  .format(assignedType, varTypes(primedVar)))
              addError(e)
            }
          } else {
            varTypes = varTypes + (primedVar -> assignedType)
          }
          Some(BoolT())
        }

        inferAndSave(rhs) match {
          case Some(tp) =>
            assignTypeAndReturnBool(tp)
          case tp@None =>
            addError(new TypeInferenceError(rhs, "Expected a type, found: " + tp))
            None
        }

      // { x \in S: e }
      case OperEx(TlaSetOper.filter, NameEx(x), set, pred) =>
        inferAndSave(set) match {
          case Some(setT@FinSetT(elemT)) =>
            assert(!varTypes.contains(x))
            varTypes = varTypes + (x -> elemT)
            val predT = inferAndSave(pred)
            if (predT.contains(BoolT())) {
              Some(setT)
            } else {
              addError(new TypeInferenceError(pred, "Expected a Boolean, found: " + predT))
              None
            }

          case tp@_ =>
            addError(new TypeInferenceError(set, "Expected a set, found: " + tp))
            varTypes = varTypes + (x -> UnknownT()) // otherwise, the type rewriter may throw an exception
            None
        }

      // {e : x \in S}
      case OperEx(TlaSetOper.map, mapEx, varsAndSets@_*) =>
        val names = varsAndSets.zipWithIndex.collect { case (NameEx(n), i) if i % 2 == 0 => n }
        val sets = varsAndSets.zipWithIndex.collect { case (e, i) if i % 2 == 1 => e }

        def bind(name: String, set: TlaEx): Unit = {
          inferAndSave(set) match {
            case Some(setT@FinSetT(elemT)) =>
              assert(!varTypes.contains(name))
              varTypes = varTypes + (name -> elemT)

            case Some(PowSetT(setT@FinSetT(_))) =>
              assert(!varTypes.contains(name))
              varTypes = varTypes + (name -> setT)

            case tp@_ =>
              addError(new TypeInferenceError(set, "Expected a set, found: " + tp))
              varTypes = varTypes + (name -> UnknownT()) // otherwise, the type rewriter may throw an exception
          }
        }

        names.zip(sets) foreach (bind _).tupled
        Some(FinSetT(inferAndSave(mapEx).getOrElse(UnknownT())))

      // [x \in S |-> e]
      case OperEx(TlaFunOper.funDef, funEx, varsAndSets@_*) =>
        val names = varsAndSets.zipWithIndex.collect { case (NameEx(n), i) if i % 2 == 0 => n }
        val sets = varsAndSets.zipWithIndex.collect { case (e, i) if i % 2 == 1 => e }

        def bind(name: String, set: TlaEx): Unit = {
          inferAndSave(set) match {
            case Some(setT@FinSetT(elemT)) =>
              assert(!varTypes.contains(name))
              varTypes = varTypes + (name -> elemT)

            case tp@_ =>
              addError(new TypeInferenceError(set, "Expected a set, found: " + tp))
              varTypes = varTypes + (name -> UnknownT()) // otherwise, the type rewriter throws an exception 10 lines below
          }
        }

        names.zip(sets) foreach (bind _).tupled
        val resT = inferAndSave(funEx).getOrElse(UnknownT())
        val domT =
          if (names.length == 1) {
            // a function of one argument
            FinSetT(varTypes(names.head))
          } else {
            // a function of multiple arguments is a function from a Cartesian product to the result type
            FinSetT(TupleT(names.map(varTypes(_))))
          }
        Some(FunT(domT, resT))

      // exists, forall, or CHOOSE
      case OperEx(op, NameEx(x), set, pred)
        if op == TlaBoolOper.exists || op == TlaBoolOper.forall || op == TlaOper.chooseBounded =>
        inferAndSave(set) match {
          case Some(setT@FinSetT(elemT)) =>
            assert(!varTypes.contains(x))
            varTypes = varTypes + (x -> elemT)
            val predT = inferAndSave(pred)
            if (predT.contains(BoolT())) {
              if (op == TlaOper.chooseBounded) {
                Some(elemT) // CHOOSE
              } else {
                Some(BoolT()) // exists/forall
              }
            } else {
              addError(new TypeInferenceError(pred, "Expected a Boolean, found: " + predT))
              None
            }

          case tp@_ =>
            addError(new TypeInferenceError(set, "Expected a set, found: " + tp))
            varTypes = varTypes + (x -> UnknownT()) // otherwise, the type rewriter may throw an exception
            None
        }

      // a type annotation
      case OperEx(BmcOper.withType, ex, annot) =>
        val exT = inferAndSave(ex)
        val annotT = AnnotationParser.fromTla(annot)
        val unifier = unifyOption(Some(annotT), exT)
        if (unifier.isDefined) {
          // save the type annotation and return the type
          typeAnnotations += (ex.ID -> unifier.get)
          unifier
        } else {
          val exTStr = if (exT.isDefined) exT.get.toString else None.toString
          addError(new TypeInferenceError(annot,
            s"No unifier for type $annotT and type $exTStr (from type annotation $annot and expression $ex)"))
          None
        }

      case OperEx(TlaActionOper.prime, NameEx(name)) =>
        val primed = name + "'"
        val result = varTypes.get(primed)
        if (result.isEmpty) {
          addError(new TypeInferenceError(expr, s"Failed to find type of variable $primed"))
        }
        result

      case ex@OperEx(TlaActionOper.prime, arg) =>
        Some(error(ex, "Expected a name under ', found: " + arg))

      // other operators
      case OperEx(_, args@_*) =>
        val argTypes = args.map(inferAndSave)
        if (argTypes.forall(_.isDefined)) {
          try {
            Some(compute(expr, argTypes.map(_.get): _*))
          } catch {
            case e: TypeInferenceError =>
              addError(e)
              None
          }
        } else {
          None
        }

      case NameEx(name) =>
        var result = varTypes.get(name)
        if (result.isEmpty) {
          // TODO: this is a temporary solution until the moment we have eliminated BoolTheory and IntTheory
          if (IntTheory().hasConst(name)) {
            result = Some(IntT())
          } else if (BoolTheory().hasConst(name)) {
            result = Some(BoolT())
          } else {
            addError(new TypeInferenceError(expr, "Failed to find type of variable " + name))
          }
        }
        result

      case ValEx(_) =>
        try {
          Some(compute(expr))
        } catch {
          case e: TypeInferenceError =>
            addError(e)
            None
        }

      case _ =>
        None
    }
  }

  /**
    * Retrieve the type errors from the latest call to inferAndSave.
    *
    * @return a list of type errors
    */
  override def getTypeErrors: Seq[TypeInferenceError] = errors

  /**
    * Call compute recursively to compute the type of a given expression. This function is expensive,
    * use it only when absolutely necessary.
    *
    * @param ex a TLA+ expression
    * @return the resulting type
    */
  override def computeRec(ex: TlaEx): CellT = ex match {
    case OperEx(BmcOper.withType, annotated, _) =>
      // a pre-computed type annotation overrides the type info
      assert(typeAnnotations.contains(annotated.ID)) // otherwise, the engine is broken
      typeAnnotations(annotated.ID)

    case OperEx(TlaActionOper.prime, NameEx(_)) =>
      // do not recurse in prime, as the type of a primed variable should be computed directly
      compute(ex)

    case OperEx(_, args@_*) =>
      compute(ex, args map computeRec: _*)

    case _ =>
      compute(ex)
  }

  /**
    * Given a TLA+ expression and the types of its arguments, compute the resulting type, if possible.
    *
    * @param ex       a TLA+ expression
    * @param argTypes the types of the arguments.
    * @return the resulting type, if it can be computed
    * @throws TypeInferenceError if the type cannot be computed.
    */
  override def compute(ex: TlaEx, argTypes: CellT*): CellT = {
    if (typeAnnotations.contains(ex.ID)) {
      // this expression has been annotated with a type
      typeAnnotations(ex.ID)
    } else {
      // chain partial functions to handle different types of operators with different functions
      val handlers =
        (computeValues
          :: computeBasicOps(argTypes)
          :: computeBoolOps(argTypes)
          :: computeIntOps(argTypes)
          :: computeControlOps(argTypes)
          :: computeSetCtors(argTypes)
          :: computeFunCtors(argTypes)
          :: computeSetOps(argTypes)
          :: computeFunOps(argTypes)
          :: computeFunApp(argTypes)
          :: computeFiniteSetOps(argTypes)
          :: computeSeqOps(argTypes)
          :: computeMiscOps(argTypes)
          :: notImplemented :: Nil) reduceLeft (_ orElse _)
      handlers(ex)
    }
  }

  private def computeValues: PartialFunction[TlaEx, CellT] = {
    case ValEx(TlaInt(_)) =>
      IntT()

    case ValEx(TlaBool(_)) =>
      BoolT()

    case ValEx(TlaStr(_)) =>
      ConstT()

    case ValEx(TlaNatSet) =>
      FinSetT(IntT())

    case ValEx(TlaIntSet) =>
      FinSetT(IntT())
  }

  private def computeBasicOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ne@NameEx(name) =>
      varTypes.get(name)
        .orElse(Some(error(ne, "No type assigned to " + name)))
        .get

    case app @ OperEx(TlaOper.apply, NameEx(opName)) =>
      varTypes.get(opName.toString) // String.toString ??
        .orElse(Some(error(app, "No type assigned to " + opName)))
        .get

    case OperEx(TlaOper.apply, opName, _*) =>
        throw new IllegalStateException(s"Unexpected operator call to $opName. Report a bug!")

    case ne@OperEx(TlaActionOper.prime, NameEx(name)) =>
      val primed = name + "'"
      varTypes.get(primed)
        .orElse(Some(error(ne, "No type assigned to " + primed)))
        .get

    case ex@OperEx(op, _, _)
      if op == TlaOper.eq || op == TlaOper.ne =>
      expectEqualTypes(ex, argTypes: _*)
      BoolT()

    case ex@OperEx(op@TlaOper.chooseBounded, x, set, pred) =>
      val xType = argTypes.head
      val setType = argTypes.tail.head
      val predType = argTypes.tail.tail.head
      setType match {
        case FinSetT(elemT) =>
          expectType(elemT, x, xType)
          expectType(BoolT(), pred, predType)
          elemT

        case _ =>
          errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op@TlaOper.chooseUnbounded, x, pred) =>
      val xType = argTypes.head
      val predType = argTypes.tail.head
      expectType(BoolT(), pred, predType)
      xType

    case ex@OperEx(op@TlaOper.chooseIdiom, _) =>
      argTypes match {
        case Seq(FinSetT(elemT)) =>
          elemT

        case _ =>
          errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op@TlaOper.label, _, _, _*) =>
      val decoratedExprType = argTypes.head
      val nameAndArgTypes = argTypes.tail
      nameAndArgTypes.foreach(expectType(ConstT(), ex, _))
      decoratedExprType
  }

  private def computeSetCtors(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(TlaSetOper.enumSet, _*) =>
      if (argTypes.isEmpty) {
        // This case typically causes problems, as any operation with
        // a concrete type would fail. One has to use a type annotation.
        FinSetT(UnknownT())
      } else {
        expectEqualTypes(ex, argTypes: _*)
        FinSetT(argTypes.head)
      }

    case ex@OperEx(op@TlaSetOper.funSet, _, _) =>
      argTypes match {
        case Seq(FinSetT(argT), FinSetT(resT)) =>
          // FinT expects the types of the domain and the result (not of the co-domain!)
          FinSetT(FunT(FinSetT(argT), resT))

        case _ => errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(TlaSetOper.recSet, args@_*) =>
      assert(argTypes.nonEmpty)
      val fieldNames = deinterleave(args, 0, 2)
        .collect { case ValEx(TlaStr(a)) => a }
      val _, fieldTypes = deinterleave(argTypes, 1, 2)
      val elemTypes = argTypes.collect { case FinSetT(t) => t }
      if (elemTypes.size < fieldTypes.size) {
        error(ex, "Only explicit sets are supported in sets of records")
      }
      assert(fieldNames.length == fieldTypes.length)
      FinSetT(RecordT(SortedMap(fieldNames.zip(elemTypes): _*)))

    case ex@OperEx(op@TlaSetOper.powerset, _) =>
      argTypes match {
        case Seq(FinSetT(elemT)) =>
          FinSetT(FinSetT(elemT))

        // what about SUBSET [S -> T]?

        case _ => errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(TlaSetOper.times, _*) =>
      assert(argTypes.nonEmpty)
      val elemTypes = argTypes.collect({ case FinSetT(t) => t }) // using partial functions
      if (elemTypes.size < argTypes.size) {
        error(ex, "Only explicit sets are supported in Cartesian products")
      }
      FinSetT(TupleT(elemTypes))

    case ValEx(TlaBoolSet) => // BOOLEAN
      FinSetT(BoolT())
  }

  private def computeSetOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(op@TlaSetOper.union, _) =>
      argTypes match {
        case Seq(FinSetT(FinSetT(elemT))) =>
          FinSetT(elemT)

        case _ => errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op@TlaSetOper.filter, _, _, _) =>
      argTypes match {
        case Seq(_, FinSetT(elemT), BoolT()) =>
          FinSetT(elemT)

        case Seq(_, PowSetT(elemT), BoolT()) =>
          FinSetT(elemT) // powersets are expanded

        // what about {f \in [S -> T] : ... }?
        // what about {f \in [a: S, B: T] |-> ... }?

        case _ => errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op@TlaSetOper.map, _*) =>
      var varType: CellT = UnknownT()
      for ((tp, index) <- argTypes.tail.zipWithIndex) {
        if (index % 2 == 0) {
          varType = tp // save the type of the bound variable
        }
        if (index % 2 == 1) {
          tp match {
            case FinSetT(et) =>
              if (et != varType) {
                error(ex, "Expected Set(%s) at position %d, found: %s".format(varType, index / 2, tp))
              }

            // what about {f \in [S -> T] |-> ... }?
            // what about {f \in [a: S, B: T] |-> ... }?
            case _ => errorUnexpected(ex, op.name, argTypes)
          }
        }
      }
      FinSetT(argTypes.head)

    case ex@OperEx(op, _, _) if op == TlaSetOper.in || op == TlaSetOper.notin =>
      argTypes match {
        case Seq(memT, FinSetT(elemT)) =>
          expectEqualTypes(ex, memT, elemT)
          BoolT()

        // what about f \in [S -> T]?
        // what about f \in [a: S, B: T]?

        case _ => errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op, _, _)
      if op == TlaSetOper.subsetProper || op == TlaSetOper.subseteq
        || op == TlaSetOper.supsetProper || op == TlaSetOper.supseteq =>
      argTypes match {
        case Seq(FinSetT(leftT), FinSetT(rightT)) =>
          expectEqualTypes(ex, leftT, rightT)
          BoolT()

        // what about f \in [S -> T]?
        // what about f \in [a: S, B: T]?
        case _ => errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op, _, _)
      if op == TlaSetOper.cup || op == TlaSetOper.cap || op == TlaSetOper.setminus =>
      argTypes match {
        case Seq(FinSetT(leftT), FinSetT(rightT)) =>
          expectEqualTypes(ex, leftT, rightT)
          FinSetT(leftT)

        case _ => errorUnexpected(ex, op.name, argTypes)
      }
  }

  private def computeFunCtors(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(TlaFunOper.tuple) =>
      SeqT(UnknownT())

    case ex@OperEx(op@TlaFunOper.tuple, _*) =>
      TupleT(argTypes)

    case ex@OperEx(op@TlaFunOper.enum, args@_*) =>
      assert(argTypes.nonEmpty)
      val fieldNames = deinterleave(args, 0, 2) collect { case ValEx(TlaStr(a)) => a }
      val namesTypes = deinterleave(argTypes, 0, 2) collect { case ConstT() => true }

      if (namesTypes.size != fieldNames.size) {
        errorUnexpected(ex, op.name, argTypes)
      }
      val fieldTypes = deinterleave(argTypes, 1, 2)
      assert(fieldNames.length == fieldTypes.length)
      RecordT(SortedMap(fieldNames.zip(fieldTypes): _*))
  }

  private def computeFunApp(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(op@TlaFunOper.app, fun, arg) =>
      val funType = argTypes.head
      val argType = argTypes.tail.head
      funType match {
        case FunT(FinSetT(funArgT), funResT) if funArgT == argType =>
          funResT

        case SeqT(resT) if argType == IntT() =>
          resT

        case TupleT(elemTypes) if argType == IntT() =>
          // try to extract an integer from the expression
          arg match {
            case ValEx(TlaInt(i)) =>
              if (i >= 1 && i <= elemTypes.length) {
                elemTypes(i.toInt - 1) // the argument is within a small range, so toInt should work
              } else {
                error(ex, "The tuple argument is out of range: " + i)
              }

            case _ => error(ex, "Expected an integer constant as the tuple argument, found: " + arg)
          }

        case RecordT(fields) if argType == ConstT() =>
          // try to extract a string from the expression
          arg match {
            case ValEx(TlaStr(s)) =>
              if (fields.contains(s)) {
                fields(s)
              } else {
                error(ex, "Unexpected record field name: " + s)
              }

            case _ => error(ex, "Expected a string constant as the tuple argument, found: " + arg)
          }

        case _ =>
          errorUnexpected(ex, op.name, argTypes)
      }
  }

  private def computeFunOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(op@TlaFunOper.funDef, e, bindings@_*) =>
      val resType = argTypes.head
      val setTypes = deinterleave(argTypes.tail, 1, 2)
      val varTypes = deinterleave(argTypes.tail, 0, 2)
      if (varTypes.length != setTypes.length) {
        errorUnexpected(ex, op.name, argTypes)
      } else {
        val elemTypes = setTypes.collect { case FinSetT(et) => et }
        if (elemTypes.length != setTypes.length) {
          // wrong types were passed
          errorUnexpected(ex, op.name, argTypes)
        }
        if (setTypes.length == 1) {
          // a single-argument function
          FunT(setTypes.head, resType)
        } else {
          // a multi-argument function, which means it receives a Cartesian product
          FunT(FinSetT(TupleT(elemTypes)), resType)
        }
      }

    case ex@OperEx(op@TlaFunOper.except, e, bindings@_*) =>
      val funType = argTypes.head
      // In principle, we could just return the function itself.
      // But we also check the argument types to be on a well-typed side.
      val indices = deinterleave(bindings, 0, 2) // the expressions
    val indexTypes = deinterleave(argTypes.tail, 0, 2)
      val valueTypes = deinterleave(argTypes.tail, 1, 2)
      funType match {
        case FunT(_, _) =>
          val (argT, resT) =
            funType match {
              // an argument to EXCEPT is always wrapped into a tuple
              case FunT(FinSetT(elemT), rt) => (TupleT(Seq(elemT)), rt)
              case _ => error(ex, "Expected a function type, found: " + funType)
            }
          for (idx <- indexTypes) {
            if (idx != argT) {
              error(ex, "Expected an index of type TupleT(%s), found: %s".format(argT, idx))
            }
          }
          for (valT <- valueTypes) {
            if (valT != resT) {
              error(ex, "Expected a result of type %s, found: %s".format(resT, valT))
            }
          }

        case rec@RecordT(_) =>
          for (idx <- indexTypes) {
            if (idx != TupleT(Seq(ConstT()))) {
              error(ex, "Expected an index of type %s, found: %s".format(ConstT(), idx))
            }
          }
          for ((index, valT) <- indices.zip(valueTypes)) {
            index match {
              case OperEx(TlaFunOper.tuple, ValEx(TlaStr(key))) =>
                if (valT != rec.fields(key)) {
                  error(ex, "Expected an index of type TupleT(%s), found: %s".format(rec.fields(key), valT))
                }

              case _ =>
                error(ex, s"Expected a record key, found: $index")
            }

          }

        case tup@TupleT(Seq(argTypes@_*)) =>
          for (idx <- indexTypes) {
            if (idx != TupleT(Seq(IntT()))) {
              error(ex, "Expected an index of type TupleT(%s), found: %s".format(IntT(), idx))
            }
          }
          for ((argT, valT) <- argTypes.zip(valueTypes)) {
            if (argT != valT) {
              error(ex, "Expected a value of type %s, found: %s".format(argT, valT))
            }
          }

        case _ =>
          error(ex, "Expected a function, a record, or a tuple")
      }

      funType

    case ex@OperEx(TlaFunOper.domain, fun) =>
      argTypes.head match {
        case FunT(domT, _) => domT
        case TupleT(_) => FinSetT(IntT())
        case RecordT(_) => FinSetT(ConstT())
        case SeqT(_) => FinSetT(IntT())
        case _ => error(ex, "Unexpected type of DOMAIN argument: " + ex)
      }
  }

  private def computeIntOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(op, _) if op == TlaArithOper.uminus =>
      assert(argTypes.length == 1)
      expectType(IntT(), ex, argTypes.head)
      IntT()

    case ex@OperEx(TlaArithOper.dotdot, _, _) =>
      assert(argTypes.length == 2)
      argTypes.foreach(expectType(IntT(), ex, _))
      FinSetT(IntT())

    case ex@OperEx(op, _, _)
      if op == TlaArithOper.plus || op == TlaArithOper.minus
        || op == TlaArithOper.mult || op == TlaArithOper.div || op == TlaArithOper.mod || op == TlaArithOper.exp =>
      assert(argTypes.length == 2)
      argTypes.foreach(expectType(IntT(), ex, _))
      IntT()

    case ex@OperEx(op, _, _)
      if op == TlaArithOper.lt || op == TlaArithOper.gt || op == TlaArithOper.le || op == TlaArithOper.ge =>
      assert(argTypes.length == 2)
      argTypes.foreach(expectType(IntT(), ex, _))
      BoolT()

    case ex@OperEx(op, _*)
      if op == TlaArithOper.sum || op == TlaArithOper.prod =>
      argTypes.foreach(expectType(IntT(), ex, _))
      IntT()
  }

  private def computeBoolOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(TlaBoolOper.not, _) =>
      assert(argTypes.length == 1)
      expectType(BoolT(), ex, argTypes.head)
      BoolT()

    case ex@OperEx(op, _, _)
      if op == TlaBoolOper.implies || op == TlaBoolOper.equiv =>
      assert(argTypes.length == 2)
      argTypes.foreach(expectType(BoolT(), ex, _))
      BoolT()

    case ex@OperEx(op, _*)
      if op == TlaBoolOper.and || op == TlaBoolOper.or =>
      argTypes.foreach(expectType(BoolT(), ex, _))
      BoolT()

    case ex@OperEx(op, x, set, pred) if op == TlaBoolOper.forall || op == TlaBoolOper.exists =>
      val xType = argTypes.head
      val setType = argTypes.tail.head
      val predType = argTypes.tail.tail.head
      expectType(BoolT(), pred, predType)
      setType match {
        case FinSetT(elemT) =>
          expectType(elemT, x, xType)

        case _ =>
          errorUnexpected(set, op.name, argTypes)
      }
      BoolT()
  }

  private def computeControlOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
      assert(argTypes.length == 3)
      expectType(BoolT(), predEx, argTypes.head)
      val leftType = argTypes.tail.head
      expectEqualTypes(ex, argTypes.tail: _*)
      leftType

    case ex@OperEx(TlaControlOper.caseNoOther, _*) =>
      val guards = argTypes.zipWithIndex.collect { case (a, i) if i % 2 == 0 => a }
      val actions = argTypes.zipWithIndex.collect { case (a, i) if i % 2 == 1 => a }
      guards.foreach(expectType(BoolT(), ex, _))
      expectEqualTypes(ex, actions: _*)
      actions.head

    case ex@OperEx(TlaControlOper.caseWithOther, _*) =>
      val guards = argTypes.zipWithIndex.collect { case (a, i) if i % 2 == 1 => a }
      val actions = argTypes.zipWithIndex.collect { case (a, i) if i % 2 == 0 => a }
      guards.foreach(expectType(BoolT(), ex, _))
      expectEqualTypes(ex, actions: _*)
      actions.head

    case ex @ LetInEx(_, _*) =>
      // Can we really type-check anything here? We would need to analyze the let bindings.
      argTypes.head
  }

  private def computeFiniteSetOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(op, _)
      if op == TlaFiniteSetOper.isFiniteSet || op == TlaFiniteSetOper.cardinality =>
      assert(argTypes.length == 1)
      argTypes.head match {
        case FinSetT(_) =>
          if (op == TlaFiniteSetOper.isFiniteSet)
            BoolT()
          else
            IntT()

        case _ =>
          errorUnexpected(ex, op.name, argTypes)
      }
  }

  private def computeSeqOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(op, _)
      if op == TlaSeqOper.head || op == TlaSeqOper.tail || op == TlaSeqOper.len =>
      assert(argTypes.length == 1)
      argTypes.head match {
        case SeqT(elemT) =>
          if (op == TlaSeqOper.head)
            elemT
          else if (op == TlaSeqOper.tail)
            SeqT(elemT)
          else IntT() // len

        case _ =>
          errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op@TlaSeqOper.append, _, argEx) =>
      assert(argTypes.length == 2)
      argTypes.head match {
        case SeqT(elemT) =>
          expectType(elemT, argEx, argTypes.tail.head)
          SeqT(elemT)

        case _ =>
          errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op@TlaSeqOper.concat, lex, rex) =>
      assert(argTypes.length == 2)
      argTypes.head match {
        case SeqT(elemT) =>
          expectType(SeqT(elemT), rex, argTypes.tail.head)
          SeqT(elemT)

        case _ =>
          errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op@TlaSeqOper.subseq, seq, start, end) =>
      assert(argTypes.length == 3)
      argTypes.head match {
        case SeqT(elemT) =>
          expectType(IntT(), start, argTypes.tail.head)
          expectType(IntT(), end, argTypes.tail.tail.head)
          SeqT(elemT)

        case _ =>
          errorUnexpected(ex, op.name, argTypes)
      }

    case ex@OperEx(op@TlaSeqOper.selectseq, seq, pred) =>
      // pred should be a second-level operator. How would we implement it here?
      throw new NotImplementedError("Type construction for Sequence.selectseq cannot be implemented.")
  }

  private def computeMiscOps(argTypes: Seq[CellT]): PartialFunction[TlaEx, CellT] = {
    case ex@OperEx(BmcOper.`skolem`, _) =>
      BoolT()

    case ex@OperEx(BmcOper.expand, _) =>
      argTypes.head

    case ex@OperEx(TlaOper.label, args@_*) =>
      for ((a, t) <- args.tail.zip(argTypes.tail)) expectType(ConstT(), a, t)
      argTypes.head

    case ex@OperEx(TlcOper.assert, expr, msg) =>
      val exprType = argTypes.head
      val msgType = argTypes.tail.head
      expectType(BoolT(), expr, exprType)
      expectType(ConstT(), msg, msgType)
      BoolT()

    case ex@OperEx(TlcOper.print, _, msg) =>
      // an expression can be of any type
      val msgType = argTypes.tail.head
      expectType(ConstT(), msg, msgType)
      BoolT()

    case ex@OperEx(TlcOper.printT, msg) =>
      val msgType = argTypes.head
      expectType(ConstT(), msg, msgType)
      BoolT()

    case ex@OperEx(TlcOper.colonGreater, _, _) =>
      TupleT(argTypes) // a :> b is simply <<a, b>> in our type system

    case ex@OperEx(TlcOper.atat, _, _) =>
      argTypes.head match {
        case funT@FunT(FinSetT(argT), resT) =>
          argTypes.tail.head match {
            case TupleT(Seq(at, rt)) =>
              expectEqualTypes(ex, argT, at)
              expectEqualTypes(ex, resT, rt)
              funT

            case tt@_ =>
              expectType(TupleT(Seq(argT, resT)), ex, tt)
              funT
          }

        case _ =>
          errorUnexpected(ex, TlcOper.atat.name, argTypes)
      }

    case ex@OperEx(BmcOper.withType, _*) =>
      throw new IllegalStateException("The type annotation must have been saved by inferAndSave: " + ex)
  }

  private def expectType(expectedType: CellT, ex: TlaEx, exType: CellT): Unit = {
    if (exType != expectedType) {
      error(ex, "Expected type %s, found %s".format(expectedType, exType))
    }
  }

  private def expectEqualTypes(ex: TlaEx, types: CellT*): Unit = {
    if (types.nonEmpty) {
      val firstType = types.head

      if (types.tail.exists(_ != firstType)) {
        error(ex, "Expected equal types: %s".format(types.mkString(" and ")))
      }
    }
  }

  private def errorUnexpected(ex: TlaEx, opname: String, argTypes: Seq[CellT]): CellT = {
    error(ex, "Unexpected types for %s: %s".format(opname, argTypes.mkString(", ")))
  }

  private def error(ex: TlaEx, message: String): CellT = {
    throw new TypeInferenceError(ex, message)
  }

  private def notImplemented: PartialFunction[TlaEx, CellT] = {
    case ex => throw new NotImplementedError("Type construction for %s is not implemented. Report a bug!".format(ex))
  }

  private def addError(error: TypeInferenceError): Unit = {
    errors :+= error
  }

  /**
    * Get a subsequence of elements whose indices satisfy the predicate: index % base == group.
    *
    * @param s     sequence
    * @param group the group number (from 0 to base - 1)
    * @param base  the divider to use in the modulo operation
    * @tparam T element type
    * @return the subsequence of s s.t. index % base == group
    */
  private def deinterleave[T](s: Seq[T], group: Int, base: Int): Seq[T] = {
    s.zipWithIndex.collect { case (e, i) if i % base == group => e }
  }
}
