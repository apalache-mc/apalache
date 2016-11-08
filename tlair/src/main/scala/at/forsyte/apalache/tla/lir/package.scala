package at.forsyte.apalache.tla

package lir {
  import at.forsyte.apalache.tla.lir.oper._

import scala.collection.immutable.HashMap
import scala.collection.parallel.mutable

/** the base class for the universe of objects used in TLA+ */
  abstract class TlaValue

  /** a constant as defined by CONSTANT */
  class TlaConst(val name: String) extends TlaValue

  /** a variable as defined by VARIABLE */
  class TlaVar(val name: String) extends TlaValue


  abstract class ScopeSymbol {
    def name: String
  }

  // declare a for LET a = ... IN...
  case class ScopeLetVariable(param: SimpleParam) extends ScopeSymbol {
    override def name: String = param.name
  }
  // declare x for \forall x \in X. ...
  case class ScopeBoundVariable(param: SimpleParam) extends ScopeSymbol {
    override def name: String = param.name
  }
  // an operator parameter
  case class ScopeFormalParameter(param: Param) extends ScopeSymbol {
    override def name: String = param.name
  }
  // a variable
  case class ScopeVariable(tlaVar: TlaVar) extends ScopeSymbol {
    override def name: String = tlaVar.name
  }
  // a constant
  case class ScopeConstant(const: TlaConst) extends ScopeSymbol {
    override def name: String = const.name
  }
  // an operator definition
  case class ScopeOper(operDef: TlaOperDef) extends ScopeSymbol {
    override def name: String = operDef.name
  }

  // a lookup exception
  class SymbolNotFoundException(val msg: String) extends RuntimeException

  /**
   *  A scope in which constants and variables are declared.
   */
  trait TlaScope {
    def add(sym: ScopeSymbol): Unit
    def remove(name: String): Unit
    def exists(name: String): Boolean
    def lookup(name: String): ScopeSymbol // throws SymbolNotFoundException
  }

  class FlatScope extends TlaScope {
    var map = HashMap.empty[String, ScopeSymbol]

    override def add(sym: ScopeSymbol) = {
      map = map + ((sym.name, sym))
    }

    override def remove(name: String) = {
      map = map - name
    }

    override def exists(name: String): Boolean = {
      map.contains(name)
    }

    override def lookup(name: String): ScopeSymbol = {
      map.get(name) match {
        case Some(s) => s
        case None => throw new SymbolNotFoundException("Symbol %s not found".format(name))
      }
    }
  }

  class ScopeStack extends TlaScope {
    var scopes: List[TlaScope] = List()

    override def add(sym: ScopeSymbol) = {
      scopes.head.add(sym)
    }

    override def remove(name: String) = {
      scopes.find { s => s.exists(name) } match {
        case Some(s) => s.remove(name)
        case None => ()
      }
    }

    override def lookup(name: String) = {
      def search(s: Seq[TlaScope]): ScopeSymbol = {
        s match {
          case Seq() =>
            throw new SymbolNotFoundException("Symbol %s not found".format(name))

          case hd :: tl =>
            try {
              hd.lookup(name)
            } catch {
              case _: SymbolNotFoundException => search(tl)
            }
        }
      }
      search(scopes)
    }

    override def exists(name: String) = {
      try {
        lookup(name)
        true
      } catch {
        case _: SymbolNotFoundException =>
          false
      }
    }

    def push(s: TlaScope) = {
      scopes = s :: scopes
    }

    def pop(): Unit = {
      if (scopes.isEmpty) throw new IllegalStateException("Empty scope stack")
      else scopes = scopes.tail
    }
  }

  /**
   * A module is just an hierarchical scope.
   */
  class Module(val name: String, val imported: Seq[Module]) extends ScopeStack {
    for (m <- imported) {
      push(m)
    }
    push(new FlatScope)
  }


  /**
  A formal parameter of an operator. Note that one can use a formal parameter in a TLA+ expression,
        and thus FormalParam inherits from TlaValue.
    */
  abstract class Param {
    def name: String
    def arity: OperArity
  }

  /** An ordinary expression, e.g., x */
  case class SimpleParam(name: String) extends Param {
    override def arity: OperArity = FixedArity(0)
  }

  /** A function signature, e.g., f(_, _) */
  case class OperParam(name: String, arity: OperArity) extends Param with TlaOper {
    override def interpretation: Interpretation.Value = Interpretation.Signature

    require(arity match { case FixedArity(_) => true; case _ => false }, "Formal parameters should have fixed arity")
  }

  /** A TLA+ expression */
  abstract class TlaEx

  /** just using a TLA+ value */
  case class ValEx(value: TlaValue) extends TlaEx

  /** applying an operator, including the one defined by OperFormalParam */
  case class OperEx(oper: TlaOper, args: TlaEx*) extends TlaEx {
    require(oper.isCorrectArity(args.size), "unexpected arity %d".format(args.size))
    require(oper.areCompatibleArgs(args: _*), "the arguments are not compatible with the operator signature")
  }

  /** converting an operator into a value (to pass an operator as an argument of another operator) */
  case class OperRefEx(oper: TlaOper) extends TlaEx

  /**
    Using a formal parameter, which is not an OperFormalParam.

    TODO: we don't like it, find a better solution. The problem is that one has to write SimpleParamEx(SimpleParam("x"))
      to refer to a formal parameter.
    */
  case class SimpleParamEx(param: SimpleParam)


  /** An operator definition, e.g. A == 1 + 2, or B(x, y) == x + y, or (C(f(_, _), x, y) == f(x, y) */
  class TlaOperDef(val name: String, val formalParams: List[Param], val body: TlaEx) {
    val operName = name
    def createOperator(): TlaOper = {
      // TODO: maybe we should define a user-instantiated operator instead of an anonymous class
      new TlaOper {
        override def arity: OperArity = FixedArity(formalParams.length)
        override def interpretation: Interpretation.Value = Interpretation.User
        override def name: String = operName

        override def areCompatibleArgs(args: TlaEx*): Boolean = {
          def isArgGood(pair: Tuple2[Param, TlaEx]) = {
            (pair._1, pair._2) match {
              case (_: SimpleParam, _: ValEx) => true
              case (_: SimpleParam, _: OperEx) => true
              case (_: OperParam, _: OperRefEx) => true
              case _ => false
            }
          }
          (formalParams zip args).forall(isArgGood)
        }
      }
    }
  }

}
