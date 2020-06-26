package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.smt.SmtTools.{And, BoolFormula}
import at.forsyte.apalache.tla.lir.storage.{BodyMap, BodyMapFactory}
import at.forsyte.apalache.tla.types.smt.SmtVarGenerator


/**
  * Generates templates for user-defined operators
  *
  * A user-defined operator template differs from a built-in operator template, because
  * the operator type is not known in advance. We therefore defer the analysis of user-defined
  * operator application to a structure-reduction over the TlaEx intermediate expression of the operator body,
  * which iteratively calls built-in operator templates for the built-in operators
  * used in the body ( or other user-defined operator templates ). Eventually, this process
  * terminates in either TLA+ literals or variables, for which types/typeVariables are known
  */
class UserDefinedTemplateGenerator(
                                    private val specLimits: SpecLimits,
                                    private val smtVarGen : SmtVarGenerator,
                                    private val nuGlobal : GlobalBinding,
                                    private val globalBodyMap : BodyMap
                                  ) {
  private val templGen   = new BuiltinTemplateGenerator( specLimits, smtVarGen )
  private val formSigEnc = new FormalSignatureEncoder( specLimits, smtVarGen )
  private val ctxBuilder = new OperatorContextBuilder

  def getObservedFields: Map[SmtIntVariable, Set[String]] = templGen.getObservedFields

  /**
    * Generates the template for a user-defined operator, given its declaration.
    */
  def makeTemplate( decl: TlaOperDecl ) : Template =
    makeTemplateInternal( decl )( nuGlobal, globalBodyMap, List.empty )

  /**
    * Returns the context build during nabla computations
    */
  def getCtx : OperatorContext = ctxBuilder.get

  /**
    * Given a name or tuple of names, generates a NameContext, assigning a fresh SMT variable
    * to each TLA variable (name) provided.
    */
  private def fromBound( ex : TlaEx ) : Binding = ex match {
    case NameEx( v ) => Map( v -> smtVarGen.getFresh )
    case OperEx( TlaFunOper.tuple, names@_* ) =>
      ( names map {
        case NameEx( v ) => v -> smtVarGen.getFresh
        case _ => throw new IllegalArgumentException( "Set filter tuple arguments should only contain names" )
      } ).toMap
    case _ => throw new IllegalArgumentException( "fromBound may only be called on names or tuples of names." )
  }

  /**
    * Given an operator expression, which potentially introduces bound variables,
    * generates a NameContext, which assigns a fresh SMT constant to each bound variable
    */
  private def mkBoundVarBindingExtension( ex : OperEx ) : Binding = ex match {
    case OperEx( TlaSetOper.filter | TlaOper.chooseBounded |
                 TlaBoolOper.exists | TlaBoolOper.forall |
                 TlaTempOper.EE | TlaTempOper.AA,
                 bound, _* ) => fromBound( bound )
    case OperEx( TlaSetOper.map | TlaFunOper.funDef, _, boundPairs@_* ) =>
      val processedBound = boundPairs.zipWithIndex collect {
        case (bound, i) if i % 2 == 0 => fromBound( bound )
      }
      processedBound.foldLeft( Map.empty[String, SmtDatatype] ) { _ ++ _ }
    case OperEx( TlaOper.chooseUnbounded, bound, _ ) => fromBound( bound )
    case OperEx( TlaFunOper.recFunDef, _, bound, _ ) => fromBound( bound )
    case _ => Map.empty
  }

  /**
    * Internal method of makeTemplate.
    *
    * see isTypeInternal.
    */
  private def makeTemplateInternal(
                                    decl: TlaOperDecl
                                  )(
                                    initialBinding : Binding,
                                    bodyMap : BodyMap,
                                    operStack : OperatorApplicationStack
                                  ) : Template = {
    case e +: ts =>
      val k = decl.formalParams.length
      // We enforce arity dynamically. A template belonging to an arity n operator accepts
      // exactly n+1 arguments (or, more accurately, a Seq of length n+1)
      assert( ts.length == k )
      // We match each formal parameter name with its corresponding argument, based on position
      val nuParams : Binding = ( decl.formalParams.zip( ts ) map {
        case (pi, ti) => pi.name -> ti
      } ).toMap

      val nu = if ( decl.isRecursive ) {
        // Instead of making M variables and k equalities, we just make
        // M-k variables and re-use the first k
        val kAlt = specLimits.maxIndex - k
        // Sanity check
        assert( kAlt >= 0 )
        val fs = ts ++: smtVarGen.getNFresh( kAlt )

        val size = SmtKnownInt( k )

        // We add the operator name to the binding
        nuParams + ( decl.name -> oper( tup( size, fs ), e ) )
      }
      else nuParams

      // By assumption, the domains of nuParams and nu are disjoint
      // The template is then given by a single isType(Internal) call.
      And( isTypeInternal( e, decl.body, initialBinding ++ nu )( bodyMap, operStack ) : _* )
    case Nil =>
      throw new IllegalArgumentException( "Templates must accept at least 1 argument." )
  }

  def isType( x: SmtDatatype, phi: TlaEx, nu : Binding ) : Seq[BoolFormula] =
    isTypeInternal( x, phi, nu )( globalBodyMap, List.empty )

  def isTypeInternal(
                      x : SmtDatatype,
                      phi : TlaEx,
                      nu : Binding
                    )(
                      bodyMap : BodyMap,
                      operStack : OperatorApplicationStack
                    ) : Seq[BoolFormula] = {
    // Every time mkConstraintsInternal( a, b, _ )( _, c ) is invoked,we record the assignment of the
    // smt value a to the UID of b, in the stack c
    ctxBuilder.record( operStack, phi.ID, x )

    def processName( n : String, id : UID, smtVar : SmtDatatype = x ) : Seq[BoolFormula] = {
      // If m contains n (n is not a user-defined operator name) then we can just read
      // the appropriate value from m and generate a single Eql constraint
      nu.get( n ) map { v => Seq( Eql( smtVar, v ) ) } getOrElse {
        // Otherwise, n must be a  user-defined operator and we have to perform a virtual call
        if ( !bodyMap.contains( n ) )
          throw new IllegalArgumentException( s"The body of operator $n is unknown" )
        val decl = bodyMap( n )
        val ts = smtVarGen.getNFresh( decl.formalParams.size )
        val f = smtVarGen.getFresh

        val sig = formSigEnc.sig( decl.formalParams )

        val sigConstraints = sig( smtVar +: f +: ts )
        // Next, we compute n's template, adding the ID of ex (the virtual call-site) to the operator stack
        val opTemplate = makeTemplateInternal( decl )( nu, bodyMap, id +: operStack )
        // We know that x must have the formal opType, in addition to the constraints obtained by the template
        // and side-constraints form the signature computation
        opTemplate( f +: ts ) +: sigConstraints
      }
    }

    phi match {
      case ValEx( _ : TlaInt ) => Seq( Eql( x, int ) )
      case ValEx( _ : TlaStr ) => Seq( Eql( x, str ) )
      case ValEx( _ : TlaBool ) => Seq( Eql( x, bool ) )
      case ValEx( TlaBoolSet ) => Seq( Eql( x, set( bool ) ) )
      case ValEx( TlaIntSet ) => Seq( Eql( x, set( int ) ) )
      case ValEx( TlaNatSet ) => Seq( Eql( x, set( int ) ) )
      case ValEx( TlaStrSet ) => Seq( Eql( x, set( str ) ) )
      case ex@NameEx( n ) =>
        processName( n, ex.ID )
      case ex@OperEx( TlaActionOper.prime, NameEx( n ) ) =>
        processName( s"$n'", ex.ID )

      /** UNCHANGED expressions are a special case, because we need to introduce the prime variable */
      case ex@OperEx( TlaActionOper.unchanged, nameEx : NameEx ) =>
        val equivalentEx = Builder.primeEq( nameEx.deepCopy(), nameEx )
        isTypeInternal( x, equivalentEx, nu )( bodyMap, operStack )
      case ex@OperEx( TlaActionOper.unchanged, OperEx( TlaFunOper.tuple, tupArgs@_* ) ) =>
        val equivalentEx = Builder.and( tupArgs map Builder.unchanged : _* )
        isTypeInternal( x, equivalentEx, nu )( bodyMap, operStack )
      case ex@OperEx( TlaActionOper.unchanged, OperEx( TlaOper.apply, NameEx( n ) ) ) =>
        bodyMap.get( n ) match {
          case Some( TlaOperDecl( _, _, nameEx : NameEx ) ) =>
            val equivalentEx = Builder.primeEq( nameEx.deepCopy(), nameEx )
            isTypeInternal( x, equivalentEx, nu )( bodyMap, operStack )
          case Some( TlaOperDecl( _, _, OperEx( TlaFunOper.tuple, tupArgs@_* ) ) ) =>
            val equivalentEx = Builder.and( tupArgs map Builder.unchanged : _* )
            isTypeInternal( x, equivalentEx, nu )( bodyMap, operStack )
          case _ =>
            throw new IllegalArgumentException( "UNCHANGED supports only single-name or name-tuple arguments." )
        }

      /** Annotations use constructors (e.g. Seq(_) in unintended ways so they should be ignored completely */
      case OperEx( BmcOper.withType, ex, annot ) =>
        isTypeInternal( x, ex, nu )( bodyMap, operStack )

      case ex@OperEx( oper, args@_* ) =>
        // If we're dealing with a built-in operator, we simply compute its template and apply it
        val opTemplate = templGen.makeTemplate( ex )

        // Quantifier introduce variables, so we have to extend m when computing sub-nablas
        val boundVarMapExtension = mkBoundVarBindingExtension( ex )

        val fs = smtVarGen.getNFresh( args.length )
        val templApp = opTemplate( x +: fs )
        val subConstraints = fs.zip( args ) flatMap {
          // For the args, we have to recursively compute isType as well
          case (fi, phii) =>
            isTypeInternal( fi, phii, nu ++ boundVarMapExtension )( bodyMap, operStack )
        }
        templApp +: subConstraints
      case LetInEx( body, defs@_* ) =>
        // In the LET-IN case, we add the bound operators to the BodyMap and recurse on the body
        val newBodyMap = BodyMapFactory.makeFromDecls( defs, bodyMap )
        isTypeInternal( x, body, nu )( newBodyMap, operStack )
      case _ => throw new IllegalArgumentException( s"isType undefined for $phi" )
    }
  }

}
