package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.io.annotations.{Annotation, AnnotationStr, StandardAnnotations}
import at.forsyte.apalache.io.typecheck.parser.{DefaultType1Parser, Type1ParseError}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecheck.etc._
import at.forsyte.apalache.tla.typecheck.integration.{RecordingTypeCheckerListener, TypeRewriter}
import at.forsyte.apalache.tla.types.TypeVarPool
import com.typesafe.scalalogging.LazyLogging

/**
 * The API to the type checker. It first translates a TLA+ module into EtcExpr and then does the type checking.
 *
 * @author
 *   Igor Konnov
 */
class TypeCheckerTool(annotationStore: AnnotationStore, inferPoly: Boolean, useRows: Boolean) extends LazyLogging {
  private val type1Parser = DefaultType1Parser

  /**
   * Check the types in a module. All type checking events are sent to a listener.
   *
   * @param listener
   *   a listener of type checking events
   * @param module
   *   a module to type check
   * @return
   *   the flag that indicates whether the module is well-typed
   */
  def check(listener: TypeCheckerListener, module: TlaModule): Boolean = {
    val maxTypeVar = findMaxUsedTypeVar(module)
    val varPool = new TypeVarPool(maxTypeVar + 1)
    val aliasSubstitution = parseAllTypeAliases(module.declarations)
    val typeAnnotations = parseTypeAnnotations(module.declarations)
    val toEtc = new ToEtcExpr(typeAnnotations, aliasSubstitution, varPool, useRows)

    // Bool is the final expression in the chain of let-definitions
    val terminalExpr: EtcExpr = EtcConst(BoolT1)(BlameRef(UID.unique))

    // translate the whole TLA+ module into a long EtcExpr. Is not that cool?
    val topExpr =
      module.declarations.foldRight(terminalExpr) { case (decl, inScopeEx) =>
        toEtc(decl, inScopeEx)
      }

    // a hack: we wrap topExpr with LET-IN, so the type of topExpr is not overwritten
    def uniqueRef() = BlameRef(UID.unique)

    // generate a unique name for the root definition, to avoid clashes
    val rootName = "MODULE_%s_%d_APALACHE".format(module.name, System.currentTimeMillis())
    val rootExpr = EtcLet(rootName, EtcAbs(EtcConst(BoolT1)(uniqueRef()))(uniqueRef()), topExpr)(uniqueRef())

    val typeChecker = new EtcTypeChecker(varPool, inferPolytypes = inferPoly)
    // run the type checker
    val result = typeChecker.compute(listener, TypeContext.empty, rootExpr)
    result.isDefined
  }

  /**
   * Check the types in a module and, if the module is well-typed, produce a new module that attaches a type tag to
   * every expression and declaration in the module.
   *
   * Only used in tests.
   *
   * @param tracker
   *   a transformation tracker that is applied when expressions and declarations are tagged
   * @param listener
   *   a listener to type checking events
   * @param defaultTag
   *   a function that returns a default type for UID, when type is missing
   * @param module
   *   a module to type check
   * @return
   *   Some(newModule) if module is well-typed; None, otherwise
   */
  def checkAndTag(
      tracker: lir.transformations.TransformationTracker,
      listener: TypeCheckerListener,
      defaultTag: UID => TypeTag,
      module: TlaModule): Option[TlaModule] = {
    // The source stores and ChangeListeners for this aren't needed, since it's only run in tests
    val recorder = new RecordingTypeCheckerListener(new SourceStore(), new lir.storage.ChangeListener())
    if (!check(new MultiTypeCheckerListener(listener, recorder), module)) {
      None
    } else {
      val transformer = new TypeRewriter(tracker, defaultTag)(recorder.toMap)
      val taggedDecls = module.declarations.map(transformer(_))
      Some(TlaModule(module.name, taggedDecls))
    }
  }

  // Parse type aliases from the annotations.
  private def parseAllTypeAliases(declarations: Seq[TlaDecl]): TypeAliasSubstitution = {
    var aliases = Map[String, lir.TlaType1]()

    // extract all aliases from the annotations
    for (decl <- declarations) {
      annotationStore.get(decl.ID).foreach { annotations =>
        annotations.filter(_.name == StandardAnnotations.TYPE_ALIAS).foreach { annot =>
          annot.args match {
            case Seq(AnnotationStr(text)) =>
              val (alias, assignedType) = parseOneTypeAlias(decl.name, decl.ID, text)
              if (!ConstT1.isAliasReference(alias)) {
                val msg =
                  s"Operator ${decl.name}: Deprecated syntax in type alias $alias. Use camelCase of Type System 1.2."
                logger.warn(msg)
              }
              aliases += alias -> assignedType

            case args =>
              throw new TypingInputException(
                  s"Unexpected annotation alias in front of ${decl.name}: " + args.mkString(", "), decl.ID)
          }
        }
      }
    }

    // Aliases can refer to one another. Substitute the aliases until we arrive at a fixpoint.
    TypeAliasSubstitution(aliases).closure()
  }

  // parse type from its text representation
  private def parseOneTypeAlias(where: String, causeUid: UID, text: String): (String, TlaType1) = {
    try {
      val (alias, tt) = DefaultType1Parser.parseAlias(text)
      ensureTypeSystem12(causeUid, tt)
      (alias, tt)
    } catch {
      case e: Type1ParseError =>
        logger.error("Parsing error in the alias annotation: " + text)
        throw new TypingInputException(s"Parser error in type alias of $where: ${e.msg}", causeUid)
    }
  }

  // Parse type annotations into TlaType1.
  private def parseTypeAnnotations(declarations: Seq[TlaDecl]): Map[UID, TlaType1] = {
    def findDeclarationName(uid: UID): String = {
      declarations.find(_.ID == uid).map(_.name).getOrElse("some declaration")
    }

    annotationStore
      .map { case (uid, annotations) =>
        annotations.filter(_.name == StandardAnnotations.TYPE) match {
          case Nil =>
            None

          case Annotation(StandardAnnotations.TYPE, AnnotationStr(annotationText)) :: Nil =>
            try {
              val typeFromText = type1Parser.parseType(annotationText)
              ensureTypeSystem12(uid, typeFromText)
              Some(uid, typeFromText)
            } catch {
              case e: Type1ParseError =>
                logger.error("Parsing error in the type annotation: " + annotationText)
                val where = findDeclarationName(uid)
                throw new TypingInputException(s"Parser error in type annotation of $where: ${e.msg}", UID.nullId)
            }

          case multiple =>
            val where = findDeclarationName(uid)
            val n = multiple.size
            val msg = s"Found $n @${StandardAnnotations.TYPE} annotations in front of $where"
            throw new TypingInputException(msg, uid)
        }
      }
      .flatten
      .toMap
  }

  // Find the maximum index used in type tags of a module.
  // We need this index to initialize the variable pool,
  // so the fresh type variables do not conflict with the old type variables.
  private def findMaxUsedTypeVar(module: TlaModule): Int = {
    def findInTag: TypeTag => Int = {
      case Typed(tt: TlaType1) =>
        val used = tt.usedNames
        if (used.isEmpty) -1 else used.max

      case _ => -1
    }

    def findInEx: TlaEx => Int = {
      // only LET-IN expressions may introduce fresh type variables, as we have let polymorphism
      case LetInEx(body, defs @ _*) =>
        defs.map(findInDecl).foldLeft(findInEx(body))(Math.max)

      case OperEx(_, args @ _*) =>
        args.map(findInEx).foldLeft(-1)(Math.max)

      case _ =>
        -1
    }

    def findInDecl: TlaDecl => Int = {
      case d @ TlaOperDecl(_, _, body) =>
        Math.max(findInEx(body), findInTag(d.typeTag))

      case d =>
        findInTag(d.typeTag)
    }

    module.declarations.map(findInDecl).foldLeft(-1)(Math.max)
  }

  // Ensure that all type annotations are using Type System 1.2, unless `useRows=false`.
  private def ensureTypeSystem12(exprId: UID, typeInAnnotation: TlaType1): Unit = {
    // recursively check that the use of rows is consistent with useRows
    def containsExpectedRecordTypes: TlaType1 => Boolean = {
      case RecT1(_) =>
        // OK, if rows are disabled
        !useRows

      case RecRowT1(_) =>
        // OK, if rows are enabled
        useRows

      case VariantT1(_) =>
        // OK, if rows are enabled
        useRows

      case RowT1(_, _) =>
        useRows

      case SetT1(elemT) =>
        containsExpectedRecordTypes(elemT)

      case SeqT1(elemT) =>
        containsExpectedRecordTypes(elemT)

      case FunT1(argT, resT) =>
        containsExpectedRecordTypes(argT) && containsExpectedRecordTypes(resT)

      case TupT1(elemTs @ _*) =>
        // tuples are non-empty, hence using reduce should be fine
        elemTs.map(containsExpectedRecordTypes).forall(_ == true)

      case SparseTupT1(fieldTypes) =>
        fieldTypes.values.map(containsExpectedRecordTypes).forall(_ == true)

      case OperT1(argTs, resT) =>
        (argTs :+ resT).map(containsExpectedRecordTypes).forall(_ == true)

      case IntT1 | StrT1 | BoolT1 | RealT1 | ConstT1(_) | VarT1(_) =>
        true
    }

    if (!containsExpectedRecordTypes(typeInAnnotation)) {
      val msg = if (useRows) {
        s"Found imprecise record types, while Type System 1.2 is enabled. Either update the annotations, or use --features=no-rows."
      } else {
        s"Found row types, while Type System 1.2 is disabled. Do not use --features=no-rows."
      }

      throw new TypingInputException(msg, exprId)
    }
  }
}
