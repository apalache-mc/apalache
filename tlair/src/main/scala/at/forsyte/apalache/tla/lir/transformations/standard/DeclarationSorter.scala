package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations.TlaModuleTransformation
import at.forsyte.apalache.tla.lir.transformations.impl.StableTopologicalSort
import com.typesafe.scalalogging.LazyLogging

import java.io.{FileWriter, PrintWriter}
import scala.collection.immutable.HashMap

/**
 * <p>This module transformation implements a stable topological sort of declarations in a module.
 * Substitutions may result in the wrong order of operators, that is, violating the define-before-use principle.
 * This class orders the declarations in a module according to the define-before-use principle, if possible.
 * Importantly, the sort is stable: The relative order of the definitions is changed only if required.</p>
 *
 * <p>This implementation make the topological sort in ConstAndDefRewriter (by Andrey Kupriyanov) obsolete.
 * Note that this transformation does not require a transformation tracker as a parameter, as it only
 * changes the relative order of the operators, not their contents.</p>
 *
 * @author Igor Konnov
 */
class DeclarationSorter extends TlaModuleTransformation with LazyLogging {
  type Edges = Map[UID, Set[UID]]
  type MapIdToDecl = Map[UID, TlaDecl]

  override def apply(input: TlaModule): TlaModule = {
    // save the original order of the declarations
    val idToDecl: MapIdToDecl = input.declarations.foldLeft(Map.empty[UID, TlaDecl]) { case (map, d) =>
      map + (d.ID -> d)
    }

    // sort the ids topologically
    val declarations = input.declarations
    val depsGraph = computeDependenciesGraph(declarations)
    val result = new StableTopologicalSort[UID].sort(depsGraph, declarations.map(_.ID))
    // map the ids back to declarations
    val sortedDeclarations = result match {
      case Left(sorted) =>
        sorted.map(idToDecl)

      case Right(witnesses) =>
        val filename = explainCyclicDependency(idToDecl, depsGraph, witnesses)
        logger.error(s"Check the dependency graph in $filename. You can view it with graphviz.")
        val opers = witnesses.map(idToDecl).map(_.name).mkString(", ")
        throw new CyclicDependencyError("Found a cyclic dependency among operators: " + opers)
    }

    new TlaModule(input.name, sortedDeclarations)
  }

  // Dump the dependency graph to a dot file. Otherwise, it is very hard to see what is going on.
  private def explainCyclicDependency(idToDecl: MapIdToDecl, depsGraph: Edges, witnesses: Set[UID]): String = {
    val filename = "dependencies.dot"

    def getName(uid: UID): String = {
      idToDecl.get(uid).map(_.name).getOrElse("undefined")
    }

    def printToDot(writer: PrintWriter): Unit = {
      writer.println("digraph dependencies {")

      for (fromId <- witnesses) {
        writer.println("""  n%s[label="%s"];""".format(fromId, getName(fromId)))
        for (toId <- depsGraph.getOrElse(fromId, Set.empty)) {
          writer.println("""  n%s -> n%s;""".format(fromId, toId))
        }
      }
      writer.println("}")
    }

    val writer = new PrintWriter(new FileWriter(filename, false))
    try {
      printToDot(writer)
      filename
    } finally {
      writer.close()
    }
  }

  // For every declaration ID id1, compute the list of distinct ID of the declarations that must be defined before id1
  private def computeDependenciesGraph(declarations: Seq[TlaDecl]): Edges = {
    // create a map from declaration names to their IDs
    val nameToId = declarations.foldLeft(new HashMap[String, UID]) { (map, d) =>
      map + (d.name -> d.ID)
    }

    def updateDependencies(map: Edges, defId: UID, uses: Set[UID]): Edges = {
      map + (defId -> (map(defId) ++ uses))
    }

    val findUses = findExprUses(nameToId)
    // create a map that contains the list of used-by IDs for every declaration, excluding the declaration itself
    val initMap = Map(declarations.map { d => d.ID -> Set.empty[UID] }: _*)
    declarations.foldLeft(initMap) {
      case (map, d @ TlaConstDecl(_)) =>
        map + (d.ID -> Set.empty[UID])

      case (map, d @ TlaVarDecl(_)) =>
        map + (d.ID -> Set.empty[UID])

      case (map, d @ TlaAssumeDecl(body)) =>
        val uses = (findUses(body) - d.ID)
        updateDependencies(map, d.ID, uses)

      case (map, d @ TlaOperDecl(_, _, body)) =>
        val uses = (findUses(body) - d.ID)
        updateDependencies(map, d.ID, uses)

      case (map, _) => map
    }
  }

  // compute the identifiers of the names used by an expression
  private def findExprUses(nameToId: Map[String, UID]): TlaEx => Set[UID] = {
    def usesRec: TlaEx => Set[UID] = {
      case NameEx(name) =>
        // This may be a use of a VARIABLE or a CONSTANT.
        // A singleton with the id, if the name is registered; otherwise, empty set.
        nameToId.get(name).fold(Set.empty[UID])(Set(_))

      case OperEx(TlaOper.apply, NameEx(name), args @ _*) =>
        // This may be an application of a user-defined operator.
        // A singleton with the id, if the name is registered
        //   (that is, for a top-level definition); otherwise, return the empty set (that is, for a LET-IN).
        val base = nameToId.get(name).map(Set(_)).getOrElse(Set.empty)
        args.foldLeft(base) { (u, arg) =>
          u ++ usesRec(arg)
        }

      case OperEx(_, args @ _*) =>
        // join the uses of the arguments
        args.foldLeft(Set.empty[UID]) { (u, arg) =>
          u ++ usesRec(arg)
        }

      case LetInEx(body, decls @ _*) =>
        // Join the uses of the body and the declarations.
        // We do not track dependencies between the LET-IN operators, because they are scoped and ordered.
        decls.foldLeft(usesRec(body)) { (u, d) =>
          u ++ usesRec(d.body)
        }

      case _ =>
        Set.empty[UID]
    }

    usesRec
  }
}

object DeclarationSorter {
  private val _instance: DeclarationSorter = new DeclarationSorter

  def instance: DeclarationSorter = {
    _instance
  }
}
