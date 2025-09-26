package com.github.apalachemc.apalache.jsonrpc

import at.forsyte.apalache.tla.bmcmt.ModelCheckerContext
import at.forsyte.apalache.tla.bmcmt.trex.{ExecutionSnapshot, IncrementalExecutionContextSnapshot}

import scala.collection.concurrent.TrieMap
import scala.collection.mutable

/**
 * A manager for snapshots of the model checker context, indexed by session ID. This class is using thread-safe
 * data structures.
 *
 * Each session may have multiple snapshots, as the user may want to roll back to a previous snapshot. Importantly,
 * whenever a snapshot `n` is recovered, all snapshots with IDs greater than `n` are deleted. This approach corresponds
 * to backtracking in search algorithms.
 *
 * @author
 *   Igor Konnov
 */
class CheckerSnapshotsPerSession {
  type Snapshot = ExecutionSnapshot[IncrementalExecutionContextSnapshot]
  type CheckerContext = ModelCheckerContext[IncrementalExecutionContextSnapshot]

  // A map from session IDs to saved snapshots. Each session may have multiple snapshots,
  // as the user may want to roll back to a previous snapshot.
  // The outer map is a TrieMap to allow concurrent reads and updates.
  // The inner map is a mutable HashMap, as we do not expect concurrent accesses to
  // snapshots within a single session.
  private val snapshots: TrieMap[String, mutable.HashMap[Int, Snapshot]] = TrieMap.empty

  /**
   * Take a snapshot of the current context and save it under the given session ID.
   * @param sessionId
   *   the ID of the current session
   * @param checkerContext
   *   the checker context to snapshot
   * @return
   *   the snapshot ID, which monotonically increases within a session (gaps are possible)
   */
  def takeSnapshot(sessionId: String, checkerContext: CheckerContext): Int = {
    val sessionSnapshots = snapshots.getOrElseUpdate(sessionId, mutable.HashMap.empty)
    val snapshot = checkerContext.trex.snapshot()
    val snapshotId = snapshot.contextSnapshot.rewriterLevel
    sessionSnapshots.put(snapshotId, snapshot)
    snapshotId
  }

  /**
   * Recover a previously saved snapshot.
   * @param sessionId
   *   the ID of the current session
   * @param checkerContext
   *   the checker context to recover
   * @param snapshotId
   *   the snapshot ID to recover
   * @return
   *   true, if the snapshot was found and recovered; false, otherwise
   */
  def recoverSnapshot(sessionId: String, checkerContext: CheckerContext, snapshotId: Int): Boolean = {
    val sessionSnapshots = snapshots.getOrElseUpdate(sessionId, mutable.HashMap.empty)
    val snapshot = sessionSnapshots.get(snapshotId)
    if (snapshot.isEmpty) {
      false
    } else {
      // remove all snapshots that beyond snapshotId
      sessionSnapshots.filterInPlace((id, _) => id <= snapshotId)
      // recover the snapshot
      checkerContext.trex.recover(snapshot.get)
      true
    }
  }

  /**
   * Forget all snapshots associated with the given session ID.
   * @param sessionId session ID
   */
  def remove(sessionId: String): Unit = {
    snapshots.remove(sessionId)
  }
}
