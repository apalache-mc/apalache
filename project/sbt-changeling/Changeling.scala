package systems.informal.sbt.changeling

/**
 * =Changeling=
 *
 * Changeling is an SBT pluging to make allow simple maintenance of a merge-conflict free changelog.
 *
 * ==Motivation==
 *
 * Merge conflicts arise when the same lines in the same files are edited
 *
 * "simultaneously" in two different branches. The basic idea is to reduce the chance of merge conflicts by adding each
 * entry of an unreleased change into the changelog via a separate file.
 *
 * ===Design===
 *
 * In order to produce a changelog that has the usual and expected format in a flatfile, we just need a representation
 * in the file system that will let us construct the expected result. If we look at a changelog, we can see an evident
 * document model. Our changelog has roughly the following general shape:
 *
 * {{{
 * # Changelog
 *
 * ## Unrelased
 *
 * ### Features
 *
 * - Change entry 1
 * - Change entry 2
 *
 * ### Bug fixes
 *
 * - Change entry 3
 * - Change entry 4
 *
 * ## 0.0.1
 *
 * ### Features
 *
 * - Change entry 1
 * - Change entry 2
 *
 * ### Bug fixes
 *
 * - Change entry 3
 * - Change entry 4
 * }}}
 *
 * The obvious, high-level document model is a tree of depth 4:
 *
 * {{{
 * Changelog
 * |------- Unreleased
 * |          |--------- Features
 * |          |            |------ Change entry 1
 * |          |            \------ Change entry 2
 * |          |
 * |          \--------- Bug fixes
 * |                       |------ Change entry 3
 * |                       \------ Change entry 4
 * |
 * \------- 0.0.1
 * |--------- Features
 * |            |------ Change entry 1
 * |            \------ Change entry 2
 * |
 * \--------- Bug fixes
 * |------ Change entry 3
 * \------ Change entry 4
 * }}}
 *
 * We can represent the document model with an analogous directory structure. However, we don't actually need to
 * represent the entire document in the file system. Critically, merge conflicts only arise over updates to the
 * `Unreleased` changes, which means we can solve the merge conflict problem by focusing just on the `Unreleased` branch
 * of the tree. We'll therefore represent the conflict liable fragment of the changelog with the following directory
 * tree:
 *
 * {{{
 * .unreleased/
 * ├── bug-fixes
 * │   ├── change-entry-1.md
 * │   └── change-entry-2.md
 * └── features
 *     ├── change-entry-3.md
 *     └── change-entry-4.md
 * }}}
 *
 * The purpose of this plugin is to maintain that directory and extract the usual markdown flatfile from it when needed
 * for releases.
 */

import sbt._
import Keys._

object ChangelingPlugin extends AutoPlugin {

  // The keys in this object are imported into a project when the plugin is enabled
  object autoImport {
    lazy val changelingKinds = settingKey[Seq[String]](
        """|Configures the supported kinds of changes, and and order in which
           |these should be reported in the rendered changelog. Each kind is a
           |possible subheading in the notes for a release.""".stripMargin
    )

    lazy val changelingDirectory = taskKey[File](
        """|Ensures an .unreleased directory exists at the root of our repo,
           |with a subdirectory for each supported kind of change""".stripMargin
    )

    lazy val changelingUnreleasedDir = settingKey[File](
        "The directory in which unreleased changes are recorded"
    )

    lazy val changelingRelaseNotes = taskKey[File](
        """|Render the contents of the `changelingUnreleasedDir` directory as a
           |markdown file, following expected format for release
           |notes""".stripMargin
    )
  }

  // Bring the keys into scope
  import autoImport._

  // Keys set in this fucntion will be the default configuration for all projects
  override lazy val globalSettings: Seq[Setting[_]] = Seq(
      changelingUnreleasedDir := (ThisBuild / baseDirectory).value / ".unreleased",
      changelingKinds := Seq(
          "Breaking changes",
          "Features",
          "Bug fixes",
          "Documentation",
      ),
  )

  // The keys set in this function will be configured for any project that enables the plugin
  override lazy val projectSettings: Seq[Setting[_]] = Seq(
      changelingDirectory := Changeling.ensureDirStructureExists(
          base = changelingUnreleasedDir.value,
          children = changelingKinds.value,
      ),
      changelingRelaseNotes := Changeling.renderReleaseNotes(
          (ThisBuild / version).value,
          changelingDirectory.value,
          (Compile / resourceManaged).value / "RELEASE.md",
      ),
  )

}

object Changeling {

  /**
   * Ensure that `base` directory exists, and that it has all `children`
   *
   * Does not overwrite any files that already exist.
   */
  def ensureDirStructureExists(base: File, children: Seq[String]): File = {
    val childOfBase: String => File = base / _
    val leafDirs = children.map(normalizeFileName.andThen(childOfBase))
    IO.createDirectories(leafDirs)
    base
  }

  /**
   * Render the directory unreleased directory structure as a markdown file
   */
  def renderReleaseNotes(version: String, unreleasedDir: File, releaseNotes: File): File = {
    // The heading for the release notes
    val versionHeading = s"## ${version} - ${java.time.LocalDate.now}"
    // To render the directory structure described above into the required flatfile
    // we just have to flatten the directory tree with the following transformations
    //
    // - transforming the change directory name into an H3 heading
    // - get the contnet of each file in the change directory, and make it a
    //   bullet list item
    val changeSections = IO
      .listFiles(unreleasedDir)
      .flatMap { changeDir =>
        val heading = s"### ${deNormalizeFileName(changeDir.base.toString)}"
        val changes = IO.listFiles(changeDir).map(readFile.andThen(mdBulletItem))
        (heading +: "" +: changes)
      }
    val notes = (versionHeading +: "" +: changeSections).mkString("\n")
    IO.write(releaseNotes, notes)
    releaseNotes
  }

  private def mdBulletItem(s: String): String = {
    val lineBreaks = "(\\r\\n?|\\n)"
    val linesBreaksRemoved = s.replaceAll(lineBreaks, " ")
    s"- ${linesBreaksRemoved}"
  }

  // Heading -> Filename
  private val normalizeFileName: String => String = _.replace(' ', '-').toLowerCase()
  // Filename -> Heading
  private val deNormalizeFileName: String => String = _.replace('-', ' ').capitalize
  private val readFile: File => String = IO.read(_)
}
