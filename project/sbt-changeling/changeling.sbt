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
