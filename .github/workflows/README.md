# Apalache's GitHub CI Workflows

## [./main.yml](./main.yml)

- Triggered on pull requests into `unstable`.
- Our primary build and test workflow.

## [./deploy.yml](./deploy.yml)

- Triggered by pull requests into `unstable`.
- Used for any artifacts that we deploy into production environments. Currently,
  this only consists of our website at https://apalache.informal.systems.

## [./prepare-release.yml](./prepare-release.yml)

- Triggered manually, or by a cron-job every Monday.
- The workflow prepares a release and opens a `[release]` PR.

## [./release.yml](./release.yml)

- Triggered by merging the `[release]` PR.
- The workflow builds the release artifact(s), tags the release commit created
  in the `prepare-release` workflow, and publishes the release to GitHub's
  release artifact store.
