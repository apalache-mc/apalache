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
- **Requirements**:
  - A personal API token is required to authenticate the API call that opens the
    PR.
    - We use a token belonging to our machine user [@apalache-bot][]. apalache-bot
      creates the PR from their fork of the repo, and they have no permissions in
      this repo itself.
    - Secrets are configured [here][secret-config].

[@apalache-bot]: https://github.com/apalache-bot
[secret-config]: https://github.com/informalsystems/apalache/settings/secrets/actions

## [./release.yml](./release.yml)

- Triggered by merging the `[release]` PR.
- The workflow builds the release artifact(s), tags the release commit created
  in the `prepare-release` workflow, and publishes the release to GitHub's
  release artifact store.

## [./container.yml](./container.yml)

- Triggered by publishing releases or merging into the `unstable` branch
- The workflow builds the docker container defined in the
  [`/Dockerfile`](../../Dockerfile) and publishes it to GitHub Packages.
