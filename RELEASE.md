## 0.62.1 - 2026-08-19

### Features

- Allow the JSON-RPC `loadSpec` method to load Quint JSON IR and Apalache JSON IR in addition to TLA+, see #3457.

### Bug fixes

- Recognize namespace-qualified Quint label bindings, such as `main::replica::__label_proposer`, by reading the label from the final name segment.
