## 0.30.5 - 2023-03-10

### Breaking changes

- Updated support for quint input, for compatibility with the (forthcoming) Quint v0.8.0. Output from earlier versions of quint will no longer be supported. See #2473 and https://github.com/informalsystems/quint/pull/689.

### Features

- Add support for quint tuples. See #2441.
- Add support for converting (most) quint list operator. See #2440.
- Added support for quint's variadic bindings in `forall` and `exists` operators. See #2471.
