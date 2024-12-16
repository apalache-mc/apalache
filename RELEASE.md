## 0.47.1 - 2024-12-16

### Bug fixes

- Fixed a few problems on parsing Quint and pretty printing TLA, see #3041
- Add extra protection against the SANY race conditions on the filesystem, see #3046
- Fix source tracking in `VCGenerator` to avoid spurious diagnostic messages, see #3010
- Fix a problem when translating Quint nullary operators used polymorphically, see #3044
