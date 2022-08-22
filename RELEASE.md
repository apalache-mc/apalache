## 0.28.1 - 2022-08-22

### Breaking changes

- The structure of the apalache.cfg has changed. All configuration keys that were previously supported have been moved under the `common` key. You can update your config files by prefixing each key from the previous versions with `commong.key-name`. For an example config file, see https://apalache.informal.systems/docs/apalache/config.html#file-format-and-supported-parameters. See #2065.

### Features

- All CLI parameters can now be configured via `apalache.cfg` files. See #2065 and documentation to follow.
