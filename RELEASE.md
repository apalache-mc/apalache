## 0.56.0 - 2026-03-20

### Features

- Upgrade Jetty from 11 to 12.1.7 (EE10) and align Jakarta Servlet API to 6.0
- Add gzip and Zstandard (zstd) compression support to the JSON-RPC server. Upgrade Jetty from 12.0.21 to 12.1.7 and use the new CompressionHandler for transparent HTTP content negotiation via Accept-Encoding / Content-Encoding (#3290).
- Add `STATE` query kind to the JSON-RPC `query` method. When `kinds` includes `"STATE"`, the result contains a `state` field with only the last state of the decoded trace (a single ITF state object), instead of the entire trace. This significantly reduces JSON payload size for long symbolic explorations #3288.
