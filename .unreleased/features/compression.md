Add gzip and Zstandard (zstd) compression support to the JSON-RPC server.
Upgrade Jetty from 12.0.21 to 12.1.7 and use the new CompressionHandler
for transparent HTTP content negotiation via Accept-Encoding / Content-Encoding.

