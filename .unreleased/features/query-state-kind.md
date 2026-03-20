Add `STATE` query kind to the JSON-RPC `query` method. When `kinds` includes `"STATE"`, the result contains a `state` field with only the last state of the decoded trace (a single ITF state object), instead of the entire trace. This significantly reduces JSON payload size for long symbolic explorations #3288.

