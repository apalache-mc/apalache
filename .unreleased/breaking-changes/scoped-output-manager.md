`OutputManager` state is now scoped to each `Tool.run` invocation; direct callers must use `OutputManager.withScope`,
and asynchronous callers must propagate a captured scope.
