# Trade-Offs

## Why do we only allow linear effects inside parameter disposers, replicators, and other simple operations?

TL;DR: Because it makes type checking and reasoning about the program easier.

1. If non-linear effects were allowed inside parameter disposers, then exceptional value from simple operation must
   subsume U0 because
   1. Disposers are invoked after the value is created. Hence disposers may cause exception again, which could cause the
      value to be ignored (when the nested exception matches a higher up handler)
   2. If a disposer performs a simple exceptional operation, and this operation returns an exceptional value matching a
      nearby handler, then this value will be ignored because the matching handler's transform loader is already
      replaced by a disposer (and hence normal execution cannot be restored). 

2. If non-linear effects were allowed inside parameter replicators, then
   1. Running the replicator could trigger an exception, which interrupts the replication process and causes the handler
      parameter to be ignored (note that one can wrapping another handler to properly dispose this parameter itself).
      But, all downstream handler disposers must be invoked, which may depend on the current handler parameter, which
      has been consumed by the (interrupted) replication process. This may be sovled by requiring usage of handler
      parameter to subsume URel. But that would require tracking more type information of the handler replicator.

3. If non-linear effects were allowed inside other simple operations, then
   1. If the handler implements some simple exceptional operation, then this operation may throw an exception, which
      would trigger disposers of all handlers above the current handler, which, in turn, may call operations on this
      handler again. This means the usage handler parameter must subsume URel because the current operation is consuming
      the parameter already, and another call to an operation of this handler would consume it again. This issue can be
      solved by requiring usage of the handler parameter to subsume URel if the handler implements any simple
      exceptional operation.

On the flip side, disallowing non-linear effects inside parameter disposers, replicators, and other simple operations
doesn't seem to cause much inconvenience. If one wants to perform non-linear effects in a simple operation, they can
just use a complex operation instead, in which case the type system will enforce resource checking through the linearity
of the continuation object. For disposers and replicators the needs to perform exceptional effects seem rare. Common use
cases like file or network IO can always be done via linear effects, where error code is returned as a variant of the
result value.