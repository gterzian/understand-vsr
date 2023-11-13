# understand-vsr
What makes Viewstamped Replication tick?

## Replicated state-machine

[Specifying](VSR.tla), and [implementing](src/main.rs), the replication protocol as described in "Viewstamped Replication Revisited"
found at https://dspace.mit.edu/handle/1721.1/71763.

1. Start the bootstap peer:
   - `cargo run --release -- --bootstrap --replica-id "1"`
2. Start two other peers:
   - `cargo run --release --  --replica-id "2"`
   - `cargo run --release --  --replica-id "3"`
3. Watch the peers replicate a log of values, using it to implement a replicated state machine supporting "read" and "increment" operations on a number.
