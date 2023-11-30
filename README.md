# understand-vsr
What makes Viewstamped Replication tick?

[Understand Viewstamped Replication with Rust, Automerge, and TLA+](https://medium.com/@polyglot_factotum/understand-viewstamped-replication-with-rust-automerge-and-tla-7a94e9e4d553)

## Replicated state-machine

[Specifying](VSR.tla), and [implementing](src/main.rs), the replication protocol as described in "Viewstamped Replication Revisited"
found at https://dspace.mit.edu/handle/1721.1/71763.

1. Start the bootstap peer:
   - `cargo run --release -- --bootstrap --replica-id "0"`
2. Start two other peers:
   - `cargo run --release --  --replica-id "1"`
   - `cargo run --release --  --replica-id "2"`
3. Watch the peers replicate a state machine supporting "read" and "increment" operations on a number.

To simulate a crash, stop a replica and re-start it with the `--recover` flag. 
