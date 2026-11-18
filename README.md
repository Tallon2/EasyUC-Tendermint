# Tendermint same-round agreement

`WeightedQuorum.ec` proves the weighted quorum bound, honest overlap and certificate uniqueness. Its weights and duplicate-free finite validator universe are parameters.

`SingleRound.ec` defines the single-height, single-round transition function and proves its invariants over arbitrary finite event sequences. A node's inbox consists of delivery events addressed to it. A publication records the source and value at emission. Delivery must refer to an existing publication and may repeat or be reordered. The Byzantine set is fixed on startup and Byzantine voters may equivocate with their own identity. Honest precommits require local prevote evidence and are emitted at most once. A decision requires a local precommit certificate and adds a decision event to the history. All weighted tallies use sets of distinct sources.

`TendermintRound.uc` calls the same transition function. It outputs `decide(node,block)` exactly when the transition accepts a decision event. The interpreter requires a unit, so the file includes a mirror of the transition machine with a relay. The checked agreement theorem concerns the shared transition function and its emitted decisions. Each instance models a single height and round with block ballots. Cross-round locks, timers, liveness and real/ideal indistinguishability are outside this artifact's proof scope.

`demo.uci` checks the actual interpreter messages for a four-node weighted configuration. Theorems in the `.ec` files use arbitrary finite configurations satisfying the stated premises.

## Run

Use a built EasyCrypt and EasyUC `ucdsl`. With the bundled source layout, `verify.sh` uses `../EasyUC/uc-dsl/bin/ucdsl` if built and otherwise looks for `ucdsl` on `PATH`. The source revisions used for the recorded run are EasyUC `97be5322` and EasyCrypt `761aaf25`. EasyUC's `uc-dsl/README.md` describes how to build the interpreter. On a machine with existing tools, set `EASYCRYPT` and `UCDSL` to their executable paths as needed.

From the paper directory:

```bash
set -o pipefail
./code/tendermint/verify.sh 2>&1 | tee '运行结果/verification.log'
```

The tactic scripts and interpreter demo run without invoking an SMT server.
