# WSC proof support

This branch packages the Lean-blaster source used by wsc-blaster, based on
`3db3e1cca4e286b91e284745269e2b4a563b402b`. It provides `blaster (induction: auto)`,
proof summaries, and the `blaster_library` attribute needed by the optional
PlutusCore and CardanoLedgerApi fact packages. It also includes the fix for
registering function-valued pattern variables during deferred match translation.

This is a supporting dependency branch, not a proposal to merge the complete
solver fork. The fact packages pin its commit for reproducible builds.

Validation in the source workspace: all 14 local regression files and six
exported proofs pass. Upstream Issue26 passes. Comparing the full pinned
upstream suite leaves six existing result/optimizer-shape expectation failures
and introduces no new diagnostics. Blaster's SMT conclusions still use the
`Blaster.Tactic.blasterProven` axiom; structural induction is kernel checked.
