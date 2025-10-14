# Edge Case Models and Bounty Coverage Mapping

This document lists targeted edge-case model configurations, what they test, and how they map to bounty evaluation criteria (Rigor, Completeness).

## Configs

1. `MC_edge_minimal.cfg` (path: `formal-verification/MC_edge_minimal.cfg`)
   - Purpose: Minimal validator set (2 validators) to test small-network behavior and tie-breaking.
   - Tests: vote uniqueness, certificate formation, type invariants.
   - Run: `java -jar tla2tools.jar -deadlock -config MC_edge_minimal.cfg Alpenglow.tla`

2. `MC_edge_byzantine.cfg` (path: `formal-verification/MC_edge_byzantine.cfg`)
   - Purpose: Exact 20% Byzantine boundary (1 out of 5 validators) to exercise boundary adversary behavior.
   - Tests: ByzantineSafety, EquivocationDetection, CensorshipResistance.
   - Run: `java -jar tla2tools.jar -deadlock -config MC_edge_byzantine.cfg Alpenglow.tla`

3. `MC_edge_quorum.cfg` (path: `formal-verification/MC_edge_quorum.cfg`)
   - Purpose: Quorum stake distribution near 67% threshold to test certificate formation and quorum intersection.
   - Tests: StakeThresholdCorrectness, QuorumIntersection, ValidCertificateStake.
   - Run: `java -jar tla2tools.jar -deadlock -config MC_edge_quorum.cfg Alpenglow.tla`

---

## Bounty Criteria Mapping

- Rigor:
  - Core safety invariants verified in `MC_edge_minimal.cfg` and `MC.cfg`.
  - Byzantine theorems exercised in `MC_edge_byzantine.cfg`.
  - Liveness properties in `MC_Liveness.tla` (use `MC_Liveness.cfg` for temporal checks).

- Completeness:
  - Edge-case coverage: small validator sets, exact 20% adversary, quorum threshold edge.
  - Boundary cases: `MC_edge_quorum.cfg` tests certificate stake threshold boundaries.

---

## Notes

- These configs are intentionally small so they can be run exhaustively by TLC.
- For large-scale or statistical testing, use the provided simulation scripts and sampling budgets in `verify.py`.

