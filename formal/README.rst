Lean proof sources
==================

The final theorem is MatchingCapacity.source_matching_tail_comparison
in SourceModel.lean. It compares the matching-size tails of two explicitly
normalized source-model laws for every finite parameter and degree vector
bounded by m. Capacity is q+1.

For proof entry points, see ../review/README.rst. For the precise pinned
build procedure and trust boundary, see ../REPRODUCE.rst. The complete
module order, source hashes, axiom output and negative-control result are
in verification-source-azure.json.

Negative*.lean files are intentionally false control claims. They must
not be included in a successful positive build. Audit.lean audits all
929 named positive declarations. No Lean sources have been changed since
the successful final Azure run, job 7c29484da68044cb.
