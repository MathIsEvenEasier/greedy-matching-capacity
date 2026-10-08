Arnosti's RANDOM-VERTEX versus RANKING conjecture
=================================================

For independent uniform job neighborhoods of prescribed sizes and equal
positive integer bin capacities, RANDOM-VERTEX has a stochastically larger
matching size than RANKING:

  Pr(M_RANDOM_VERTEX >= K) >= Pr(M_RANKING >= K), for every natural K.

This resolves the full conjecture following Theorem 2 in Nick Arnosti's
*Greedy Matching in Bipartite Random Graphs*, under that paper's
random-neighborhood model. The conjecture assumes a common capacity. The result holds for all finite sizes,
for fixed neighborhood-independent job and priority orders, and hence
also for the source model's independent uniform orders.

Interactive proof: https://mathiseveneasier.github.io/greedy-matching-capacity/

Source paper: https://doi.org/10.1287/stsy.2021.0082

What the comparison means
-------------------------

RANDOM-VERTEX uses a fresh uniform choice among available feasible bins.
RANKING draws one common priority order and always uses the first available
feasible bin. The inequality compares matching-size distributions over
random graphs and algorithm choices. It is not a claim that one algorithm
wins on each individual run, on every fixed graph, or with unequal capacities.

The proof
---------

* A two-bin coefficient identity gives monotonicity and convexity.
* Convexity and capped association compare conditional load concentration.
* Monotonicity and that concentration comparison bound the probability
  that the next choice creates a full bin.
* A refined-history bijection identifies actual matching histories with
  product choice laws conditioned on the residual cap.
* A coupling indexed by accepted-job counts orders the next hitting times
  and full-bin increments. Total probability preserves the actual state
  marginals, without a Markov premise.
* Reaching acceptance level K is equivalent to matching at least K jobs.
  Relabeling and averaging transfer the comparison to the source model.

The manuscript uses Cohen--Sackrowitz (1987), Lemma 4.1, for a concise
association argument. Lean proves the needed finite rational specialization
by direct induction on the common cap; the source theorem is not an axiom.

Read and check
--------------

* research-note.tex: concise manuscript and both bibliographic references.
* docs/: interactive illustrations and a clickable dependency map of the
  six supporting results, coupling argument, and main conclusion. Select
  a result to see its statement, direct prerequisites, and their roles.
* formal/SourceModel.lean: final explicit probability laws and theorem.
* formal/verification-source-azure.json: build, axiom audit and source hashes.
* review/README.rst: model correspondence and questions for external review.
* evidence/: returned compiler records, compiled artifacts and cleanup record.
* REPRODUCE.rst: scope and commands for checking or rebuilding the proof.
* archive/: the earlier research narrative, preserved for provenance.

Lightweight verification, with no Lean compilation::

    python3 verify_packet.py
    node --test scripts/math.test.mjs

The browser's tiny finite examples are illustrations. They do not replace
the general mathematical proof or the Lean certificate.

Verification status
-------------------

Lean 4.34.0, Mathlib 5ed2965256430c3649e86755f9576b54eca72435.
The recorded Azure run compiled 91 positive modules containing 714 named
theorems and audited 929 named declarations. Dependencies are restricted
to propext, Classical.choice and Quot.sound. The positive proof contains
no sorry, custom axioms, unsafe, native_decide or ofReduceBool. Deliberately
false Negative*.lean modules are excluded from the positive build.
The final negative control was rejected with an unsolved False goal.

The source-model theorem has no extra comparison, association, coupling
or Markov premise. The certificate uses the standard Lean kernel; no
independent kernel reimplementation audit is claimed. VibeMathed lists the
result as Candidate, Lean-checked. A full independent proof and formal
statement audit remains open. No priority claim is made.

Authorship and resources
------------------------

Prepared by MathIsEvenEasier with OpenAI Codex (GPT-6 Astra).
Heavy compilation and proof audits were performed in bounded Azure jobs;
the resource deletion receipt is included.

Public source build
-------------------

A public GitHub Actions build on 6 October 2026 rebuilt all
91 positive modules from commit c521b8d45bfa8a38b60a8e55b5ab104634d48b49
and rejected 1 deliberately invalid control. The final theorem's
printed axioms are propext, Classical.choice and Quot.sound.

https://github.com/MathIsEvenEasier/greedy-matching-capacity/actions/runs/37468519145

Permanent copies of the compiler records, exact source hashes, final axiom
output and confirmed Azure cleanup are in evidence/public-ci-2026-10-06/.
The proof-source hashes still match this checkout. See PUBLIC-CI.rst for
the resource limits, trust boundary and reproduction procedure.
