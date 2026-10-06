Review guide
============

The result
----------

For independent uniform job neighborhoods of prescribed sizes and a common
positive integer bin capacity, RANDOM-VERTEX has a stochastically larger
matching size than RANKING. The comparison holds for every fixed job order
and every fixed common bin ranking independent of the neighborhoods. It
therefore holds after averaging over the independent uniform orders in
Arnosti's model.

Read ``../research-note.tex`` for the concise manuscript. It contains the
model, proof and formal statement. The earlier research narrative is
preserved in ``../archive/research-note-2026-10-05.tex``. Source and proof
correspondence, exact Lean declaration locations and file hashes are in
``source-model-review.json``. All paths inside that JSON are relative to
the repository root.

Primary source and exact claim
------------------------------

Nick Arnosti, *Greedy Matching in Bipartite Random Graphs*, Stochastic
Systems 12(2), 133-150 (2022), DOI 10.1287/stsy.2021.0082:

https://pubsonline.informs.org/doi/pdf/10.1287/stsy.2021.0082

The algorithms are on published page 135, Section 1.1. Definition 2 on
page 136 specifies the random graph. The conjecture follows Theorem 2
on that page and concerns equal capacities greater than two. Our theorem
includes all positive integer capacities. It compares probabilities over
the random graph and algorithm choices; it does not assert a comparison
for each fixed graph or for unequal capacities.

The source implements RANDOM-VERTEX through independent uniform preference
permutations for the jobs. The first member of a nonempty available set in
the current job's unused permutation is uniform on that set. Thus fresh
uniform choice gives the same sequential law. The manuscript explains this
equivalence; Lean defines the sequential uniform response directly. It
does not separately model the whole array of job preference permutations.
RANKING uses one common priority permutation throughout the history.

Lean entry points
-----------------

Start with ``../formal/SourceModel.lean``:

* ``sourceRVHistory`` and ``sourceRankingHistory`` define the probability
  laws by explicit graph and permutation averages.
* ``source_rv_probability``, ``source_ranking_probability`` and their
  nonnegativity lemmas establish that these are probability laws.
* ``source_matching_tail_comparison`` is the final theorem. Its only
  input restriction is ``degree(j) <= m``. Capacity is ``q+1``, so every
  positive integer capacity is covered. It allows every finite job and
  bin count and every natural matching-size threshold.

Then follow these proof ingredients:

* ``CappedAssociation.lean`` proves ``cappedAssociation_all`` directly by
  induction on the common cap. The manuscript instead invokes the
  applicable published association result for a shorter exposition.
* ``PairCoefficients.lean``, ``CategoricalDensity.lean`` and
  ``CategoricalConcentration.lean`` turn ordered choice rows into a
  comparison of capped load distributions.
* ``UniformCappedLaw.lean`` identifies the uniform reference law and
  proves ``ordered_vs_uniform_saturation``.
* ``HistoryFiber.lean``, ``HistoryFactorization.lean`` and
  ``StoppingTransitionLaws.lean`` connect that inequality to actual
  matching histories and their conditional transitions.
* ``BoundedNextCoupling.lean``, ``CouplingInduction.lean`` and
  ``FixedPriorityComparison.lean`` give the ordered coupling of state
  marginals and the matching-tail comparison.
* ``PriorityRelabeling.lean`` and ``IndependentNeighborhoods.lean`` identify
  the fixed-priority history theorem with the source graph and orders.

Points deserving close mathematical review
-----------------------------------------

1. Check the source-law definitions against Arnosti's Section 1.1 and
   Definition 2, including graph sampling before the arrival permutation
   and the single common RANKING priority.
2. Check the use of Cohen--Sackrowitz, Lemma 4.1, with the truncated
   factorial carrier and its integer-valued extension. The relevant
   source pages and earlier full-paper audit are in the JSON packet.
3. Check that every capped residual assignment gives a compatible history
   with exactly the prescribed availability path. This is the reason no
   extra hidden conditioning event appears in the residual product law.
4. Check the passage from positive refined histories to the coarse
   accepted-count state and then to coupled one-time marginals. The
   projected original process is not assumed to be Markov. Choices
   conditioned on the cap are not claimed to remain independent.

Verification and limits
-----------------------

The unchanged Lean proof was compiled in Azure on 5 October 2026 with
Lean 4.34.0 and the pinned Mathlib commit in the certificate:
91 positive modules, 714 named theorems and 929 audited declarations.
Only ``propext``, ``Classical.choice`` and ``Quot.sound`` occur as axiom
dependencies. The false negative-control claim was rejected. Task resource
deletion was confirmed in the returned record. See
``../formal/verification-source-azure.json`` and ``../formal/README.rst``.

This packet records authoring-agent self-review by OpenAI Codex
(GPT-6 Astra), dated 6 October 2026. Independent external review has not
yet occurred. No novelty or priority claim is made. Reference checks and
source hashes do not by themselves establish mathematical correctness.

Run the light packet check from the repository root::

    python3 verify_packet.py

This performs local metadata checks only. It also verifies the returned
Azure records and archived artifacts. A full Lean rebuild requires the
bounded Azure workflow described in ../REPRODUCE.rst, with independent
cleanup and result retrieval. Primary-paper PDFs are not redistributed;
the source-review JSON retains their original names and hashes for provenance.
