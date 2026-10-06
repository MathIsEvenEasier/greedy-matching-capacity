Verification and reproduction
=============================

Light local check
-----------------

From the repository root::

    python3 verify_packet.py

This validates file hashes, the final certificate, the returned positive
and negative compiler records, compiled-artifact presence, axiom output,
recorded cleanup, manuscript references and the proof's declaration map.
It checks evidence integrity; it does not execute Lean or prove that a
compiler log is authentic. For independent proof checking, rebuild.

The interactive examples can be checked with a current Node.js runtime::

    node --test scripts/math.test.mjs

These are small deterministic unit checks, not a general theorem proof.
For a local browser preview::

    python3 -m http.server 8767 --directory docs --bind 127.0.0.1

Rebuilding on a bounded Azure worker
-----------------------------------

The recorded run used Lean 4.34.0 and Mathlib commit
5ed2965256430c3649e86755f9576b54eca72435. It used one Lean thread,
a 6000 MiB Lean memory limit, a 90-second timeout for each module,
a 12 GiB worker without swap, and a 35-minute worker limit. An independent
cloud cleanup controller removed the compute and control resources.

Provision an Azure worker with memory/time limits and independent cleanup
before starting a full rebuild. Do not run this workload on the local
interactive computer. The rebuild script below does not provision Azure
or provide the cloud cleanup controller; those are prerequisites.

On the worker, install the official Lean 4.34.0 toolchain, clone Mathlib,
check out the exact commit above and obtain its upstream binary cache
with ``lake exe cache get Mathlib.lean``. Then run::

    timeout 1800 python3 scripts/rebuild.py /path/to/pinned-mathlib-checkout

The script checks the Lean version and Mathlib revision, copies this
repository's Lean sources into that prepared checkout and compiles the
positive modules in the certificate's dependency order. It uses a fresh
output directory for our compiled modules, reports audited dependencies,
and checks that NegativeSource fails with the intended False goal.
A nonzero exit or timeout is a failure, not a successful partial certificate.
Retrieve the output and confirm cloud resource deletion before considering
the verification job complete.

Trust and scope
---------------

The result is MatchingCapacity.source_matching_tail_comparison in
formal/SourceModel.lean. The only input bound is degree(j)<=m; q+1 is the
common capacity. Both source history laws are nonnegative and normalized.
The source's independent per-job preference permutations are represented
by the equivalent fresh uniform available-neighbor response. The written
model correspondence explains this equivalence; Lean does not separately
construct an array of those preference permutations.

The 929-declaration audit allows only propext, Classical.choice and
Quot.sound. Mathlib and the Lean compiler/kernel are part of the trust
boundary. This record is not an independent kernel implementation audit
or independent external review of the mathematical modeling.

The evidence archive contains compiled artifacts for provenance, but the
rebuild script does not use them. It rebuilds our modules from source.
Primary-paper PDFs and cloud credentials/configuration are not distributed.
The review JSON retains the hashes and original local names of primary
PDFs for provenance; consult the DOI links to obtain those papers.
Historical research notes may mention intermediate reports or workspaces
that are not part of this compact publication package.
