Public Lean build
=================

The ``Lean proof (Azure)`` workflow rebuilds the project proof sources at
its displayed Git commit and prints the final theorem's axiom dependencies.
Compiler records, source hashes and a provenance report are downloadable
as the ``lean-verification-<commit>`` artifact (90-day retention).
The normal cache is used only for the pinned upstream mathlib dependencies.
No compiled project result is imported from an earlier run.

Workflow: https://github.com/MathIsEvenEasier/greedy-matching-capacity/actions/workflows/lean.yml

The workflow is manually dispatched on main. It has read-only repository
permissions, no cloud credentials, and does not run on pull requests. An
operator first provisions a disposable Azure runner using the controller
in the Minkowski repository:

https://github.com/MathIsEvenEasier/minkowski14/tree/main/ci/azure

The controller uses Azure CLI authentication and GitHub CLI authentication
on the operator's machine. Set AZURE_SUBSCRIPTION_ID and, if needed, GH_BIN
and GH_CONFIG_DIR. Run ``python3 ci/azure/audit.py prepare`` from Minkowski's
repository, then ``launch <returned-directory>``. The prepared plan gives
the unique runner label ``azure-proof-<job_id>``. Dispatch this workflow
with that label. The controller prepares one runner for each of the three
repositories; dispatch all three workflows, which run sequentially in the
order Minkowski, DNA duality, greedy matching. Each runner accepts one job.

The VM has no inbound access. A systemd cgroup caps the entire runner
session at 24 GiB with no swap and 115 minutes. A separate cloud Logic App
is armed before compute creation and requests deletion after 125 minutes,
even if the operator disconnects. The workflow also has a 110-minute limit.
A timeout, interruption or missing artifact is a failure, never verification.

After completion run ``collect <returned-directory>`` to retrieve the
runner transport record and delete both resource groups. Confirm
``cleanup-report.json`` reports ``all_deleted: true``. The guard targets
the compute group; private recovery storage stays until collection. Check
each GitHub workflow conclusion and its proof report separately: the
runner exiting successfully is not itself proof verification.

Runner registration tokens are short-lived and private. They are never
committed, printed or uploaded as public build artifacts. The local runs/
directory is ignored by Git. No subscription credentials are sent to the
runner. This is a public source rebuild using the ordinary Lean kernel,
not an audit by a second kernel implementation or a human statement audit.
