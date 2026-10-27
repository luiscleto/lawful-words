#!/bin/sh
# The gate: every law in LAWS.bend proven in PROOF.bend, checked by bend2 and
# then by the Lean-proven BendTT kernel (--verdict needs Lean, from elan).
set -e
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
timeout 1800 env BEND_NO_TELEMETRY=1 nice -n 19 bend PROOF.bend --check-only
timeout 1800 env BEND_NO_TELEMETRY=1 nice -n 19 bend PROOF.bend --verdict
