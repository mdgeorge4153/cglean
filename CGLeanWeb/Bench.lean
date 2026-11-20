import CGLeanWeb.Drag

/-!
The drag-and-drop demo's benchmark (`web/main.js`), natively: replays the
built-in drag in exact and in filtered arithmetic.

    lake build demo-bench && .lake/build/bin/demo-bench [replays]

Building compiles every imported Mathlib module to native code, so the first
build takes several minutes.
-/

open CGLeanWeb.Drag

-- Times `reps` replays, best of three rounds, as the page does. The trace is
-- read from `live` on each call, as in the page, so the replays aren't shared.
def timeReplays (exact : UInt8) (reps : Nat) : IO (Float × String) := do
  let mut best := 0
  let mut out := ""
  for r in [0:3] do
    let t0 ← IO.monoNanosNow
    for _ in [0:reps] do
      out ← replayTrace exact
    let dt := (← IO.monoNanosNow) - t0
    best := if r == 0 then dt else min best dt
  return (best.toFloat / 1e6 / reps.toFloat, out)

def main (args : List String) : IO Unit := do
  let reps := (args.head? >>= String.toNat?).getD 20
  useSyntheticTrace
  let events := (← traceSize).toNat
  let (e, eOut) ← timeReplays 1 reps
  let (f, fOut) ← timeReplays 0 reps
  let line (name : String) (ms : Float) :=
    s!"{name}: {ms} ms per replay, {1000 * ms / events.toFloat} µs per event"
  IO.println s!"{events} events, {reps} replays, best of 3 rounds"
  IO.println (line "exact" e)
  IO.println (line "filtered" f)
  IO.println s!"filtered / exact: {f / e}"
  IO.println (if eOut == fOut then s!"both end at {eOut}" else s!"DISAGREE: exact {eOut}, filtered {fOut}")
