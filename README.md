# hammer-demo-apr2025

## System setup

(From Josh's ntp-toolkit README:)

Before experimenting with the current hammer evaluation tool, make sure you are able to invoke the `hammer` tactic successfully by installing [zipperposition](https://github.com/sneeuwballen/zipperposition) (version 2.1) and go to the following Lean code (at the end of [HammerDemo/Setup.lean](HammerDemo/Setup.lean)):
```
example {p q r : Prop} (hp : p) (hq : q) (hr : r) : p ∧ q := by
  hammerCore [] [*] { simpTarget := no_target }
```

This code should prove the goal and yield the following suggestion:
```
Try this:
  apply @Classical.byContradiction
  intro negGoal
  duper [hp, hq, negGoal] {preprocessing := full}
```

## Demos
Stable internet is required for demo, since an external server is used.

The demo (√2 is irrational) is in [HammerDemo/IrrationalSqrtTwo.lean](HammerDemo/IrrationalSqrtTwo.lean).

For each position in the proof labelled `hammer`able, you may replace the following tactic block with a single `hammer`, which will close the goal and suggest a replacement found by LeanHammer.
Some of them are trivial and solved by `simp_all`; some others are nontrivial and require a combination of `aesop` and `auto`.
You may also first replace it with `suggest_premises` to see the premises retrieved (by a remote server).
