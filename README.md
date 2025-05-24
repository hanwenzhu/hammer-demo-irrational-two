# hammer-demo-irrational-two

The is a demo of LeanHammer proving the fact that √2 is irrational.

## System setup

Before experimenting with the current hammer evaluation tool, go to the following Lean code (at the end of [HammerDemo/Setup.lean](HammerDemo/Setup.lean)):

```lean
import Hammer

example {p q r : Prop} (hp : p) (hq : q) (hr : r) : p ∧ q := by
  hammerCore [] [*] { simpTarget := no_target }
```

This code should prove the goal and yield the following suggestion:

```
Try this:
  duper [*] {preprocessing := full}
```

This ensures the hammer is working properly, and in particular Zipperposition is installed correctly.

## Demos
Stable internet is required for demo, since an external server is used.

The demo (√2 is irrational) is in [HammerDemo/IrrationalSqrtTwo.lean](HammerDemo/IrrationalSqrtTwo.lean).

For each position in the proof labelled `hammer`able, you may replace the following tactic block with a single `hammer`, which will close the goal and suggest a replacement found by LeanHammer.
Some of them are trivial and solved by `simp_all`; some others are nontrivial and require `aesop` and/or `auto`.
You may also first replace it with `suggest_premises` to see the premises retrieved (by a remote server).
