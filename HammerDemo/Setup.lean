import Hammer

example {p q r : Prop} (hp : p) (hq : q) (_hr : r) : p ∧ q := by
  hammerCore [] [*] {}
