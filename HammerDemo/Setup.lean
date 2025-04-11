import Mathlib.Tactic.Linter.UnusedTactic
import Hammer
import Aesop

section Meta

open Lean Meta Elab Tactic PremiseSelection

section ExtensibleHammer

initialize hammerExtension : SimplePersistentEnvExtension (TSyntax `tactic) (List (TSyntax `tactic)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.cons)
    addImportedFn := mkStateFromImportedEntries (·.cons) {}
  }

def extendHammer (stx : TSyntax `tactic) : CoreM Unit := do
  modifyEnv fun env => hammerExtension.addEntry env stx

def getHammerExtensions : CoreM (List (TSyntax `tactic)) := return hammerExtension.getState (← getEnv)

open Lean.Elab.Command in
elab (name := registerHammerStx) "register_hammer_extension" tac:tactic : command => liftTermElabM do
  -- remove comments
  let tac : TSyntax `tactic := ⟨tac.raw.copyHeadTailInfoFrom .missing⟩
  extendHammer tac

initialize
  Batteries.Linter.UnreachableTactic.addIgnoreTacticKind ``registerHammerStx
initialize
  Mathlib.Linter.UnusedTactic.addIgnoreTacticKind ``registerHammerStx

end ExtensibleHammer

elab "hammer" "[" premises:ident,* "]" : tactic => do
  let goal ← getMainGoal
  let suggestedPremises ← select goal {maxSuggestions := some 32}
  let premises : Array Ident := premises ++ suggestedPremises.map fun s => mkIdent s.name
  let mut addIdentStxs ← premises.mapM fun x => do
    `(Aesop.tactic_clause| (add unsafe 20% $x:ident))
  for hammerExtension in ← getHammerExtensions do
    addIdentStxs := addIdentStxs.push (← `(Aesop.tactic_clause| (add unsafe 5% (by $hammerExtension:tactic))))
  let coreRecommendation : Array Term := premises.take 16 |>.map (fun s => ⟨s.raw⟩)
  let tactic ← `(tactic| aesop? $addIdentStxs* (add unsafe 10% (by hammerCore [] [*, $coreRecommendation,*] {simpTarget := no_target})))
  logInfo (← PrettyPrinter.ppTactic tactic)
  evalTactic tactic

macro "hammer" : tactic => `(tactic| hammer [])

end Meta

example {p q r : Prop} (hp : p) (hq : q) (_hr : r) : p ∧ q := by
  hammerCore [] [*] { simpTarget := no_target }
