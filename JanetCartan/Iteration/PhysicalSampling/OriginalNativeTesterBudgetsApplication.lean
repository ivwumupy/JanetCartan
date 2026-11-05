module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalActualEventApplication
public meta import Lean

/-! # The identical before-history bare tester constants on the new spines

The lifted constants are literally the original `Cbare` and `Ctest` of the
bare46 input; not another testing estimate, event or threshold. In particular
the parameter reserve of the sampling kernel is not replaced by the higher
inverse/source reserve. The actual high profile already contributes σ exactly
once to the sampler scalar source (`new:eq:amplitude-test`). -/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalNativeTesterBudgetsApplication
open Lean Meta Elab Command
private def ps := `JanetCartan.PhysicalSampling
private def g := ps ++ `OriginalNativeGradedEvent
private def a := ps ++ `OriginalActualEvent
private def sm := ps ++ `OriginalNativeSmoothEvent
private def high := ps ++ `OriginalNativeInitialEvent
private def bare := ps ++ `OriginalBareEvent
private def app (n : Name) (v : Array Expr) := mkAppN (mkConst n) v
private def bodyAt (n : Name) (v : Array Expr) : MetaM Expr := do
  let some b := (← getConstInfo n).value? (allowOpaque := true) | throwError "native testing reserve: missing {n}"
  pure (b.beta v).headBeta
private def inBody (v : Expr) (name : Name) (len : Nat) : MetaM (Array Expr) := do
  let some t := v.find? (·.isAppOfArity name len) | throwError "native testing reserve: missing original {name} spine of length {len}"
  pure t.getAppArgs

/-- Extract the exact original46 arguments from the aligned native graded44
*before R₀*, keeping the separate numerical kernel and inverse orders. -/
def bare46Of44 (v : Array Expr) : MetaM (Array Expr) := do
  unless v.size == 44 do throwError "native testing reserve: expected graded44"
  let t ← inferType (app (g ++ `event_le) v)
  let p ← inBody t (sm ++ `S) 47
  let q ← inBody (← bodyAt (sm ++ `S) p) (high ++ `S) 47
  inBody (← bodyAt (high ++ `S) q) (bare ++ `S) 46

/-- Exact graded44 already selected beneath the single-cap33 maximum, with
all moment, ambient, density and signed-graph admissions before R₀. -/
def graded44Of33 (v : Array Expr) : MetaM (Array Expr) := do
  unless v.size == 33 do throwError "native testing reserve: expected single-scale33"
  let p ← bodyAt (a ++ `S) v
  unless p.isAppOfArity (g ++ `S) 44 do throwError "native testing reserve: changed actual original44 budget"
  pure p.getAppArgs

/-- Identical bare46 with all old σ/γ margins already paid from the one
before-source ceiling; no history, rate or sample handoff is needed. -/
def bare46Of33 (v : Array Expr) : MetaM (Array Expr) := do
  bare46Of44 (← graded44Of33 v)

elab "retain_native_original_tester_costs " idx:num : command => liftTermElabM <| withTransparency .reducible do
  let n := idx.getNat
  unless n == 33 || n == 44 do throwError "native testing reserve: unknown early input spine"
  let dst := if n == 33 then a else g
  forallBoundedTelescope (← getConstInfo (dst ++ `S)).type (some n) fun p _ => do
    let b ← if n == 33 then bare46Of33 p else bare46Of44 p
    for field in [`Cbare,`Ctest] do
      let name := dst ++ field
      let v := app (bare ++ field) b
      let type ← instantiateMVars (← mkForallFVars p (mkConst ``Real))
      let value ← instantiateMVars (← mkLambdaFVars p v)
      if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "native testing reserve: open {name}"
      addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
    logInfo m!"retained identical original bare46 Cbare/Ctest at before-history spine {n}"
end JanetCartan.PhysicalSampling.OriginalNativeTesterBudgetsApplication
end
