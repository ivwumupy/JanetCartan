module
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingProfileTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSourceProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalQuadraticSourceBudgets
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMassBudget
public import JanetCartan.Iteration.PhysicalMean.PicardProfiles
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Prehistory constants for the same full-source finite Picard run

Use the ACTUAL complete-forcing budget, actual linear all-order budget, and
actual balanced quadratic budget. P_j is the individual recurrence budget;
D_N is the common finite sum over j≤N, not an alias for P_N. Both are chosen
BEFORE R0, history, target DATA, sample and input prefix. The same D_N supplies
the exact contraction coefficient and original unweighted mass coefficient.
These are static algebraic budgets, not a claim that the analytic full-source
Picard estimate or physical mean has already been closed
(`new:eq:source-bound`, `app:ch_mean_pairs:prop:mean-iteration`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped BigOperators
@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def commonProfile (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ) (N s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), sourceIterateProfile Cg CE CQ j s
private theorem commonProfile_nonneg (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s) (N s : ℕ) :
    0 ≤ commonProfile Cg CE CQ N s :=
  Finset.sum_nonneg fun j _ ↦ sourceIterateProfile_nonneg Cg CE CQ hCg hCE hCQ j s
private theorem individual_le_common (Cg CE : ℕ → ℝ) (CQ : (ℕ → ℝ) → ℕ → ℝ)
    (hCg : ∀ s, 0 ≤ Cg s) (hCE : ∀ s, 0 ≤ CE s)
    (hCQ : ∀ A : ℕ → ℝ, (∀ s, 0 ≤ A s) → ∀ s, 0 ≤ CQ A s)
    (N j : ℕ) (hj : j ≤ N) (s : ℕ) :
    sourceIterateProfile Cg CE CQ j s ≤ commonProfile Cg CE CQ N s :=
  sourceIterate_profile_le_finite_sum Cg CE CQ hCg hCE hCQ hj s
end JanetCartan.PhysicalMean.OriginalFullSourcePicard
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalFullSourcePicard
open Lean Meta Elab Command
open OriginalCanonicalMomentAdmissionTemplate (withSelectedBefore)
private def root := `JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "full-source Picard budget: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "full-source Picard budget: later history/target/sample input escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual full-source Picard static budgets P_j and COMMON D_N=Σj≤N P_j, on the SAME original selected33 BEFORE R0/history/target/sample. The unweighted mass constant is exactly Cmass44*D_N(n+1). No analytic source or mean success premise (new:eq:source-bound; app:ch_mean_pairs:prop:mean-iteration)."
  logInfo m!"actual full-source static budget {key}/{p.size}: before history, common finite Picard sum retained"

elab "define_actual_full_source_picard_budget " mode:num : command => liftTermElabM do
  unless mode.getNat < 7 do throwError "full-source Picard budget: unknown mode"
  withSelectedBefore 44 fun native selected _ => do
    unless native.size == 44 && selected.size == 33 do throwError "full-source Picard budget: selected33/native44 changed"
    let Cg := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSourceBudget selected
    let CE := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh native
    let CQ := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.CQ native
    let hCg := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSourceBudget_nonneg selected
    let hCE := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh_nonneg native
    let hCQ := app `JanetCartan.PhysicalMean.OriginalCanonicalQuadraticSourceProfiles.CQ_nonneg native
    let costs := #[Cg,CE,CQ]
    let proofs := costs ++ #[hCg,hCE,hCQ]
    withLocalDeclNoLocalInstanceUpdate `N .default (mkConst ``Nat) fun N => do
      let params := selected.push N
      let P := app (root ++ `P) params
      let D := app (root ++ `D) params
      let rawP := app `JanetCartan.PhysicalMean.sourceIterateProfile (costs.push N)
      let rawD := app ``commonProfile (costs.push N)
      if mode.getNat == 0 then
        save `P params rawP (← inferType rawP) true
      else if mode.getNat == 1 then
        let proof := app `JanetCartan.PhysicalMean.sourceIterateProfile_nonneg (proofs.push N)
        let target := (← inferType proof).replace fun e => if e == rawP then some P else none
        save `P_nonneg params proof target
      else if mode.getNat == 2 then
        save `D params rawD (← inferType rawD) true
      else if mode.getNat == 3 then
        let proof := app ``commonProfile_nonneg (proofs.push N)
        let target := (← inferType proof).replace fun e => if e == rawD then some D else none
        save `D_nonneg params proof target
      else if mode.getNat == 4 then
        let stem := app ``individual_le_common (proofs.push N)
        forallBoundedTelescope (← inferType stem) (some 3) fun tail _ => do
          unless tail.size == 3 do throwError "full-source Picard budget: common profile index boundary changed"
          let proof := mkAppN stem tail
          let Pj := app (root ++ `P) (selected.push tail[0]!)
          let rawPj := app `JanetCartan.PhysicalMean.sourceIterateProfile (costs.push tail[0]!)
          let target := (← inferType proof).replace fun e => if e == rawPj then some Pj else if e == rawD then some D else none
          save `P_le_D (params ++ tail) proof target
      else
        let n := app ``Nat.succ #[native[0]!]
        let order := app ``Nat.succ #[n]
        let mass := app `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.Cmass native
        let cost ← termWith [(`M,mass),(`D,D),(`q,order)] "M * D q"
        if mode.getNat == 5 then
          save `M params cost (mkConst ``Real) true
        else
          let hM := app `JanetCartan.PhysicalMean.OriginalCanonicalInputMass.Cmass_nonneg native
          let hD := mkApp (app (root ++ `D_nonneg) params) order
          let proof ← termWith [(`hM,hM),(`hD,hD)] "mul_nonneg hM hD"
          let target := (← inferType proof).replace fun e => if e == cost then some (app (root ++ `M) params) else none
          save `M_nonneg params proof target
end JanetCartan.PhysicalMean.OriginalFullSourcePicard
end

define_actual_full_source_picard_budget 0
define_actual_full_source_picard_budget 1
define_actual_full_source_picard_budget 2
define_actual_full_source_picard_budget 3
define_actual_full_source_picard_budget 4
define_actual_full_source_picard_budget 5
define_actual_full_source_picard_budget 6
