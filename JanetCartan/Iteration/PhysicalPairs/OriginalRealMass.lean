module
public import JanetCartan.Iteration.PhysicalPairs.OriginalMassRates
public import JanetCartan.Iteration.PhysicalPairs.OriginalAdmittedStage
public import JanetCartan.Iteration.PhysicalPairs.FractionalSize
/-! # Both manuscript rates with the actual coefficient mass on one sample

Keep `b²(∑√μ)²` in both conclusions and the physical exponent `r+1` for
real `r≥0`. The integer ceiling enters only the prehistory Sobolev price,
not the scaling or the original Fourier field. Consumers: the two displays
`main:eq:pair-error` and `main:eq:pair-high-size` on the SAME correction.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
open scoped SchwartzMap
namespace JanetCartan.PhysicalPairs.OriginalRealMass
open PhysicalCutoff
private theorem carrier_pos {R : ℝ} (h : 1 ≤ R) : 0 < R^carrierExponent := Real.rpow_pos_of_pos (zero_lt_one.trans_le h) _
theorem all_real {n N : ℕ} (S : 𝓢(Euclidean n,Euclidean N)) (D : ℕ → ℝ) {b m lam : ℝ} (hl : 0 < lam)
    (h : ∀ k : ℕ, FractionalSize.normAt k S ≤ 2*(D k*lam^(k+1))*b^2*m) (r : ℝ) (hr : 0 ≤ r) :
    FractionalSize.normAt r S ≤ (2*FractionalSize.cost D r)*b^2*m*lam^(r+1) := by
  let k := ⌈r⌉₊
  have h₀ := h 0
  simp only [Nat.cast_zero,Nat.zero_add,pow_one] at h₀
  have h0 : lam^r*lam = lam^(r+1) := by rw [Real.rpow_add hl,Real.rpow_one]
  have hk : lam^(r-(k:ℝ))*lam^(k+1) = lam^(r+1) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hl]; congr 1; push_cast; ring
  apply (FractionalSize.split hl hr (Nat.le_ceil r) S).trans
  apply (add_le_add (mul_le_mul_of_nonneg_left h₀ (Real.rpow_nonneg hl.le r))
    (mul_le_mul_of_nonneg_left (h k) (Real.rpow_nonneg hl.le (r-k)))).trans_eq
  calc
    _ = 2*b^2*m*(D 0*(lam^r*lam)+D k*(lam^(r-(k:ℝ))*lam^(k+1))) := by ring
    _ = _ := by rw [h0,hk]; unfold FractionalSize.cost; change _ = 2*(D 0+D k)*b^2*m*lam^(r+1); ring
end JanetCartan.PhysicalPairs.OriginalRealMass
end
public meta section
set_option warningAsError true
set_option maxHeartbeats 1400000
set_option maxRecDepth 20000
namespace JanetCartan.PhysicalPairs.OriginalRealMass
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalRealMass
private def b := `JanetCartan.PhysicalPairs
private def a (k : Name) (p : Array Expr) := mkAppN (mkConst k) p
run_cmd liftTermElabM do
  let base := b ++ `OriginalPairStage.at_shared_history
  forallBoundedTelescope (← getConstInfo base).type (some 53) fun p _ => do
    let shared := a base p
    let some S := (← inferType shared).find? (·.isAppOfArity (b ++ `OriginalSignedSum.correction) 47) | throwError "missing true shared correction"
    let sa := S.getAppArgs
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := a `JanetCartan.embeddingDimension #[n]
    let pre := p[:37].toArray ++ #[p[38]!,p[40]!,p[41]!]
    let D := a (b ++ `OriginalSizeSelection.D) pre
    let R := a `JanetCartan.historyScale #[p[44]!,mkConst `JanetCartan.growthExponent,p[46]!]
    let hR := a (b ++ `OriginalStageSize.stage_one) #[a (b ++ `OriginalSizeSelection.S) pre,p[44]!,a (b ++ `OriginalSizeSelection.hS) pre,p[45]!,p[46]!]
    let hl := a ``carrier_pos #[R,hR]
    let lam := (← inferType hl).appArg!
    let nat ← withLocalDeclD `order (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] (a (b ++ `OriginalStageSize.coefficient_mass_size) (p[:37].toArray ++ p[38:43].toArray ++ #[k] ++ p[44:].toArray))
    let rhs := (← inferType (mkApp nat (mkNatLit 0))).appArg!
    let mass := rhs.appArg!
    let scale := rhs.getAppArgs[4]!.appArg!.getAppArgs[4]!
    let real := a ``all_real #[n,N,S,D,scale,mass,lam,hl,nat]
    let metric := a (b ++ `OriginalMassRates.metric_lag) (p[:38].toArray ++ p[39:45].toArray ++ #[sa[38]!] ++ p[46:].toArray)
    let proof ← mkAppM ``And.intro #[metric,real]
    discard <| store (ns ++ `at_shared_history) p proof
run_cmd liftTermElabM do
  let chosen := b ++ `OriginalAdmittedStage.estimates
  let ci ← getConstInfo chosen
  let pair := b ++ `OriginalPairStage.estimates
  forallBoundedTelescope ci.type (some 53) fun p _ => do
    let picked := (ci.value! (allowOpaque := true)).beta p
    unless picked.isAppOf ``Eq.mp && picked.appArg!.isAppOf pair do throwError "the selected-stage proof did not retain its original event transport and numeric choices"
    let transport := picked.appFn!.appArg!
    unless transport.isAppOf ``congrArg do throwError "the original stage transport was not the identical full-wave selection"
    let eq := transport.appArg!
    unless eq.isAppOfArity (b ++ `OriginalSelectedWaves.at_genuine_sample) 48 do throwError "not the native same-good-event wave equality"
    let native := ((← getConstInfo pair).value! (allowOpaque := true)).beta picked.appArg!.getAppArgs
    unless native.isAppOfArity (b ++ `OriginalPairStage.at_shared_history) 53 do throwError "original numerical width/cap changed"
    let proof := a (ns ++ `at_shared_history) native.getAppArgs
    let t ← inferType proof
    let e := (← inferType eq).getAppArgs
    let old := e[1]!
    let pred ← withLocalDeclD `sameSampledWaves (← inferType old) fun z => do
      let ty := t.replace fun u => if u == old then some z else none
      unless ty != t do throwError "lost the original coefficient mass's identical wave family"
      mkLambdaFVars #[z] ty
    let pr ← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[pred,eq],proof]
    discard <| store (ns ++ `estimates) p pr false (some (pred.beta #[e[2]!]))
end JanetCartan.PhysicalPairs.OriginalRealMass
end
