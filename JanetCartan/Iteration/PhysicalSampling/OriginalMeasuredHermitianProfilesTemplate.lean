module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernels
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBandBudgets
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredKernelsApplication
public meta import Lean

/-!
# Retaining joint jets of the same original corrected matrix amplitude

Consumer: the carrier pullback required before applying
`PhysicalMean.norm_jointFullMeasuredHermitian_kernel_source_profile` in
`app:ch_mean_pairs:eq:comparison-input`. This module retains the amplitude
from the literal `OriginalMeasuredFamily.Row.kernel` constructor and applies
its existing five coefficient profiles and SAME response-jet input. It does
not construct the response profile or the full positive physical weight.

The global extension below uses the support of the EXISTING coefficient
cutoff. It introduces no output cutoff and changes neither the response
operator nor its domain. Response jets on the whole original working compact
remain an explicit upstream obligation; these statements alone do not close
the mixed physical/parameter Hermitian estimate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSampling.OriginalMeasuredHermitianProfilesTemplate
open Set RawPrimary.AmplitudeGrades.Polynomial

private theorem cutoff_smooth_on {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) {κ : E → ℝ} (hκ : ContDiff ℝ ∞ κ) : ContDiffOn ℝ ∞ κ s :=
  hκ.contDiffOn

private theorem cut_budget_nonnegative (n N : ℕ)
    (Aκ Cjet A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    (hAκ : ∀ j, 0 ≤ Aκ j) (hCjet : ∀ j, 0 ≤ Cjet j)
    (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j)
    (hCresp : ∀ j, 0 ≤ Cresp j) :
    ∀ j, 0 ≤ productProfile
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
        Matrix (Fin N) (Fin n) ℂ →L[ℝ] Matrix (Fin N) (Fin n) ℂ)
      Aκ (fun k ↦ derivativeProfile n N Cjet A₀ A₁ B₀ B₁ k + Cresp k) j := by
  apply productProfile_nonneg _ hAκ
  intro j
  exact add_nonneg
    (polynomialProfiles_nonneg n N hCjet hA₀ hA₁ hB₀ hB₁ j).2.2.2.2 (hCresp j)

/-- Extend jets of the already cut amplitude, not of the uncut response. -/
private theorem cut_jets_on_all_points
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {κ : E → ℝ} {A : E → F} {C : ℕ → ℝ}
    {L : ℝ} {rpar : ℕ}
    (hsupport : tsupport κ ⊆ K) (hC : ∀ j, 0 ≤ C j) (hL : 1 ≤ L)
    (hjets : ∀ j, ∀ w ∈ K,
      ‖iteratedFDeriv ℝ j (fun v ↦ κ v • A v) w‖ ≤ C j * L ^ (j-rpar)) :
    ∀ j w, ‖iteratedFDeriv ℝ j (fun v ↦ κ v • A v) w‖ ≤ C j * L ^ (j-rpar) := by
  intro j w
  by_cases hw : w ∈ K
  · exact hjets j w hw
  · have hs : tsupport (fun v ↦ κ v • A v) ⊆ tsupport κ :=
      tsupport_smul_subset_left κ A
    have hz : iteratedFDeriv ℝ j (fun v ↦ κ v • A v) w = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦
        hw (hsupport (hs ((tsupport_iteratedFDeriv_subset j) h))))
    rw [hz, norm_zero]
    exact mul_nonneg (hC j) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.PhysicalSampling.OriginalMeasuredHermitianProfilesTemplate
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredHermitianProfilesTemplate
open Lean Meta Elab Command
open OriginalMeasuredKernelsApplication (withRow)
private def ns := `JanetCartan.PhysicalSampling.OriginalMeasuredHermitianProfiles
private def band := `JanetCartan.PhysicalSampling.OriginalMeasuredBand

private def save (short : Name) (params : Array Expr) (proof : Expr)
    (data := false) : MetaM Expr := do
  let target ← inferType proof
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "original Hermitian input: open or recovered declaration {short}"
  let name := ns ++ short
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  addDocStringCore name "The SAME original measured-row matrix cut amplitude and its joint derivative budget, retained from the literal full-response mean spine. The budget precedes history and rate; the jet deduction still consumes that spine's response smoothness and response jets. This is an input to, not a proof of, the full physical Hermitian profile (app:ch_mean_pairs:eq:comparison-input)."
  logInfo m!"checked SAME original corrected-amplitude input {short} at {params.size} inputs"
  return mkAppN (mkConst name) params

/-- Apply the exact existing cut-amplitude producer to the original mean
spine. The result is still conditional on its original response inputs. -/
elab "retain_original_corrected_amplitude_jets " which:num : command => liftTermElabM <|
    withTransparency .reducible <| withRow fun x later init m => do
  let t ← inferType m[56]!
  let normal := t.getAppArgs[t.getAppNumArgs - 2]!
  unless normal.isAppOfArity `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13 do
    throwError "original Hermitian input: lost actual leading coefficient"
  let raw := normal.getAppArgs
  let a := #[x[0]!] ++ raw[1:12].toArray ++ #[m[52]!,m[53]!,raw[12]!,init[33]!]
  let continuity := mkAppN
    (mkConst `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.cut_amplitude_continuous)
    (x ++ #[later[1]!,later[2]!,later[4]!])
  let colorType := (← inferType later[1]!).bindingDomain!
  let fixed := x[:45].toArray
  let root := x[:22].toArray.push x[40]!
  let Acut := mkAppN (mkConst (band ++ `Acut)) root
  let hAcut := mkAppN (mkConst (band ++ `hAcut)) root
  let cutoffJets := mkAppN (mkConst (band ++ `cutoff_jets)) root
  let smoothCut ← mkAppM ``cutoff_smooth_on #[init[29]!,init[34]!]
  let profiles := init[28:33].toArray ++ m[55:60].toArray ++ #[m[61]!] ++ init[16:28].toArray ++
    #[m[60]!, later[2]!, later[3]!, m[62]!] ++ m[65:70].toArray ++ #[later[4]!, later[5]!]
  let args := a ++ #[colorType,later[1]!] ++ profiles ++
    #[smoothCut,Acut,hAcut,cutoffJets]
  unless args.size == 56 do throwError "original Hermitian input: changed cut-profile56"
  let bound := mkAppN
    (mkConst `JanetCartan.Sampling.cutCorrectedDerivativeAmplitude_joint_bounds_of_profiles [.zero]) args
  let parameters := x ++ later[1:6].toArray
  match which.getNat with
  | 0 | 4 =>
    let n := mkApp (mkConst ``Nat.succ) a[0]!
    let hBudget := mkAppN (mkConst ``cut_budget_nonnegative)
      (#[n,a[1]!,Acut] ++ init[16:22].toArray ++ #[hAcut] ++ init[22:28].toArray)
    let budget ← forallBoundedTelescope (← inferType hBudget) (some 1) fun j t => do
      mkLambdaFVars j t.getAppArgs.back!
    if which.getNat == 0 then
      discard <| save `cutAmplitudeBudget fixed budget true
    else
      discard <| save `cutAmplitudeBudget_nonneg fixed hBudget
  | 1 =>
    let amplitude ← forallBoundedTelescope (← inferType continuity) (some 1) fun c t => do
      unless t.isAppOf ``Continuous do throwError "original Hermitian input: lost literal cut amplitude"
      mkLambdaFVars c t.appArg!
    discard <| save `cutAmplitude (x.push later[1]!) amplitude true
  | 2 => discard <| save `cutAmplitude_jets_on_working_compact parameters bound
  | 3 =>
    let localBound := mkAppN (mkConst (ns ++ `cutAmplitude_jets_on_working_compact)) parameters
    let hBudget := mkAppN (mkConst (ns ++ `cutAmplitudeBudget_nonneg)) fixed
    let globalBound ← forallBoundedTelescope (← inferType localBound) (some 1) fun c _ => do
      let p ← mkAppM ``cut_jets_on_all_points #[init[36]!,hBudget,m[62]!,mkApp localBound c[0]!]
      mkLambdaFVars c p
    discard <| save `cutAmplitude_jets_global parameters globalBound
  | _ => throwError "original Hermitian input: unknown field"

end JanetCartan.PhysicalSampling.OriginalMeasuredHermitianProfilesTemplate
end
