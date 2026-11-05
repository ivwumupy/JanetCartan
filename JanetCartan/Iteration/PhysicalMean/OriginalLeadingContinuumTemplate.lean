module

public import JanetCartan.Iteration.PhysicalMean.OriginalWeightedHermitianProfilesTemplate
public import Mathlib.Tactic.Module
public meta import Lean

/-!
# Retain the true-rate error from the already checked original parent jets

The actual parent proof already applies the joint theorem producing both its
full corrected amplitude estimate and its corrected-minus-leading estimate.
Retain the latter without rerunning any raw-coefficient, response, geometry,
positive-density or sampler constructor. This supplies the primitive needed
for the missing leading-minus-corrected continuum term in new:eq:mean-source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuum
open CurrentMean HermitianCarrierPullback OriginalWeightedHermitianProfiles SeparatedSampling

open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation
open Metric

/-- The error cost already paid by the original coefficient and response
profiles, before the rate and all history. -/
noncomputable def parentErrorCost (n N : ℕ) (C A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ) (j : ℕ) : ℝ :=
  errorProfile n N C A₀ A₁ B₀ B₁ j+Cresp j

theorem parentErrorCost_nonneg (n N : ℕ) (C A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    (j : ℕ) : 0 ≤ parentErrorCost n N C A₀ A₁ B₀ B₁ Cresp j :=
  add_nonneg (polynomialProfiles_nonneg n N hC hA₀ hA₁ hB₀ hB₁ j).2.2.2.1 (hCresp j)

/-- The original leading matrix is smooth on the same parent neighborhood
from its already retained leading normal and phase, with no new geometry. -/
theorem leading_smooth_from_normal {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
    (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    (hν : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω) :
    ContDiffOn ℝ ∞ (fullLeadingPrincipalMatrix T Q F row col Φ Y r) Ω := by
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
    (phaseGradient_smooth T Q).comp (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  apply (((normalTensor n N).isBoundedBilinearMap.contDiff.comp_contDiffOn (hξ.prodMk hν)).neg).congr
  intro w _
  exact fullLeadingPrincipalMatrix_eq_tensor T Q F row col Φ Y r w


private theorem bilinear_square_small_error
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] E →L[ℝ] F) (B P : E) (t : ℝ) :
    L (B-t • P) (B-t • P) - L B B =
      t • (t • L P P + (1/2 : ℝ) • (L (B-P) (B-P) - L (B+P) (B+P))) := by
  simp only [map_sub, map_add, map_smul, sub_apply, add_apply, smul_apply]
  module

/-- Signed leading-minus-corrected identity, used only for estimates of the
original field. P is the normalized small error; it is not a new physical atom. -/
theorem hermitian_small_error_identity {n N : ℕ}
    (B P : Matrix (Fin N) (Fin n) ℂ) (t : ℝ) :
    hermitianTensor (B-t • P) - hermitianTensor B =
      t • (t • hermitianTensor P + (1/2 : ℝ) •
        (hermitianTensor (B-P) - hermitianTensor (B+P))) := by
  simpa only [hermitianContinuousBilinear_apply, mixedHermitianTensor_self] using
    bilinear_square_small_error (hermitianContinuousBilinear (m := Fin N) (n := Fin n)) B P t

/-- Reuse the existing weighted-square calculus three times; no new derivative
product or carrier budget is required to retain the linear small-rate factor. -/
private theorem small_rate_combination_jets
    {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P U V : X → E) (hP : ContDiff ℝ ∞ P) (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (j : ℕ) (x : X) {D : ℝ} (hD : 0 ≤ D)
    (hPj : ‖iteratedFDeriv ℝ j P x‖ ≤ D)
    (hUj : ‖iteratedFDeriv ℝ j U x‖ ≤ D)
    (hVj : ‖iteratedFDeriv ℝ j V x‖ ≤ D) :
    ‖iteratedFDeriv ℝ j (t • (t • P + (1/2 : ℝ) • (V-U))) x‖ ≤ t*(2*D) := by
  have hTP : ContDiff ℝ ∞ (t • P) := hP.const_smul t
  have hDiff : ContDiff ℝ ∞ (V-U) := hV.sub hU
  have hHalf : ContDiff ℝ ∞ ((1/2 : ℝ) • (V-U)) := hDiff.const_smul _
  have hInner : ContDiff ℝ ∞ (t • P + (1/2 : ℝ) • (V-U)) := hTP.add hHalf
  rw [iteratedFDeriv_const_smul_apply (hInner.contDiffAt.of_le (by simp)),
    norm_smul, Real.norm_of_nonneg ht]
  apply mul_le_mul_of_nonneg_left _ ht
  rw [iteratedFDeriv_add_apply (hTP.contDiffAt.of_le (by simp))
    (hHalf.contDiffAt.of_le (by simp))]
  apply (norm_add_le _ _).trans
  rw [iteratedFDeriv_const_smul_apply (hP.contDiffAt.of_le (by simp)),
    iteratedFDeriv_const_smul_apply (hDiff.contDiffAt.of_le (by simp)),
    norm_smul, norm_smul, Real.norm_of_nonneg ht,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2),
    iteratedFDeriv_sub_apply (hV.contDiffAt.of_le (by simp)) (hU.contDiffAt.of_le (by simp))]
  have hFirst := (mul_le_mul_of_nonneg_left hPj ht).trans
    (mul_le_of_le_one_left hD ht1)
  have hSecond : (1/2 : ℝ) * ‖iteratedFDeriv ℝ j V x - iteratedFDeriv ℝ j U x‖ ≤ D := by
    apply (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hVj hUj))
      (by norm_num : (0 : ℝ) ≤ 1/2)).trans_eq
    ring
  linarith

private theorem small_rate_combination_profiles
    {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P U V : X → E) (hP : ContDiff ℝ ∞ P) (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (D K : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) (hK : ∀ j, 0 ≤ K j)
    (hPJ : ∀ j x, ‖iteratedFDeriv ℝ j P x‖ ≤ D j*K j)
    (hUJ : ∀ j x, ‖iteratedFDeriv ℝ j U x‖ ≤ D j*K j)
    (hVJ : ∀ j x, ‖iteratedFDeriv ℝ j V x‖ ≤ D j*K j) :
    ContDiff ℝ ∞ (t • (t • P + (1/2 : ℝ) • (V-U))) ∧
      ∀ j x, ‖iteratedFDeriv ℝ j (t • (t • P + (1/2 : ℝ) • (V-U))) x‖ ≤ t*(2*D j)*K j := by
  refine ⟨((hP.const_smul t).add ((hV.sub hU).const_smul (1/2 : ℝ))).const_smul t,?_⟩
  intro j x
  simpa only [mul_assoc] using small_rate_combination_jets P U V hP hU hV ht ht1 j x
    (mul_nonneg (hD j) (hK j)) (hPJ j x) (hUJ j x) (hVJ j x)

/-- The whole-parent signed measured error uses the existing carrier-square
calculus, unchanged exterior weight and measurement. Its cost is static and
its linear true-rate factor is not discarded. -/
theorem weighted_error_profiles_on_parameter_window {n d N : ℕ}
    (X : Set (Euclidean n)) (hX : IsCompact X)
    (ζ : Euclidean 3 → Euclidean d) (φ : Point → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (W : Set (Euclidean 3)) (hW : IsOpen W) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hφW : MapsTo (WithLp.toLp 2) (tsupport φ) W)
    (K Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d)))
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hgK : MapsTo (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) (X ×ˢ tsupport φ) K)
    (CM CB CE : ℕ → ℝ) (hCM : ∀ j, 0 ≤ CM j)
    (hCB : ∀ j, 0 ≤ CB j) (hCE : ∀ j, 0 ≤ CE j)
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (hC : ContDiff ℝ ∞ C) (hCX : tsupport C ⊆ X)
    (B E : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ)
    (hB : ContDiffOn ℝ ∞ B Ω) (hE : ContDiffOn ℝ ∞ E Ω)
    (L : ℝ) (r : ℕ) (hL : 1 ≤ L) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hMC : HasDerivativeProfile K (fun v ↦ C v.1) r L CM)
    (hBJ : ∀ j v, v ∈ K → ‖iteratedFDeriv ℝ j B v‖ ≤ CB j*L^(j-r))
    (hEJ : ∀ j v, v ∈ K → ‖iteratedFDeriv ℝ j E v‖ ≤ t*CE j*L^(j-r)) :
    let D := weightedLocalCarrierBudget (N := N) X ζ φ CM (fun j ↦ CB j+CE j)
    let H := fun w : Euclidean n × Point ↦
      let v := (w.1,WithLp.toLp 2 w.2,ζ (WithLp.toLp 2 w.2))
      φ w.2 • C w.1 (hermitianTensor (B v-E v) - hermitianTensor (B v))
    ContDiff ℝ ∞ H ∧ ∀ j w, ‖iteratedFDeriv ℝ j H w‖ ≤ t*(2*D j)*L^(j-r) := by
  intro D H
  let P := t⁻¹ • E
  have hP : ContDiffOn ℝ ∞ P Ω := hE.const_smul (t⁻¹ : ℝ)
  have hsum (j) : 0 ≤ CB j+CE j := add_nonneg (hCB j) (hCE j)
  have hLj (j) : 0 ≤ L^(j-r) := pow_nonneg (zero_le_one.trans hL) _
  have hPJ (j) (v) (hv : v ∈ K) : ‖iteratedFDeriv ℝ j P v‖ ≤ CE j*L^(j-r) := by
    change ‖iteratedFDeriv ℝ j (t⁻¹ • E) v‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply ((hE.contDiffAt (hΩ.mem_nhds (hKΩ hv))).of_le (by simp)),
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    apply (mul_le_mul_of_nonneg_left (hEJ j v hv) (inv_nonneg.mpr ht.le)).trans_eq
    simp [← mul_assoc,ht.ne']
  have hPall (j) (v) (hv : v ∈ K) :
      ‖iteratedFDeriv ℝ j P v‖ ≤ (CB j+CE j)*L^(j-r) :=
    (hPJ j v hv).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hCB j)) (hLj j))
  have hU : ContDiffOn ℝ ∞ (B+P) Ω := hB.add hP
  have hV : ContDiffOn ℝ ∞ (B-P) Ω := hB.sub hP
  have hUJ (j) (v) (hv : v ∈ K) :
      ‖iteratedFDeriv ℝ j (B+P) v‖ ≤ (CB j+CE j)*L^(j-r) := by
    rw [iteratedFDeriv_add_apply ((hB.contDiffAt (hΩ.mem_nhds (hKΩ hv))).of_le (by simp))
      ((hP.contDiffAt (hΩ.mem_nhds (hKΩ hv))).of_le (by simp))]
    exact ((norm_add_le _ _).trans (add_le_add (hBJ j v hv) (hPJ j v hv))).trans_eq (add_mul ..).symm
  have hVJ (j) (v) (hv : v ∈ K) :
      ‖iteratedFDeriv ℝ j (B-P) v‖ ≤ (CB j+CE j)*L^(j-r) := by
    rw [iteratedFDeriv_sub_apply ((hB.contDiffAt (hΩ.mem_nhds (hKΩ hv))).of_le (by simp))
      ((hP.contDiffAt (hΩ.mem_nhds (hKΩ hv))).of_le (by simp))]
    exact ((norm_sub_le _ _).trans (add_le_add (hBJ j v hv) (hPJ j v hv))).trans_eq (add_mul ..).symm
  let S := fun (A : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ)
    (w : Euclidean n × Point) ↦ φ w.2 • C w.1
      (hermitianTensor (A (w.1,WithLp.toLp 2 w.2,ζ (WithLp.toLp 2 w.2))))
  have hb := weighted_profiles_on_parameter_window (N := N) X hX ζ φ hφ hφc W hW hζ hφW
    K Ω hK hΩ hKΩ hgK CM (fun j ↦ CB j+CE j) hCM hsum
  obtain ⟨hSP,hSPJ⟩ := hb.2 C hC hCX P hP L r hL hMC hPall
  obtain ⟨hSU,hSUJ⟩ := hb.2 C hC hCX (B+P) hU L r hL hMC hUJ
  obtain ⟨hSV,hSVJ⟩ := hb.2 C hC hCX (B-P) hV L r hL hMC hVJ
  have heq : H = t • (t • S P + (1/2 : ℝ) • (S (B-P)-S (B+P))) := by
    funext w
    let v := (w.1,WithLp.toLp 2 w.2,ζ (WithLp.toLp 2 w.2))
    have hEP : t • P v = E v := by
      change t • (t⁻¹ • E v) = E v
      rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
    change φ w.2 • C w.1 (hermitianTensor (B v-E v)-hermitianTensor (B v)) = _
    rw [← hEP,hermitian_small_error_identity]
    simp only [S,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,map_smul,map_add,map_sub,
      smul_add,smul_sub,smul_smul]
    module
  rw [heq]
  exact small_rate_combination_profiles (S P) (S (B+P)) (S (B-P)) hSP hSU hSV
    ht.le ht1 D (fun j ↦ L^(j-r)) hb.1 hLj hSPJ hSUJ hSVJ

/-- The signed field in the actual continuum is leading minus corrected,
not the auxiliary normalized-error square used to prove its estimate. -/
theorem weighted_leading_profiles_on_parameter_window {n d N : ℕ}
    (X : Set (Euclidean n)) (hX : IsCompact X)
    (ζ : Euclidean 3 → Euclidean d) (φ : Point → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (W : Set (Euclidean 3)) (hW : IsOpen W) (hζ : ContDiffOn ℝ ∞ ζ W)
    (hφW : MapsTo (WithLp.toLp 2) (tsupport φ) W)
    (K Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d)))
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hgK : MapsTo (fun w : Euclidean n × Point ↦
      (w.1, WithLp.toLp 2 w.2, ζ (WithLp.toLp 2 w.2))) (X ×ˢ tsupport φ) K)
    (CM CB CE : ℕ → ℝ) (hCM : ∀ j, 0 ≤ CM j)
    (hCB : ∀ j, 0 ≤ CB j) (hCE : ∀ j, 0 ≤ CE j)
    (C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n)
    (hC : ContDiff ℝ ∞ C) (hCX : tsupport C ⊆ X)
    (B A : Euclidean n × (Euclidean 3 × Euclidean d) → Matrix (Fin N) (Fin n) ℂ)
    (hB : ContDiffOn ℝ ∞ B Ω) (hA : ContDiffOn ℝ ∞ A Ω)
    (L : ℝ) (r : ℕ) (hL : 1 ≤ L) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hMC : HasDerivativeProfile K (fun v ↦ C v.1) r L CM)
    (hBJ : ∀ j v, v ∈ K → ‖iteratedFDeriv ℝ j B v‖ ≤ CB j*L^(j-r))
    (hEJ : ∀ j v, v ∈ K → ‖iteratedFDeriv ℝ j (B-A) v‖ ≤ t*CE j*L^(j-r)) :
    let D := weightedLocalCarrierBudget (N := N) X ζ φ CM (fun j ↦ CB j+CE j)
    let H := fun w : Euclidean n × Point ↦
      let v := (w.1,WithLp.toLp 2 w.2,ζ (WithLp.toLp 2 w.2))
      φ w.2 • C w.1 (hermitianTensor (A v) - hermitianTensor (B v))
    ContDiff ℝ ∞ H ∧ ∀ j w, ‖iteratedFDeriv ℝ j H w‖ ≤ t*(2*D j)*L^(j-r) := by
  simpa only [Pi.sub_apply,sub_sub_cancel] using
    weighted_error_profiles_on_parameter_window X hX ζ φ hφ hφc W hW hζ hφW
      K Ω hK hΩ hKΩ hgK CM CB CE hCM hCB hCE C hC hCX
      B (B-A) hB (hB.sub hA) L r hL t ht ht1 hMC hBJ hEJ

end JanetCartan.PhysicalMean.OriginalLeadingContinuum

end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
open Lean Meta Elab Command

private def native := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native
private def joint := `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude_joint_bounds
private def root := `JanetCartan.PhysicalMean.OriginalLeadingContinuum

private def nativeTelescope (type : Expr) (count : Nat)
    (go : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,result,xs => go xs result
    | remaining+1,type,xs => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "actual leading continuum: native telescope ended at {xs.size}"
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop remaining (body.instantiate1 x) (xs.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
          loop remaining (body.instantiate1 x) (xs.push x)

/-- Read only the checked52 proof. The generic50 arguments must be independent
of the three later point/jet binders, which are discarded before reuse. -/
def withParentJoint (go : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo (native ++ `jets)
  let some body := info.value? (allowOpaque := true) |
    throwError "actual leading continuum: missing frozen parent jets52 value"
  nativeTelescope info.type 52 fun params _ => do
    let value := (body.beta params).headBeta
    let some full := value.find? (·.isAppOfArity joint 53) |
      throwError "actual leading continuum: checked joint53 application is absent"
    let args := full.getAppArgs[:50].toArray
    if args.any (fun e => e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry) then
      throwError "actual leading continuum: generic50 depends on later jet/point or recovered data"
    go params args

private def save (key : Name) (params : Array Expr) (proof target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then
      throwError "actual leading continuum: open or recovered declaration {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking {name}/{params.size}"
  out.flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  addDocStringCore name "Actual original corrected-minus-leading amplitude error on the unchanged parent sigma-cover, preserving the true colored rate, full response and original positive scalar. This is a primitive for the continuum summand of new:eq:mean-source, not the full initializer estimate."
  out.putStrLn s!"kernel passed {name}/{params.size}"
  out.flush

/-- Preserve the second half of the SAME checked joint bound. No new analytic
premise or inner-cutoff/phase mask is introduced on the baseline. -/
elab "retain_original_parent_true_rate_error" : command => liftTermElabM do
  withParentJoint fun params args => do
    let proof := mkAppN (mkConst joint) args
    nativeTelescope (← inferType proof) 3 fun point target => do
      unless target.isAppOfArity ``And 2 do
        throwError "actual leading continuum: joint theorem no longer supplies paired bounds"
      let error := Expr.proj ``And 1 (mkAppN proof point)
      save `parent_error_jets params (← mkLambdaFVars point error)
        (← mkForallFVars point target.getAppArgs[1]!)

private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def weighted := `JanetCartan.PhysicalMean.OriginalWeightedHermitianProfiles
private def calculus := `JanetCartan.PhysicalMean.HermitianCarrierPullback

/-- Read the already checked weighted-profile application, including its exact
outer weight, genuine graph, measurement, reserve and scale. -/
def withWeightedParent (go : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) :
    MetaM Unit := withParentJoint fun p a => do
  let some body := (← getConstInfo (weighted ++ `weighted_profile)).value? (allowOpaque := true) |
    throwError "actual leading continuum: missing frozen weighted profile"
  let value := (body.beta p).headBeta
  let .proj ``And 1 geometric := value.getAppFn |
    throwError "actual leading continuum: changed frozen weighted proof projection"
  unless geometric.isAppOfArity (weighted ++ `weighted_profiles_on_parameter_window) 23 &&
      value.getAppNumArgs == 10 do
    throwError "actual leading continuum: changed frozen weighted23/dynamic10 ABI"
  go p a geometric.getAppArgs value.getAppArgs

/-- Exact static costs. Four commands keep each publication at ordinary limits;
none introduces an input beyond original44 and the fixed row. -/
elab "publish_original_leading_error_cost " mode:num : command => liftTermElabM do
  withWeightedParent fun p a g _ => do
    let fixed := p[:44].toArray.push p[50]!
    let costArgs := a[:2].toArray ++ a[26:32].toArray
    let CE := app (root ++ `CE) fixed
    let hCE := app (root ++ `CE_nonneg) fixed
    match mode.getNat with
    | 0 =>
      let term := app (root ++ `parentErrorCost) costArgs
      save `CE fixed term (← inferType term) true
    | 1 =>
      let proof := app (root ++ `parentErrorCost_nonneg) (costArgs ++ a[32:38].toArray)
      save `CE_nonneg fixed proof (← inferType proof)
    | 2 | 3 =>
      let some body := (← getConstInfo (weighted ++ `D)).value? |
        throwError "actual leading continuum: missing original static carrier cost"
      let raw := (body.beta fixed).headBeta
      unless raw.isAppOfArity (calculus ++ `weightedLocalCarrierBudget) 8 do
        throwError "actual leading continuum: changed fixed carrier-budget producer"
      let da := raw.getAppArgs
      let CB := da[7]!
      let pair ← withLocalDeclNoLocalInstanceUpdate `j .default (mkConst ``Nat) fun j => do
        let sum ← mkAppM ``HAdd.hAdd #[mkApp CB j,mkApp CE j]
        let hsum ← mkAppM ``add_nonneg #[mkApp g[22]! j,mkApp hCE j]
        return (← mkLambdaFVars #[j] sum,← mkLambdaFVars #[j] hsum)
      let inputs := da.set! 7 pair.1
      if mode.getNat == 2 then
        let term := app (calculus ++ `weightedLocalCarrierBudget) inputs
        save `D fixed term (← inferType term) true
      else
        let proof := app (calculus ++ `weightedLocalCarrierBudget_nonneg) (inputs ++ #[g[21]!,pair.2])
        save `D_nonneg fixed proof (← inferType proof)
    | _ => throwError "actual leading continuum: unknown static error-cost mode"

/-- The exact signed measured tensor, no baseline cutoff or angular factor,
with the true colored rate and the original coefficient scale still visible. -/
elab "publish_original_weighted_leading_error" : command => liftTermElabM do
  withWeightedParent fun p a g d => do
    let fixed := p[:44].toArray.push p[50]!
    let CE := app (root ++ `CE) fixed
    let hCE := app (root ++ `CE_nonneg) fixed
    let hLeading := app (root ++ `leading_smooth_from_normal)
      (a[:12].toArray ++ #[a[14]!,a[16]!,a[20]!,a[21]!])
    let hLeadingType ← inferType hLeading
    unless hLeadingType.isAppOf ``ContDiffOn do
      throwError "actual leading continuum: leading regularity changed"
    let A := hLeadingType.getAppArgs[hLeadingType.getAppNumArgs-2]!
    let args := g[:21].toArray ++ #[CE,g[21]!,g[22]!,hCE] ++
      #[d[0]!,d[1]!,d[2]!,d[3]!,A,d[4]!,hLeading,d[5]!,d[6]!,d[7]!,
        a[38]!,a[40]!,a[41]!,d[8]!,d[9]!,app (root ++ `parent_error_jets) p]
    let proof := app (root ++ `weighted_leading_profiles_on_parameter_window) args
    let rawTarget ← inferType proof
    let .letE _ _ rawBudget _ _ := rawTarget.consumeMData |
      throwError "actual leading continuum: lost static weighted budget let"
    let target := OriginalWeightedHermitianProfilesTemplate.rootLets rawTarget
    unless target.isAppOfArity ``And 2 && target.getAppArgs[0]!.isAppOf `ContDiff do
      throwError "actual leading continuum: lost signed smoothness/profile pair"
    let rawField := target.getAppArgs[0]!.appArg!
    save `weightedError p rawField (← inferType rawField) true
    let field := app (root ++ `weightedError) p
    let budget := app (root ++ `D) fixed
    let namedTarget := target.replace fun e =>
      if e == rawField then some field else if e == rawBudget then some budget else none
    unless (namedTarget.find? (·.isAppOf (root ++ `weightedError))).isSome &&
        (namedTarget.find? (·.isAppOf (root ++ `D))).isSome do
      throwError "actual leading continuum: field or static cost name did not survive"
    save `weighted_error_profile p proof namedTarget

end JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
end
