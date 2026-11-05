module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier
public import JanetCartan.Analysis.Calculus.HomogeneousTransversality
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Parameter differentiation of the carrier phase

The parameter identity following the averaged mixed matrix in
`app:ch_response:thm:response-literal-transfer`. The phase and frequency are
fixed during differentiation. All covectors are physical covectors (integer
unit-torus frequencies therefore enter as `2π k`).

These are conditional calculus results: the compatible phase construction must
supply homogeneity, differentiability and the buffered segment hypotheses. No
operator estimate or identification of torus and Lebesgue data is asserted.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology

namespace JanetCartan.ResponseTransfer

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The averaged normalized covector Hessian in the parameter identity of
`app:ch_response:thm:response-literal-transfer`. Its first slot is the segment
direction and its second slot is the carrier variation. -/
def averagedCovectorHessian (S : Euclidean n → Euclidean n → ℝ)
    (x ζ ε : Euclidean n) : Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ (S x)) (ζ + t • ε)

/-- The normalized order-zero coefficient `C_c` in
`app:ch_response:thm:response-literal-transfer`, as a map from the physical
increment to a parameter covector. Its normalized increment argument is `ε`;
the actual application uses `ε = ρ⁻¹ • δ`. -/
def parameterPhaseCoefficient (S : Euclidean n → Euclidean n → ℝ)
    (ζ : P → Euclidean n) (x ε : Euclidean n) (c : P) :
    Euclidean n →L[ℝ] P →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ P (Euclidean n) ℝ).flip (fderiv ℝ ζ c)).comp
    (averagedCovectorHessian S x (ζ c) ε)

/-- Evaluation of the typed coefficient from the parameter identity in
`app:ch_response:thm:response-literal-transfer`. -/
theorem parameterPhaseCoefficient_apply (S : Euclidean n → Euclidean n → ℝ)
    (ζ : P → Euclidean n) (x ε δ : Euclidean n) (c v : P) :
    parameterPhaseCoefficient S ζ x ε c δ v =
      averagedCovectorHessian S x (ζ c) ε δ (fderiv ℝ ζ c v) := rfl

/-- Fundamental theorem of calculus on the buffered normalized segment,
used in the parameter identity of `app:ch_response:thm:response-literal-transfer`.
The assumptions concern only the primitive covector derivatives of `S`. -/
theorem covectorGradient_sub_eq_averagedHessian
    (S : Euclidean n → Euclidean n → ℝ) (x ζ ε : Euclidean n)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fderiv ℝ (S x)) (ζ + t • ε))
    (hc : ContinuousOn
      (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ (S x)) (ζ + t • ε)) (Icc 0 1)) :
    fderiv ℝ (S x) (ζ + ε) - fderiv ℝ (S x) ζ =
      averagedCovectorHessian S x ζ ε ε := by
  have hc' := hc
  rw [← uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hc'
  rw [averagedCovectorHessian, ContinuousLinearMap.intervalIntegral_apply
    hc'.intervalIntegrable]
  symm
  have hpath (t : ℝ) : HasDerivAt (fun t : ℝ ↦ ζ + t • ε) ε t := by
    simpa using ((hasDerivAt_id t).smul_const ε).const_add ζ
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ (hd t (by simpa using ht)).hasFDerivAt.comp_hasDerivAt t (hpath t))
    (hc'.clm_apply continuousOn_const).intervalIntegrable

/-- Exact Fréchet parameter identity in
`app:ch_response:thm:response-literal-transfer`. Applied to `v : P`, the result is
`(∫ S_ξξ(x, ζ(c) + t δ/ρ) dt) δ (ζ'(v))`, the typed version of `C_c δ`.
Only the carrier varies; both `S` and `ρ` are fixed. -/
theorem hasFDerivAt_phaseIncrement_parameter
    (S : Euclidean n → Euclidean n → ℝ) (ζ : P → Euclidean n)
    (c : P) (ζ' : P →L[ℝ] Euclidean n) (ρ : ℝ) (hρ : 0 < ρ)
    (x δ : Euclidean n) (hζ : HasFDerivAt ζ ζ' c)
    (hhom : PosHomogeneousOne (S x))
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, ζ c + t • (ρ⁻¹ • δ) ≠ 0)
    (hfirst : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (S x) (ζ c + t • (ρ⁻¹ • δ)))
    (hphysical : DifferentiableAt ℝ (S x) (ρ • ζ c + δ) ∧
      DifferentiableAt ℝ (S x) (ρ • ζ c))
    (hsecond : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fderiv ℝ (S x)) (ζ c + t • (ρ⁻¹ • δ)))
    (hc : ContinuousOn
      (fun t : ℝ ↦ fderiv ℝ (fderiv ℝ (S x)) (ζ c + t • (ρ⁻¹ • δ))) (Icc 0 1)) :
    HasFDerivAt (fun c ↦ phaseIncrement S (ζ c) ρ x δ)
      ((averagedCovectorHessian S x (ζ c) (ρ⁻¹ • δ) δ).comp ζ') c := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have he : ρ • (ζ c + ρ⁻¹ • δ) = ρ • ζ c + δ := by
    simp [smul_add, smul_smul, hρ.ne']
  have hg0 : fderiv ℝ (S x) (ρ • ζ c) = fderiv ℝ (S x) (ζ c) :=
    hhom.fderiv_smul (by simpa using hne 0 h0)
      (by simpa using hfirst 0 h0) hρ
  have hg1 : fderiv ℝ (S x) (ρ • ζ c + δ) =
      fderiv ℝ (S x) (ζ c + ρ⁻¹ • δ) := by
    rw [← he]
    exact hhom.fderiv_smul (by simpa using hne 1 h1)
      (by simpa using hfirst 1 h1) hρ
  have h := (hphysical.1.hasFDerivAt.comp c ((hζ.const_smul ρ).add_const δ)).sub
    (hphysical.2.hasFDerivAt.comp c (hζ.const_smul ρ))
  change HasFDerivAt (fun c ↦ phaseIncrement S (ζ c) ρ x δ) _ c at h
  rw [← ContinuousLinearMap.sub_comp, hg1, hg0,
    covectorGradient_sub_eq_averagedHessian S x (ζ c) (ρ⁻¹ • δ) hsecond hc] at h
  convert h using 1
  ext v
  simp [smul_smul, hρ.ne']

/-- A primitive Hessian bound gives a frequency-independent bound for its
normalized average (`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_averagedCovectorHessian_le
    (S : Euclidean n → Euclidean n → ℝ) (x ζ ε : Euclidean n) (M : ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (S x)) (ζ + t • ε)‖ ≤ M) :
    ‖averagedCovectorHessian S x ζ ε‖ ≤ M := by
  simpa [averagedCovectorHessian] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (fun t ht ↦ hM t ⟨(by simpa using ht.1 : 0 < t).le, by simpa using ht.2⟩)

/-- The parameter coefficient is bounded by the primitive normalized Hessian
bound times the carrier derivative bound. This is the zeroth coefficient budget
used by `app:ch_response:eq:direct-envelope-profile`, with no frequency loss. -/
theorem norm_parameterPhaseCoefficient_le
    (S : Euclidean n → Euclidean n → ℝ) (ζ : P → Euclidean n)
    (x ε : Euclidean n) (c : P) (M : ℝ)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (S x)) (ζ c + t • ε)‖ ≤ M) :
    ‖parameterPhaseCoefficient S ζ x ε c‖ ≤ M * ‖fderiv ℝ ζ c‖ := by
  have hM0 : 0 ≤ M :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ (S x)) (ζ c + (0 : ℝ) • ε))).trans
      (hM 0 (by norm_num))
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM0 (norm_nonneg _))
  intro δ
  change ‖(averagedCovectorHessian S x (ζ c) ε δ).comp (fderiv ℝ ζ c)‖ ≤ _
  calc
    _ ≤ ‖averagedCovectorHessian S x (ζ c) ε δ‖ * ‖fderiv ℝ ζ c‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖averagedCovectorHessian S x (ζ c) ε‖ * ‖δ‖) * ‖fderiv ℝ ζ c‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (M * ‖δ‖) * ‖fderiv ℝ ζ c‖ := by
      gcongr
      exact norm_averagedCovectorHessian_le S x (ζ c) ε M hM
    _ = (M * ‖fderiv ℝ ζ c‖) * ‖δ‖ := by ring

end JanetCartan.ResponseTransfer
