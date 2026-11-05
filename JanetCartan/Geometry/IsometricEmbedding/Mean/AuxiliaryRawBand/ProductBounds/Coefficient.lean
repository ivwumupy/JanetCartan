module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.Source
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevProduct

/-!
# Coefficient multiplication with the joint derivative budget

The product step for `app:ch_background:eq:bg-Vaux-raw-band` and
`app:ch_background:eq:bg-Vaux-band`. These estimates are consumed by source
multiplication and by the geometric raising, stress and full-strain assembly.
-/

@[expose] public noncomputable section

namespace JanetCartan.AuxiliaryRawBand

open CurrentMean

variable {n : ℕ}

private theorem cNorm_const_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set E) (s : ℕ) (v : F) : cNorm S s (fun _ ↦ v) ≤ ‖v‖ := by
  induction s with
  | zero =>
    rw [cNorm_order_zero]
    exact Real.sSup_le (by rintro _ ⟨x, _, rfl⟩; exact le_rfl) (norm_nonneg _)
  | succ s ih =>
    rw [cNorm_succ]
    have hz : sSup ((fun x : E ↦ ‖iteratedFDeriv ℝ (s+1) (fun _ : E ↦ v) x‖) '' S) ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro _ ⟨x, _, rfl⟩
      simp [iteratedFDeriv_succ_const]
    linarith

private theorem sobolev_mono {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : Torus n → E} (hf : IsSmoothPeriodic f) {r s : ℕ} (hrs : r ≤ s) :
    periodicSobolevNorm r f ≤ periodicSobolevNorm s f := by
  apply Real.sqrt_le_sqrt
  apply (hf.summable_periodicSobolevNorm r).tsum_le_tsum _
    (hf.summable_periodicSobolevNorm s)
  intro k
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (frequencyNorm k)]) (by exact_mod_cast hrs)

/-- Dimension/order constant for coefficient multiplication in
`app:ch_background:eq:bg-Vaux-raw-band`; independent of both fibers. -/
def coefficientProductConstant (n s : ℕ) : ℝ :=
  periodicProductSobolevConstant n s * (s + 1)

/-- Positivity of the product constant used in the auxiliary profile estimates
(`app:ch_background:eq:bg-Vaux-band`). -/
theorem coefficientProductConstant_nonneg (n s : ℕ) :
    0 ≤ coefficientProductConstant n s :=
  mul_nonneg (zero_le_one.trans (one_le_periodicProductSobolevConstant n s)) (by positivity)

/-- Singleton specialization of the proved weighted product theorem, retaining
orders `r` and `s-r`. Consumed by coefficient and scalar multiplication for
`app:ch_background:eq:bg-Vaux-raw-band`. -/
theorem periodicSobolevNorm_bilinear_le
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (B : D →L[ℝ] E →L[ℝ] F) (hB : ‖B‖ ≤ 1)
    (A : Torus n → D) (f : Torus n → E)
    (hA : IsSmoothPeriodic A) (hf : IsSmoothPeriodic f) (s : ℕ) :
    periodicSobolevNorm s (fun x ↦ B (A x) (f x)) ≤
      coefficientProductConstant n s * ∑ r ∈ Finset.range (s+1),
        cNorm (fundamentalCell n) r (periodicLift A) * periodicSobolevNorm (s-r : ℕ) f := by
  have hid : IsSmoothPeriodic (fun _ : Torus n ↦ ContinuousLinearMap.id ℝ F) :=
    ⟨continuous_const, contDiff_const⟩
  have h := periodicSobolevNorm_contracted_weightedBilinear_le
    B hB (fun _ : Unit ↦ (1 : ℝ)) (fun _ ↦ zero_le_one)
    (fun x _ ↦ A x) (fun x _ ↦ f x) (fun _ ↦ hA) (fun _ ↦ hf)
    (fun _ ↦ ContinuousLinearMap.id ℝ F) hid s
  simp only [Fintype.sum_unique, one_smul, ContinuousLinearMap.id_apply,
    weightedPeriodicCNorm, weightedPeriodicSobolevNorm, one_mul,
    Real.sqrt_sq (cNorm_nonneg _ _ _),
    Real.sqrt_sq (show 0 ≤ periodicSobolevNorm _ f from Real.sqrt_nonneg _)] at h
  apply h.trans
  let P := fun r ↦ cNorm (fundamentalCell n) r (periodicLift A) *
    periodicSobolevNorm (s-r : ℕ) f
  have hP (r : ℕ) : 0 ≤ P r := mul_nonneg (cNorm_nonneg _ _ _) (Real.sqrt_nonneg _)
  have hc (a : ℕ) : cNorm (fundamentalCell n) a
      (periodicLift (fun _ : Torus n ↦ ContinuousLinearMap.id ℝ F)) ≤ 1 :=
    (cNorm_const_le _ a _).trans ContinuousLinearMap.norm_id_le
  calc
    _ ≤ periodicProductSobolevConstant n s * ∑ a ∈ Finset.range (s+1),
        ∑ r ∈ Finset.range (s-a+1), P r := by
      apply mul_le_mul_of_nonneg_left _
        (zero_le_one.trans (one_le_periodicProductSobolevConstant n s))
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro r _
      calc
        _ ≤ (1 * cNorm (fundamentalCell n) r (periodicLift A)) *
            periodicSobolevNorm (s-r : ℕ) f :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hc a) (cNorm_nonneg _ _ _))
            (sobolev_mono hf (by omega)) (Real.sqrt_nonneg _)
            (mul_nonneg zero_le_one (cNorm_nonneg _ _ _))
        _ = P r := by simp [P]
    _ ≤ periodicProductSobolevConstant n s * ∑ _a ∈ Finset.range (s+1),
        ∑ r ∈ Finset.range (s+1), P r := by
      apply mul_le_mul_of_nonneg_left _
        (zero_le_one.trans (one_le_periodicProductSobolevConstant n s))
      apply Finset.sum_le_sum
      intro a _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun r _ _ ↦ hP r)
    _ = _ := by simp [coefficientProductConstant, P, mul_assoc]

/-- Smooth operator coefficients multiply finite-dimensional Hilbert fields
with the joint derivative budget, for raising, stress and strain in
`app:ch_background:eq:bg-Vaux-raw-band`. -/
theorem periodicSobolevNorm_clm_apply_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : Torus n → E →L[ℝ] F) (f : Torus n → E)
    (hA : IsSmoothPeriodic A) (hf : IsSmoothPeriodic f) (s : ℕ) :
    periodicSobolevNorm s (fun x ↦ A x (f x)) ≤
      coefficientProductConstant n s * ∑ r ∈ Finset.range (s+1),
        cNorm (fundamentalCell n) r (periodicLift A) * periodicSobolevNorm (s-r : ℕ) f :=
  periodicSobolevNorm_bilinear_le (ContinuousLinearMap.id ℝ (E →L[ℝ] F))
    ContinuousLinearMap.norm_id_le A f hA hf s

/-- Scalar version, used for the actual source cutoff and for `1-ψ` in
`app:ch_background:eq:bg-Vaux-raw-band`. -/
theorem periodicSobolevNorm_smul_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (χ : Torus n → ℝ) (f : Torus n → E)
    (hχ : IsSmoothPeriodic χ) (hf : IsSmoothPeriodic f) (s : ℕ) :
    periodicSobolevNorm s (fun x ↦ χ x • f x) ≤
      coefficientProductConstant n s * ∑ r ∈ Finset.range (s+1),
        cNorm (fundamentalCell n) r (periodicLift χ) * periodicSobolevNorm (s-r : ℕ) f :=
  periodicSobolevNorm_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ)
    ContinuousLinearMap.opNorm_lsmul_le χ f hχ hf s

end JanetCartan.AuxiliaryRawBand
