module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationField
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.FieldBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAuxiliaryBounds
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.JetComposition
public import JanetCartan.Analysis.Fourier.Periodic.Interpolation
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricRemainder.TensorBounds

/-!
# Finite-reserve bounds for the actual uncut preparation field

For `app:ch_mean_pairs:prop:mean-coarse`, the same uncut image datum produces
both the physical half tangent lift and its full linearized metric. The source
multiplier and Bessel gain give a finite Sobolev-to-jet estimate. Primitive jets
of the cutoff raising coefficient and immersion then bound both physical
objects, including the final-cutoff derivative terms.

These are finite-reserve estimates, consumed by the low bounds for
`preparationAccumulatedField`. Constants precede the raw datum and every finite
source sequence. The actual inverse/adjoint must still supply its raw estimates;
sharp all-order profiles require the separate one-high/interpolation argument.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius Topology

namespace JanetCartan.CurrentMean
open ContinuumRow PeriodicSobolevSpace

variable {n N : ℕ}

local instance preparationJetNorm : NormedAddCommGroup (Euclidean n →L[ℝ] Euclidean N) :=
  inferInstance
local instance preparationJetSpace : NormedSpace ℝ (Euclidean n →L[ℝ] Euclidean N) :=
  inferInstance
local instance preparationTensorJetNorm :
    NormedAddCommGroup ((Euclidean n →L[ℝ] Euclidean N) →L[ℝ] MetricTensor n) := inferInstance
local instance preparationTensorJetSpace :
    NormedSpace ℝ ((Euclidean n →L[ℝ] Euclidean N) →L[ℝ] MetricTensor n) := inferInstance

private theorem preparation_raw_sobolev_mono
    (h : OutputL2 n) (hh : ∀ j, h ∈ periodicSobolevLevel n (Euclidean n) j)
    {i j : ℕ} (hij : i ≤ j) : periodicSobolevNorm i h ≤ periodicSobolevNorm j h := by
  simpa only [periodicSobolevSeminorm_eq] using periodicSobolevSeminorm_mono hij ⟨h, hh j⟩

private theorem preparation_smooth_sobolev_mono
    {f : Torus n → Euclidean n} (hf : IsSmoothPeriodic f)
    {i j : ℕ} (hij : i ≤ j) : periodicSobolevNorm i f ≤ periodicSobolevNorm j f := by
  apply Real.sqrt_le_sqrt
  apply (hf.summable_periodicSobolevNorm i).tsum_le_tsum _
    (hf.summable_periodicSobolevNorm j)
  intro k
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (frequencyNorm k)])
    (by exact_mod_cast hij)

private theorem preparation_periodic_cNorm_le
    {f : Torus n → Euclidean n} (hf : IsSmoothPeriodic f)
    (K : Set (Euclidean n)) (s : ℕ) :
    cNorm K s (periodicLift f) ≤ cNorm (fundamentalCell n) s (periodicLift f) := by
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ sSup_norm_iteratedFDeriv_nonneg (fundamentalCell n) j (periodicLift f))
  intro j hj x _
  apply norm_iteratedFDeriv_periodicLift_le f j _ x
  intro y hy
  exact le_csSup (bddAbove_norm_iteratedFDeriv (isCompact_fundamentalCell n)
    (hf.2.of_le (by simp) : ContDiff ℝ s (periodicLift f)) hj) (Set.mem_image_of_mem _ hy)

/-- The SAME uncut Bessel covector has a finite jet bound from the raw
image datum. The shift is explicit and independent of the requested order;
no density synthesis on arbitrary L² inputs is asserted
(`app:ch_mean_pairs:eq:mean-coarse-field-profile`). -/
theorem exists_preparationCovector_cNorm_bound (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χsrc : C(Torus n, ℝ))
      (_hs : IsSmoothPeriodic (χsrc : Torus n → ℝ)),
      cNorm (fundamentalCell n) (s + n) (periodicLift χsrc) ≤ M →
      ∀ (h : OutputL2 n) (_hh : ∀ j, h ∈ periodicSobolevLevel n (Euclidean n) j),
      cNorm (fundamentalCell n) s (periodicLift (preparationCovector χsrc h)) ≤
        C * periodicSobolevNorm (s + n : ℕ) h := by
  let q := s + n
  let C := fourierInterpolationConstant n s (q + 1)
  let B := AuxiliaryRawBand.coefficientProductConstant n q * (q + 1) * M
  have hC : 0 ≤ C := fourierInterpolationConstant_nonneg _ _ _
  have hB : 0 ≤ B := by
    exact mul_nonneg (mul_nonneg (AuxiliaryRawBand.coefficientProductConstant_nonneg n q)
      (by positivity)) hM
  refine ⟨2 * C * B, by positivity, ?_⟩
  intro χsrc hs hsrc h hh
  let u := preparationCovector χsrc h
  have hu : IsSmoothPeriodic u := isSmoothPeriodic_preparationCovector χsrc hs h hh
  have hcov : periodicSobolevNorm (q + 1 : ℕ) u ≤ B * periodicSobolevNorm q h := by
    apply (periodicSobolevNorm_preparationCovector_succ_le χsrc hs h hh q).trans
    calc
      _ ≤ AuxiliaryRawBand.coefficientProductConstant n q *
          ∑ _j ∈ Finset.range (q + 1), M * periodicSobolevNorm q h := by
        apply mul_le_mul_of_nonneg_left _ (AuxiliaryRawBand.coefficientProductConstant_nonneg n q)
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul ((cNorm_mono_order (by simpa using hj)).trans hsrc)
          (preparation_raw_sobolev_mono h hh (Nat.sub_le q j)) (Real.sqrt_nonneg _) hM
      _ = _ := by simp [B, mul_assoc]
  have hzero : periodicL2Norm u ≤ periodicSobolevNorm (q + 1 : ℕ) u := by
    rw [← periodicSobolevNorm_zero_eq_periodicL2Norm
      (hu.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace u))]
    simpa only [Nat.cast_zero] using preparation_smooth_sobolev_mono hu (Nat.zero_le (q + 1))
  have hi := cNorm_le_fourierInterpolation hu
    (r := s) (m := q + 1) (K := 1) (by dsimp [q]; push_cast; linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]) le_rfl
  simp only [Real.one_rpow, one_mul] at hi
  apply hi.trans
  change C * (periodicL2Norm u + periodicSobolevNorm (q + 1 : ℕ) u) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hzero hC,
    mul_le_mul_of_nonneg_left hcov hC]

private def preparationStrainBilinear (n N : ℕ) :
    (Euclidean n →L[ℝ] Euclidean N) →L[ℝ]
      (Euclidean n →L[ℝ] Euclidean N) →L[ℝ] MetricTensor n := by
  let L : (Euclidean n →L[ℝ] Euclidean N) →ₗ[ℝ]
      (Euclidean n →L[ℝ] Euclidean N) →ₗ[ℝ] MetricTensor n := LinearMap.mk₂ ℝ
    (fun A B ↦ (fun i j ↦ inner ℝ (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single j 1)) +
      inner ℝ (B (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1)) : MetricTensor n))
    (by intros; ext i j; simp only [add_apply, inner_add_left, inner_add_right, Matrix.add_apply]; ring)
    (by intros; ext i j; simp only [smul_apply, real_inner_smul_left, inner_smul_right, Matrix.smul_apply, smul_eq_mul]; ring)
    (by intros; ext i j; simp only [add_apply, inner_add_left, inner_add_right, Matrix.add_apply]; ring)
    (by intros; ext i j; simp only [smul_apply, real_inner_smul_left, inner_smul_right, Matrix.smul_apply, smul_eq_mul]; ring)
  exact L.mkContinuous₂ (2 * n) (by
    intro A B
    apply (metricTensor_norm_le_of_entries
      (show 0 ≤ 2 * (‖A‖ * ‖B‖) by positivity) ?_).trans_eq
    · ring
    · intro i j
      have hb (i j : Fin n) :
          ‖inner ℝ (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single j 1))‖ ≤
            ‖A‖ * ‖B‖ :=
        (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (mul_le_mul
          (by simpa [PiLp.norm_single] using A.le_opNorm (EuclideanSpace.single i 1))
          (by simpa [PiLp.norm_single] using B.le_opNorm (EuclideanSpace.single j 1))
          (norm_nonneg _) (norm_nonneg _))
      change ‖inner ℝ (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single j 1)) +
        inner ℝ (B (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1))‖ ≤ _
      rw [real_inner_comm (A (EuclideanSpace.single j 1)) (B (EuclideanSpace.single i 1))]
      exact (norm_add_le _ _).trans (by linarith [hb i j, hb j i]))

private theorem preparation_linearizedMetric_cNorm_le
    {K : Set (Euclidean n)} (hK : IsCompact K) (s : ℕ)
    {F V : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F) (hV : ContDiff ℝ ∞ V) :
    cNorm K s (linearizedMetric F V) ≤
      (2 : ℝ) ^ s * ‖preparationStrainBilinear n N‖ *
        cNorm K (s + 1) F * cNorm K (s + 1) V := by
  have h := cNorm_bilinear_le (preparationStrainBilinear n N) hK
    (hF.fderiv_right (by simp) : ContDiff ℝ s (fderiv ℝ F))
    (hV.fderiv_right (by simp) : ContDiff ℝ s (fderiv ℝ V))
  change cNorm K s (linearizedMetric F V) ≤ _ at h
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (GeometricProfile.cNorm_fderiv_le K s F) (by positivity))
    (GeometricProfile.cNorm_fderiv_le K s V) (cNorm_nonneg _ _ _)
      (mul_nonneg (by positivity) (cNorm_nonneg _ _ _)))

/-- Agreement with the literal cutoff half tangent lift on the physical
chart. The coefficient is fixed before the raw datum; it is not an auxiliary
field chosen independently at each order
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationAuxiliaryField_eqOn_raisingCoefficient
    (χsrc : C(Torus n, ℝ)) (h : OutputL2 n)
    (F : Euclidean n → Euclidean N) (χout : Euclidean n → ℝ)
    (A : Euclidean n → Euclidean n →L[ℝ] Euclidean N) (W : Set (Euclidean n))
    (hA : ∀ x ∈ W, A x = χout x • AuxiliaryRawBand.halfTangentCoefficient F x) :
    EqOn (preparationAuxiliaryField χsrc h F χout)
      (fun x ↦ A x (periodicLift (preparationCovector χsrc h) x)) W := by
  intro x hx
  dsimp only
  rw [hA x hx, smul_apply,
    AuxiliaryRawBand.halfTangentCoefficient_apply]
  rfl

/-- Finite-reserve bounds for the actual uncut field AND its full strain.
The primitive coefficient `A` is the original output cutoff times the half
raising map on an open neighborhood. Equality of jets transfers the estimate
to the physical field, so every derivative of that cutoff is included.
The constant precedes the coefficients, datum and physical chart
(`app:ch_mean_pairs:eq:mean-coarse-field-profile`). -/
theorem exists_preparationAuxiliaryField_cNorm_bound (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χsrc : C(Torus n, ℝ))
      (_hs : IsSmoothPeriodic (χsrc : Torus n → ℝ)),
      cNorm (fundamentalCell n) (s + 1 + n) (periodicLift χsrc) ≤ M →
      ∀ (F : Euclidean n → Euclidean N) (χout : Euclidean n → ℝ)
        (A : Euclidean n → Euclidean n →L[ℝ] Euclidean N),
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ A →
      ∀ (W K : Set (Euclidean n)), IsOpen W → IsCompact K → K ⊆ W →
      (∀ x ∈ W, A x = χout x • AuxiliaryRawBand.halfTangentCoefficient F x) →
      cNorm K (s + 1) A ≤ M → cNorm K (s + 1) F ≤ M →
      ∀ (h : OutputL2 n) (_hh : ∀ j, h ∈ periodicSobolevLevel n (Euclidean n) j),
      cNorm K s (preparationAuxiliaryField χsrc h F χout) +
        cNorm K s (linearizedMetric F (preparationAuxiliaryField χsrc h F χout)) ≤
          C * periodicSobolevNorm (s + 1 + n : ℕ) h := by
  obtain ⟨Cu, hCu, huB⟩ := exists_preparationCovector_cNorm_bound (n := n) (s + 1) hM
  let Cv := (2 : ℝ) ^ (s + 1) * M * Cu
  let Cs := (2 : ℝ) ^ s * ‖preparationStrainBilinear n N‖ * M
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  refine ⟨(1 + Cs) * Cv, by positivity, ?_⟩
  intro χsrc hs hsrc F χout A hF hA W K hW hK hKW hraise hAM hFM h hh
  let u := periodicLift (preparationCovector χsrc h)
  let V := fun x ↦ A x (u x)
  have hu : ContDiff ℝ ∞ u := (isSmoothPeriodic_preparationCovector χsrc hs h hh).2
  have hV : ContDiff ℝ ∞ V := hA.clm_apply hu
  have heq := preparationAuxiliaryField_eqOn_raisingCoefficient χsrc h F χout A W hraise
  have hev (x : Euclidean n) (hx : x ∈ W) :
      preparationAuxiliaryField χsrc h F χout =ᶠ[𝓝 x] V :=
    Filter.eventually_of_mem (hW.mem_nhds hx) (fun y hy ↦ heq hy)
  have hstrain : EqOn (linearizedMetric F (preparationAuxiliaryField χsrc h F χout))
      (linearizedMetric F V) W := by
    intro x hx
    exact congrArg (fun L : Euclidean n →L[ℝ] Euclidean N ↦
      (fun i j ↦ inner ℝ (partialDeriv F x i) (L (EuclideanSpace.single j 1)) +
        inner ℝ (L (EuclideanSpace.single i 1)) (partialDeriv F x j) : MetricTensor n))
      (hev x hx).fderiv_eq
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq (fun x hx ↦ hev x (hKW hx)) s,
    GeometricProfile.cNorm_eq_of_eventuallyEq (fun x hx ↦
      Filter.eventually_of_mem (hW.mem_nhds (hKW hx)) (fun y hy ↦ hstrain hy)) s]
  have huK : cNorm K (s + 1) u ≤ Cu * periodicSobolevNorm (s + 1 + n : ℕ) h :=
    (preparation_periodic_cNorm_le (isSmoothPeriodic_preparationCovector χsrc hs h hh)
      K (s + 1)).trans
      (huB χsrc hs hsrc h hh)
  have hvB : cNorm K (s + 1) V ≤ Cv * periodicSobolevNorm (s + 1 + n : ℕ) h := by
    have hv := cNorm_bilinear_le_of_opNorm_le
      (ContinuousLinearMap.id ℝ (Euclidean n →L[ℝ] Euclidean N)) hK
      (hA.of_le (by simp) : ContDiff ℝ (s + 1) A)
      (hu.of_le (by simp) : ContDiff ℝ (s + 1) u) ContinuousLinearMap.norm_id_le
    change cNorm K (s + 1) V ≤ _ at hv
    apply hv.trans
    calc
      _ ≤ (2 : ℝ) ^ (s + 1) * 1 * M * (Cu * periodicSobolevNorm (s + 1 + n : ℕ) h) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAM (by positivity)) huK
          (cNorm_nonneg _ _ _) (by positivity)
      _ = _ := by dsimp [Cv]; ring
  have hsB := (preparation_linearizedMetric_cNorm_le hK s hF hV).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hFM (by positivity)) hvB
      (cNorm_nonneg _ _ _) (by positivity))
  have hv0 : cNorm K s V ≤ Cv * periodicSobolevNorm (s + 1 + n : ℕ) h :=
    (cNorm_mono_order (Nat.le_succ s)).trans hvB
  dsimp [Cs]
  nlinarith [hsB]

end JanetCartan.CurrentMean
