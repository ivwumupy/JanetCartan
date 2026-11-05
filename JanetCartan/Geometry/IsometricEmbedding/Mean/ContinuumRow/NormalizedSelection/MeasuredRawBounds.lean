module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedRow.Estimates

/-!
# Uniform measured row bounds from the retained normalized local operators

Specialize the existing measured-row theorem to the actual uniform normalized
profiles. Its fixed-reference norms are absorbed before the varying source
scale. The finite density multiplier is then applied to the same augmented
adjoint, retaining both cut and uncut densities.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open CarrierSobolev PeriodicSobolevSpace GeometricProfile

/-- Apply the existing measured augmented-row estimate to uniform normalized
local profiles. No new operators are chosen: restriction, image and exterior
act on the supplied literal carriers. Both density bounds follow from the
same augmented raw membership. The profile inputs are the exact outputs of
`exists_finite_incidence_geometry_rawAdjoints_and_sampling` and
`exists_common_measured_normalized_data`; the finite measured constructor
instantiates them (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-density-adjoint`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_uniform_measured_row_bounds
    {n : ℕ} {ι : Type*} [Fintype ι] (H : FlatReference n)
    (χ χsrc ψ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (hχsrc : IsSmoothPeriodic χsrc) (hψ : IsSmoothPeriodic ψ)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m)
    (Craw : ι → ℕ → ℝ) (hCraw : ∀ i s, 0 ≤ Craw i s)
    (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n - 1))
    {a b : ι → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (χinitial : ι → ContDiffBump (0 : CarrierVariable n)) :
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
    ∀ coeff : ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ j, IsSmoothPeriodic (coeff j)) →
      (∀ m j x, ‖iteratedFDeriv ℝ m (periodicLift (coeff j)) x‖ ≤ P m) →
    ∀ (d : ι → CarrierData n (embeddingDimension n))
      (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i w, (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) →
      (∀ i s, ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s ((V i).adjoint (toL2 s v)) ∧
        rawSobolevNorm s ((V i).adjoint (toL2 s v)) ≤
          Craw i s * (‖v‖ + ‖toL2 s v‖)) →
      let A := augmentedRow (imageChannel coeff χ χsrc)
        (fun i ↦ CommonMeasurement.restrictCarrier χ (V i)) ψ
      (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
        A.adjoint w ∈ augmentedInputLevel n ι s ∧
        (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
          Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖)) ∧
      ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
        let u := A.adjoint w
        ∃ hf : ∀ i, MemRawSobolev 1 (u.fst.snd i),
          (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut (z₀ i) (θ₀ i) (ha i) (hb i) (u.fst.snd i) (hf i))) ∧
            MemPhysicalSobolev s (physicalComplexifyL2
            (density (z₀ i) (θ₀ i) (ha i) (hb i) (χinitial i) (u.fst.snd i) (hf i)))) ∧
          densityUncutFamilySize z₀ θ₀ ha hb s u ≤
            Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖) ∧
          densityFamilySize z₀ θ₀ ha hb χinitial s u ≤
            Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + ‖w‖) := by
  classical
  obtain ⟨C, hC, hrow⟩ := exists_measured_retained_augmented_bounds H isCompact_empty 0
    (fun _ : ι ↦ (∅ : Set (Euclidean (n - 1) × Euclidean 3))) zero_le_one
    χ χsrc ψ hχ hχsrc hψ P hP Craw hCraw
  let B (s : ℕ) := 1 + cNorm (closedBall (0 : Euclidean n) 0) (s + 2 * (n + 1) + 14) H.map
  have hB (s : ℕ) : 1 ≤ B s := by dsimp [B]; linarith [cNorm_nonneg (s := closedBall (0 : Euclidean n) 0) (s + 2 * (n + 1) + 14) H.map]
  let Cbound (s : ℕ) := C s * B s
  have hCbound (s : ℕ) : 0 ≤ Cbound s := mul_nonneg (hC s) (zero_le_one.trans (hB s))
  obtain ⟨L, hL, hdensity⟩ := exists_densityFamily_gradeNorm_bounds z₀ θ₀ ha hb χinitial
  refine ⟨Cbound, (fun s ↦ L s * Cbound (s + 1)), hCbound,
    (fun s ↦ mul_nonneg (hL s) (hCbound _)), ?_⟩
  intro coeff hcoeff hjets d V hrep hraw A
  have hraw' := hrow H.map H.contDiff
    (by simp only [sub_self, cNorm_zero]; norm_num) coeff hcoeff
    (fun m j x ↦ (hjets m j x).trans (by
      have hp := hP m
      have hn := cNorm_nonneg (s := closedBall (0 : Euclidean n) 0) (m + 2) H.map
      nlinarith))
    (fun _ _ ↦ 0) d V hrep
    (by simpa only [cNorm_empty, add_zero, one_mul] using hraw)
  have hgrade (s : ℕ) (w : OutputL2 n) (hw : w ∈ periodicSobolevLevel n (Euclidean n) s) :
      A.adjoint w ∈ augmentedInputLevel n ι s ∧
      (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
        Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + ‖w‖) := by
    obtain ⟨hm, hbound⟩ := hraw' s w hw
    refine ⟨hm, ?_⟩
    have hh : (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
        C s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + B s * ‖w‖) := by
      simpa only [empty_union, cNorm_empty, Finset.sum_const_zero, add_zero] using hbound
    apply hh.trans
    dsimp only [Cbound]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hC s)
    rw [mul_add]
    exact add_le_add (le_mul_of_one_le_left
      ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg s w) (hB s)) le_rfl
  refine ⟨hgrade, ?_⟩
  intro s w hw
  obtain ⟨hf, hmem, huncut, hcut⟩ := hdensity s _ (hgrade (s + 1) w hw).1
  refine ⟨hf, hmem, ?_, ?_⟩
  · exact (huncut.trans (mul_le_mul_of_nonneg_left (hgrade (s + 1) w hw).2 (hL s))).trans_eq
      (mul_assoc _ _ _).symm
  · exact (hcut.trans (mul_le_mul_of_nonneg_left (hgrade (s + 1) w hw).2 (hL s))).trans_eq
      (mul_assoc _ _ _).symm

end JanetCartan.ContinuumRow.NormalizedSelection
