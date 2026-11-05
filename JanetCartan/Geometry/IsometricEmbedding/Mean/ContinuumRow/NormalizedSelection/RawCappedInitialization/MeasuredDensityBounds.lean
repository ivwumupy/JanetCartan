module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedRow.Estimates

/-!
# Measured corrected rows with the original density reserve

Apply the existing retained-row theorem to the actual local corrected raw
profiles. Absorb only fixed-reference norms; the high density norm remains
attached to the low datum norm.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumAdjoint ContinuumAdjoint.Canonical ContinuumAdjoint.DensityMultiplier
open CarrierSobolev PeriodicSobolevSpace GeometricProfile

/-- On the supplied measured carriers, retain the single high initial-density
norm from the original corrected raw adjoints. The actual raw producer is
`ContinuumInverse.exists_corrected_seed_rawAdjoint_for_submasks`, applied by
`exists_finite_incidence_row_with_corrected_rawAdjoints`; the measured
constructor instantiates this deduction on that same row. Fixed-reference
constants precede all varying densities and source scales
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_uniform_measured_density_row_bounds
    {n : ℕ} {ι : Type*} [Fintype ι] (H : FlatReference n)
    (χ χsrc ψ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (hχsrc : IsSmoothPeriodic χsrc) (hψ : IsSmoothPeriodic ψ)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m)
    (Craw : ι → ℕ → ℝ) (hCraw : ∀ i s, 0 ≤ Craw i s)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n - 1))
    {a b : ι → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (χinitial : ι → ContDiffBump (0 : CarrierVariable n)) :
    ∃ Cbound Lbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧ (∀ s, 0 ≤ Lbound s) ∧
    ∀ coeff : ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ j, IsSmoothPeriodic (coeff j)) →
      (∀ m j x, ‖iteratedFDeriv ℝ m (periodicLift (coeff j)) x‖ ≤ P m) →
    ∀ (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
      (d : ι → CarrierData n (embeddingDimension n))
      (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i w, (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) →
      (∀ i s, ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s ((V i).adjoint (toL2 s v)) ∧
        rawSobolevNorm s ((V i).adjoint (toL2 s v)) ≤
          Craw i s * (‖v‖ + (1 + cNorm (Kin i) (s + 2 * (n + 1) + 14)
            (initial i)) * ‖toL2 s v‖)) →
      let Hhigh := fun s ↦ 1 + ∑ i,
        cNorm (Kin i) (s + 2 * (n + 1) + 14) (initial i)
      let A := augmentedRow (imageChannel coeff χ χsrc)
        (fun i ↦ CommonMeasurement.restrictCarrier χ (V i)) ψ
      (∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) s →
        A.adjoint w ∈ augmentedInputLevel n ι s ∧
        (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
          Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + Hhigh s * ‖w‖)) ∧
      ∀ s w, w ∈ periodicSobolevLevel n (Euclidean n) (s + 1) →
        let u := A.adjoint w
        ∃ hf : ∀ i, MemRawSobolev 1 (u.fst.snd i),
          (∀ i, MemPhysicalSobolev s (physicalComplexifyL2
            (densityUncut (z₀ i) (θ₀ i) (ha i) (hb i) (u.fst.snd i) (hf i))) ∧
            MemPhysicalSobolev s (physicalComplexifyL2
            (density (z₀ i) (θ₀ i) (ha i) (hb i) (χinitial i) (u.fst.snd i) (hf i)))) ∧
          densityUncutFamilySize z₀ θ₀ ha hb s u ≤
            Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + Hhigh (s + 1) * ‖w‖) ∧
          densityFamilySize z₀ θ₀ ha hb χinitial s u ≤
            Lbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm (s + 1) w + Hhigh (s + 1) * ‖w‖) := by
  classical
  obtain ⟨C, hC, hrow⟩ := exists_measured_retained_augmented_bounds H isCompact_empty 0
    Kin zero_le_one χ χsrc ψ hχ hχsrc hψ P hP Craw hCraw
  let B (s : ℕ) := 1 + cNorm (closedBall (0 : Euclidean n) 0) (s + 2 * (n + 1) + 14) H.map
  have hB (s : ℕ) : 1 ≤ B s := by
    dsimp [B]
    linarith [cNorm_nonneg (s := closedBall (0 : Euclidean n) 0)
      (s + 2 * (n + 1) + 14) H.map]
  let Cbound (s : ℕ) := C s * B s
  have hCbound (s : ℕ) : 0 ≤ Cbound s := mul_nonneg (hC s) (zero_le_one.trans (hB s))
  obtain ⟨L, hL, hdensity⟩ := exists_densityFamily_gradeNorm_bounds z₀ θ₀ ha hb χinitial
  refine ⟨Cbound, (fun s ↦ L s * Cbound (s + 1)), hCbound,
    (fun s ↦ mul_nonneg (hL s) (hCbound _)), ?_⟩
  intro coeff hcoeff hjets initial d V hrep hraw Hhigh A
  have hraw' := hrow H.map H.contDiff
    (by simp only [sub_self, cNorm_zero]; norm_num) coeff hcoeff
    (fun m j x ↦ (hjets m j x).trans (by
      have hp := hP m
      have hn := cNorm_nonneg (s := closedBall (0 : Euclidean n) 0) (m + 2) H.map
      nlinarith))
    initial d V hrep (by simpa only [cNorm_empty, add_zero] using hraw)
  have hgrade (s : ℕ) (w : OutputL2 n) (hw : w ∈ periodicSobolevLevel n (Euclidean n) s) :
      A.adjoint w ∈ augmentedInputLevel n ι s ∧
      (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
        Cbound s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + Hhigh s * ‖w‖) := by
    obtain ⟨hm, hbound⟩ := hraw' s w hw
    refine ⟨hm, ?_⟩
    let S := ∑ i, cNorm (Kin i) (s + 2 * (n + 1) + 14) (initial i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ cNorm_nonneg ..
    have hhigh : B s + S ≤ B s * Hhigh s := by
      change B s + S ≤ B s * (1 + S)
      nlinarith [le_mul_of_one_le_left hS (hB s)]
    have hh : (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint w) ≤
        C s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s w + (B s + S) * ‖w‖) := by
      simpa only [empty_union] using hbound
    apply hh.trans
    dsimp only [Cbound]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hC s)
    calc
      _ ≤ B s * (periodicSobolevScale n (Euclidean n)).gradeNorm s w +
          (B s * Hhigh s) * ‖w‖ :=
        add_le_add (le_mul_of_one_le_left
          ((periodicSobolevScale n (Euclidean n)).gradeNorm_nonneg s w) (hB s))
          (mul_le_mul_of_nonneg_right hhigh (norm_nonneg w))
      _ = _ := by ring
  refine ⟨hgrade, ?_⟩
  intro s w hw
  obtain ⟨hf, hmem, huncut, hcut⟩ := hdensity s _ (hgrade (s + 1) w hw).1
  refine ⟨hf, hmem, ?_, ?_⟩
  · exact (huncut.trans (mul_le_mul_of_nonneg_left (hgrade (s + 1) w hw).2 (hL s))).trans_eq
      (mul_assoc _ _ _).symm
  · exact (hcut.trans (mul_le_mul_of_nonneg_left (hgrade (s + 1) w hw).2 (hL s))).trans_eq
      (mul_assoc _ _ _).symm

end JanetCartan.ContinuumRow.NormalizedSelection
