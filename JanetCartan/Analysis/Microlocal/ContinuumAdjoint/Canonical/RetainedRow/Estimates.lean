module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.FiniteAdjoint
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AuxiliaryAdjoints
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.InputEstimates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Chart

/-!
# The retained operators on the common measurement chart

This is the finite deduction used by `exists_retained_row_initial_adjoint`.
Its complex raw bounds and representatives are precisely the outputs of
`LeadingCarrier.exists_covering_retained_forward_adjoint_row_before_geometry`.
No operator is selected here: common restriction, realification and augmentation
act on those same operators. The image arrays likewise remain unchanged.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-realification`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.Canonical
open ContinuumRow CarrierSobolev PeriodicSobolevSpace
open ContinuumCommutator.ImageChannel.Differential

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Apply the retained complex bounds to the SAME measured real row and its
actual image/exterior adjoints. Constants precede the current immersion,
original scalars, coefficient arrays, operators and datum. The input raw
estimate is the exact proved finite-row output, instantiated by
`exists_retained_row_initial_adjoint`; it is not a new geometric premise
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_measured_retained_augmented_bounds
    (G : FlatReference n) {K : Set (Euclidean n)} (hK : IsCompact K) (R : ℝ)
    (Kin : ι → Set (Euclidean (n-1) × Euclidean 3))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (χ χsrc ψ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (hχsrc : IsSmoothPeriodic χsrc) (hψ : IsSmoothPeriodic ψ)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m)
    (Craw : ι → ℕ → ℝ) (hCraw : ∀ i s, 0 ≤ Craw i s) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
    ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (_hF : ContDiff ℝ ∞ F),
      cNorm (closedBall 0 R) 8 (F - G.map) < δ →
    ∀ (coeff : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)),
      (∀ a, IsSmoothPeriodic (coeff a)) →
      (∀ m a x, ‖iteratedFDeriv ℝ m (periodicLift (coeff a)) x‖ ≤
        P m * (1 + cNorm (closedBall 0 R) (m+2) F)) →
    ∀ (initial : ι → Euclidean (n-1) × Euclidean 3 → ℝ)
      (d : ι → CarrierData n (embeddingDimension n))
      (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i w, (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) →
      (∀ i s, ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s ((V i).adjoint (toL2 s v)) ∧
        rawSobolevNorm s ((V i).adjoint (toL2 s v)) ≤
          Craw i s * (‖v‖ + (1 + cNorm K (s+2*(n+1)+14) F +
            cNorm (Kin i) (s+2*(n+1)+14) (initial i)) * ‖toL2 s v‖)) →
      let Vb := fun i ↦ CommonMeasurement.restrictCarrier χ (V i)
      let A := augmentedRow (imageChannel coeff χ χsrc) Vb ψ
      let H := fun m ↦ 1 + cNorm (K ∪ closedBall 0 R) m F +
        ∑ i, cNorm (Kin i) m (initial i)
      ∀ (s : ℕ) (v : OutputL2 n), v ∈ (periodicSobolevScale n (Euclidean n)).level s →
        A.adjoint v ∈ (augmentedInputSobolevScale n ι).level s ∧
        (augmentedInputSobolevScale n ι).gradeNorm s (A.adjoint v) ≤
          C s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s v +
            H (s+2*(n+1)+14) * ‖v‖) := by
  classical
  obtain ⟨Caux, hCaux, haux⟩ := AuxiliaryAdjoints.exists_auxiliaryAdjoints_reference_profile
    G R hδ χ χsrc ψ hχ hχsrc hψ P hP
  let Kcut (s : ℕ) := 1 + ‖cutoffSobolev χ hχ s‖ + ‖cutoffMultiplier (n := n) χ‖
  have hKcut (s : ℕ) : 0 ≤ Kcut s := by dsimp [Kcut]; positivity
  let Ccarrier (s : ℕ) := (∑ i, 2 * Craw i s) * Kcut s
  have hCcarrier (s : ℕ) : 0 ≤ Ccarrier s :=
    mul_nonneg (Finset.sum_nonneg fun i _ ↦ mul_nonneg (by norm_num) (hCraw i s)) (hKcut s)
  refine ⟨fun s ↦ Ccarrier s + Caux s,
    (fun s ↦ add_nonneg (hCcarrier s) (hCaux s).le), ?_⟩
  intro F hF hnear coeff hcoeff hjets initial d V hrep hraw Vb A H
  have hK' := hK.union (isCompact_closedBall (0 : Euclidean n) R)
  have hcarrierHigh (m : ℕ) : 1 + cNorm K m F +
      (∑ i, cNorm (Kin i) m (initial i)) ≤ H m :=
    add_le_add (add_le_add le_rfl
      (cNorm_mono_set subset_union_left hK' (hF.of_le (by simp)))) le_rfl
  have hauxHigh (s : ℕ) : 1 + cNorm (closedBall 0 R) (s+3) F ≤ H (s+2*(n+1)+14) := by
    have hset := cNorm_mono_set (f := F) (r := s+3) subset_union_right hK'
      (hF.of_le (by simp))
    have horder := cNorm_mono_order (f := F) (s := K ∪ closedBall 0 R)
      (by omega : s+3 ≤ s+2*(n+1)+14)
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦
      cNorm_nonneg (s := Kin i) (s+2*(n+1)+14) (initial i))
    dsimp only [H]
    linarith
  have hreal (i : ι) (s : ℕ) (v : PeriodicSobolevSpace n (Euclidean n) s) :=
    carrierChannel_adjoint_raw_bound (d i) (V i) (V i).adjoint (hrep i) (hrep i)
      (hCraw i s) (add_nonneg (add_nonneg zero_le_one (cNorm_nonneg ..))
        (cNorm_nonneg ..)) (hraw i s) v
  have hfamily (s : ℕ) (v : PeriodicSobolevSpace n (Euclidean n) s) :
      ∃ u : CarrierFamilySobolevSpace n ι s,
        carrierFamilyToL2 s u = (carrierRow Vb).adjoint (toL2 s v) ∧
        ‖u‖ ≤ Ccarrier s * (‖v‖ + H (s+2*(n+1)+14) * ‖toL2 s v‖) := by
    let w := cutoffSobolev χ hχ s v
    have heq (i : ι) : (carrierChannel (Vb i)).adjoint (toL2 s v) =
        (carrierChannel (V i)).adjoint (toL2 s w) := by
      rw [toL2_cutoffSobolev, CommonMeasurement.carrierChannel_restrictCarrier,
        ContinuousLinearMap.adjoint_comp, cutoffMultiplier_adjoint]
      rfl
    let u : CarrierFamilySobolevSpace n ι s := WithLp.toLp 2 (fun i ↦
      RawSobolevSpace.ofRawL2 s ((carrierChannel (V i)).adjoint (toL2 s w)) (hreal i s w).1)
    refine ⟨u, ?_, ?_⟩
    · rw [carrierRow_adjoint_apply]
      apply PiLp.ext
      intro i
      exact (RawSobolevSpace.toRawL2_ofRawL2 s _ _).trans (heq i).symm
    · have he (i : ι) : ‖u i‖ = rawSobolevNorm s
          ((carrierChannel (V i)).adjoint (toL2 s w)) := by
        rw [RawSobolevSpace.norm_eq, RawSobolevSpace.toRawL2_ofRawL2]
      have hb := sum_single_high_bound
        (fun i ↦ rawSobolevNorm s ((carrierChannel (V i)).adjoint (toL2 s w)))
        (fun i ↦ 2 * Craw i s) (fun i ↦ cNorm (Kin i) (s+2*(n+1)+14) (initial i))
        ‖w‖ ‖toL2 s w‖ (cNorm K (s+2*(n+1)+14) F)
        (fun i ↦ mul_nonneg (by norm_num) (hCraw i s)) (fun _ ↦ cNorm_nonneg ..)
        (norm_nonneg _) (fun i ↦ (hreal i s w).2)
      have hw : ‖w‖ ≤ Kcut s * ‖v‖ :=
        ((cutoffSobolev χ hχ s).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right
            (by dsimp [Kcut]; linarith [norm_nonneg (cutoffMultiplier (n := n) χ)])
            (norm_nonneg v))
      have hw₀ : ‖toL2 s w‖ ≤ Kcut s * ‖toL2 s v‖ := by
        rw [toL2_cutoffSobolev]
        exact ((cutoffMultiplier χ).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right
            (by dsimp [Kcut]; linarith [norm_nonneg (cutoffSobolev χ hχ s)]) (norm_nonneg _))
      have hH : 0 ≤ H (s+2*(n+1)+14) :=
        add_nonneg (add_nonneg zero_le_one (cNorm_nonneg ..))
          (Finset.sum_nonneg fun _ _ ↦ cNorm_nonneg ..)
      have hsumC : 0 ≤ ∑ i, 2 * Craw i s :=
        Finset.sum_nonneg fun i _ ↦ mul_nonneg (by norm_num) (hCraw i s)
      calc
        ‖u‖ ≤ ∑ i, ‖u i‖ := carrierFamily_norm_le_sum s u
        _ = _ := Finset.sum_congr rfl (fun i _ ↦ he i)
        _ ≤ _ := hb
        _ ≤ (∑ i, 2 * Craw i s) * (‖w‖ + H (s+2*(n+1)+14) * ‖toL2 s w‖) := by
          gcongr
          exact hcarrierHigh _
        _ ≤ (∑ i, 2 * Craw i s) * (Kcut s * ‖v‖ +
            H (s+2*(n+1)+14) * (Kcut s * ‖toL2 s v‖)) := by gcongr
        _ = _ := by dsimp [Ccarrier]; ring
  intro s
  have hnorm (v : PeriodicSobolevSpace n (Euclidean n) s) :
      ‖v‖ = (periodicSobolevScale n (Euclidean n)).gradeNorm s (toL2 s v) := by
    have he : inclusion (Nat.le_refl s) v = v := by
      apply toL2_injective s
      exact multiplier_toL2_inclusion _ _
    simpa only [he] using multiplier_norm_inclusion_eq_gradeNorm (Nat.le_refl s) v
  apply augmentedAdjoint_gradeNorm_of_lifts A s (Ccarrier s + Caux s) (H (s+2*(n+1)+14))
  intro v
  obtain ⟨uc, huc, hbc⟩ := hfamily s v
  obtain ⟨hvi, hve, hba⟩ := haux F hF hnear coeff hcoeff hjets s (toL2 s v) (toL2_mem s v)
  let vi := ofL2 s ((imageChannel coeff χ χsrc).adjoint (toL2 s v)) hvi
  let ve := ofL2 s ((exteriorChannel ψ).adjoint (toL2 s v)) hve
  let u : AugmentedInputSobolevSpace n ι s := WithLp.toLp 2 (WithLp.toLp 2 (vi, uc), ve)
  have hui : toL2 s vi = (imageChannel coeff χ χsrc).adjoint (toL2 s v) := toL2_ofL2 ..
  have hue : toL2 s ve = (exteriorChannel ψ).adjoint (toL2 s v) := toL2_ofL2 ..
  have hba' : ‖vi‖ + ‖ve‖ ≤ Caux s * (‖v‖ + H (s+2*(n+1)+14) * ‖toL2 s v‖) := by
    rw [hnorm vi, hnorm ve, hui, hue, hnorm v]
    exact hba.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hauxHigh s) (norm_nonneg _))) (hCaux s).le)
  refine ⟨u, ?_, ?_⟩
  · change augmentedInputToL2 s u = (augmentedRow (imageChannel coeff χ χsrc) Vb ψ).adjoint _
    rw [augmentedInputToL2_apply, physicalInputToL2_apply,
      augmentedRow_adjoint_apply, physicalRow_adjoint_apply]
    change WithLp.toLp 2 (WithLp.toLp 2 (toL2 s vi, carrierFamilyToL2 s uc), toL2 s ve) = _
    rw [hui, hue, huc, exteriorChannel_adjoint]
  · have hsq : ‖u‖^2 = ‖vi‖^2 + ‖uc‖^2 + ‖ve‖^2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
      rfl
    have hnorm : ‖u‖ ≤ ‖vi‖ + ‖ve‖ + ‖uc‖ := by
      nlinarith [norm_nonneg u, norm_nonneg vi, norm_nonneg ve, norm_nonneg uc,
        mul_nonneg (norm_nonneg vi) (norm_nonneg ve),
        mul_nonneg (norm_nonneg vi) (norm_nonneg uc),
        mul_nonneg (norm_nonneg ve) (norm_nonneg uc)]
    calc
      _ ≤ ‖vi‖ + ‖ve‖ + ‖uc‖ := hnorm
      _ ≤ Caux s * (‖v‖ + H (s+2*(n+1)+14) * ‖toL2 s v‖) +
          Ccarrier s * (‖v‖ + H (s+2*(n+1)+14) * ‖toL2 s v‖) := add_le_add hba' hbc
      _ = _ := by ring

end JanetCartan.ContinuumAdjoint.Canonical
