module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers.SmoothBounds

/-!
# Sobolev actions of the actual scalar image multipliers

Smooth density constructs the action, and continuity of the existing L²
multiplier identifies it. The complementary derivative allocation survives
completion for `app:ch_background:eq:bg-commutator`.
-/

public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open PeriodicSobolevSpace ContinuumRow

variable {n : ℕ}

private theorem smooth_sub (f g : Torus n → Euclidean n)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    IsSmoothPeriodic (f - g) := ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

private theorem ofSmooth_sub (s : ℕ) (f g : Torus n → Euclidean n)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    ofSmooth s (f - g) (smooth_sub f g hf hg) = ofSmooth s f hf - ofSmooth s g hg := by
  apply toL2_injective s
  rw [map_sub]
  apply Lp.ext
  exact (toL2_ofSmooth_ae s _ _).trans
    (((toL2_ofSmooth_ae s f hf).sub (toL2_ofSmooth_ae s g hg)).symm.trans
      (Lp.coeFn_sub _ _).symm)

private theorem dist_ofSmooth_cutoff_le (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (f g : Torus n → Euclidean n)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    dist (ofSmooth s (fun x ↦ q x • f x) (Exterior.smooth_smul hq hf))
      (ofSmooth s (fun x ↦ q x • g x) (Exterior.smooth_smul hq hg)) ≤
      (AuxiliaryRawBand.coefficientProductConstant n s * (s + 1) *
        cNorm (fundamentalCell n) s (periodicLift q)) *
          dist (ofSmooth s f hf) (ofSmooth s g hg) := by
  have h := norm_ofSmooth_cutoff_le_top q hq s (f - g) (smooth_sub f g hf hg)
  have he : (fun x ↦ q x • (f - g) x) =
      (fun x ↦ q x • f x) - (fun x ↦ q x • g x) := by
    funext x
    exact smul_sub _ _ _
  simpa only [he, ofSmooth_sub s _ _ (Exterior.smooth_smul hq hf) (Exterior.smooth_smul hq hg),
    ofSmooth_sub s f g hf hg, dist_eq_norm] using h

private theorem exists_cutoffSobolev (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ∃ v : PeriodicSobolevSpace n (Euclidean n) s,
      toL2 s v = cutoffMultiplier q (toL2 s u) ∧
        ‖v‖ ≤ (AuxiliaryRawBand.coefficientProductConstant n s * (s + 1) *
          cNorm (fundamentalCell n) s (periodicLift q)) * ‖u‖ := by
  let C := AuxiliaryRawBand.coefficientProductConstant n s * (s + 1) *
    cNorm (fundamentalCell n) s (periodicLift q)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (AuxiliaryRawBand.coefficientProductConstant_nonneg n s) (by positivity))
      (cNorm_nonneg _ _ _)
  let f (j : ℕ) := periodicCutoff (j + 1) (toL2 s u)
  have hf (j : ℕ) : IsSmoothPeriodic (f j) := isSmoothPeriodic_periodicCutoff _ _
  let v (j : ℕ) := ofSmooth s (fun x ↦ q x • f j x) (Exterior.smooth_smul hq (hf j))
  have hu := tendsto_smoothApproximation s u
  have hc : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq
      (ε / (C + 1)) (div_pos hε (by linarith))
    refine ⟨N, fun j hj k hk ↦ ?_⟩
    have hdist := dist_ofSmooth_cutoff_le q hq s (f j) (f k) (hf j) (hf k)
    have hlt := (lt_div_iff₀ (show 0 < C + 1 by linarith)).mp (hN j hj k hk)
    change dist (v j) (v k) ≤ C * dist (smoothApproximation s u j)
      (smoothApproximation s u k) at hdist
    nlinarith [show 0 ≤ dist (smoothApproximation s u j) (smoothApproximation s u k) from dist_nonneg]
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨w, ?_, ?_⟩
  · have hL := ((cutoffMultiplier q).continuous.tendsto (toL2 s u)).comp
      (((toL2 s).continuous.tendsto u).comp hu)
    change Tendsto (fun j ↦ cutoffMultiplier q (toL2 s (ofSmooth s (f j) (hf j))))
      atTop (𝓝 (cutoffMultiplier q (toL2 s u))) at hL
    simp_rw [cutoffMultiplier_ofSmooth q hq s s] at hL
    exact tendsto_nhds_unique (((toL2 s).continuous.tendsto w).comp hw) hL
  · exact le_of_tendsto_of_tendsto' hw.norm (tendsto_const_nhds.mul hu.norm)
      (fun j ↦ norm_ofSmooth_cutoff_le_top q hq s (f j) (hf j))

private def cutoffSobolevLinear (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q) (s : ℕ) :
    PeriodicSobolevSpace n (Euclidean n) s →ₗ[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s where
  toFun u := (exists_cutoffSobolev q hq s u).choose
  map_add' u v := by
    apply toL2_injective s
    rw [(exists_cutoffSobolev q hq s (u + v)).choose_spec.1, map_add, map_add,
      map_add, (exists_cutoffSobolev q hq s u).choose_spec.1,
      (exists_cutoffSobolev q hq s v).choose_spec.1]
  map_smul' c u := by
    apply toL2_injective s
    rw [(exists_cutoffSobolev q hq s (c • u)).choose_spec.1, map_smul, map_smul,
      map_smul, (exists_cutoffSobolev q hq s u).choose_spec.1]
    rfl

/-- The actual cutoff multiplier acting on every integer Sobolev space.
Its construction uses the proved smooth product estimate and completeness
(`app:ch_background:prop:bg-inverse`). -/
def cutoffSobolev (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q) (s : ℕ) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s :=
  (cutoffSobolevLinear q hq s).mkContinuous
    (AuxiliaryRawBand.coefficientProductConstant n s * (s + 1) *
      cNorm (fundamentalCell n) s (periodicLift q))
    (fun u ↦ (exists_cutoffSobolev q hq s u).choose_spec.2)

/-- The action is a restriction of the existing L² multiplier, with no change
of representatives or measure (`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem toL2_cutoffSobolev (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (cutoffSobolev q hq s u) = cutoffMultiplier q (toL2 s u) :=
  (exists_cutoffSobolev q hq s u).choose_spec.1

/-- Smooth agreement for the constructed Sobolev multiplier
(`app:ch_background:eq:bg-commutator`). -/
@[simp] theorem cutoffSobolev_ofSmooth (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f) :
    cutoffSobolev q hq s (ofSmooth s f hf) =
      ofSmooth s (fun x ↦ q x • f x) (Exterior.smooth_smul hq hf) := by
  apply toL2_injective s
  rw [toL2_cutoffSobolev, cutoffMultiplier_ofSmooth q hq s s]

/-- Compatibility with every lower Sobolev inclusion, needed when derivatives
are distributed among image factors (`app:ch_background:eq:bg-commutator`). -/
theorem inclusion_cutoffSobolev (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    {s t : ℕ} (h : s ≤ t) (u : PeriodicSobolevSpace n (Euclidean n) t) :
    inclusion h (cutoffSobolev q hq t u) = cutoffSobolev q hq s (inclusion h u) := by
  apply toL2_injective s
  rw [multiplier_toL2_inclusion, toL2_cutoffSobolev, toL2_cutoffSobolev,
    multiplier_toL2_inclusion]

/-- The finite product estimate for every Sobolev datum retains the allocation
`j` on the coefficient and `s-j` on the datum. The constant is the existing
explicit dimension/order constant (`app:ch_background:eq:bg-commutator`). -/
theorem norm_cutoffSobolev_le (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖cutoffSobolev q hq s u‖ ≤ AuxiliaryRawBand.coefficientProductConstant n s *
      ∑ j ∈ Finset.range (s + 1), cNorm (fundamentalCell n) j (periodicLift q) *
        ‖inclusion (Nat.sub_le s j) u‖ := by
  refine (denseRange_ofSmooth (n := n) (F := Euclidean n) s).induction_on u ?_ ?_
  · exact isClosed_le (cutoffSobolev q hq s).continuous.norm
      (continuous_const.mul (continuous_finsetSum _ (fun j _ ↦
        continuous_const.mul (inclusion (Nat.sub_le s j)).continuous.norm)))
  · rintro ⟨f, hf⟩
    simpa only [cutoffSobolev_ofSmooth, multiplier_inclusion_ofSmooth] using
      norm_ofSmooth_cutoff_le q hq s f hf

/-- The lower Sobolev norm in the product estimate is exactly the original
scale's grade norm of the same L² datum (`app:ch_background:prop:bg-inverse`). -/
theorem multiplier_norm_inclusion_eq_gradeNorm {s t : ℕ} (h : s ≤ t)
    (u : PeriodicSobolevSpace n (Euclidean n) t) :
    ‖inclusion h u‖ = (periodicSobolevScale n (Euclidean n)).gradeNorm s (toL2 t u) := by
  rw [(periodicSobolevScale n (Euclidean n)).gradeNorm_eq
    (antitone_periodicSobolevLevel h (toL2_mem t u))]
  rfl

/-- The coefficient-jet/lower-grade estimate in the form consumed by the
single-high image-normal estimate (`app:ch_background:eq:bg-commutator`). -/
theorem norm_cutoffSobolev_le_gradeNorm (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖cutoffSobolev q hq s u‖ ≤ AuxiliaryRawBand.coefficientProductConstant n s *
      ∑ j ∈ Finset.range (s + 1), cNorm (fundamentalCell n) j (periodicLift q) *
        (periodicSobolevScale n (Euclidean n)).gradeNorm (s-j) (toL2 s u) := by
  simpa only [multiplier_norm_inclusion_eq_gradeNorm] using norm_cutoffSobolev_le q hq s u

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
