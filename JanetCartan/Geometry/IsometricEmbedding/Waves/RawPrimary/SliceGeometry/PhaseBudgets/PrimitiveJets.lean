module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGeometry.Geometry

/-!
# Primitive phase jets on the actual slice domains

The covector differential in `app:ch_seed:eq:seed-quotient-integral` costs
one derivative of the SAME full phase. The fixed adapted coordinates cost
only a geometric constant. The consumer is the finite joint phase budget
for `UniformNormalData.input_jets` in `PhaseBudgets`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceGeometry
open ActualCarriers FrozenMenu CurrentFullPhase SliceBounds
open FullPhaseCharts.ActualPhase FullPhaseCharts.InverseEstimates

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

local notation "E" => Euclidean (n - 1)

private def basePhaseInclusion : ((ℝ × E) × E) →L[ℝ] (Euclidean n × E) :=
  ((NullTransport.ActualFlow.adaptedCoordinates T.data.adapted).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)

private theorem norm_basePhaseInclusion_le : ‖basePhaseInclusion T‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro q
  change max ‖adaptedPhysicalCoordinates T.data.adapted q.1‖ ‖q.2‖ ≤ 2 * ‖q‖
  have ht := (norm_fst_le q.1).trans (norm_fst_le q)
  have hy := (norm_snd_le q.1).trans (norm_fst_le q)
  have hη := norm_snd_le q
  have hp := norm_slicePhysicalCoordinates_le T q.1.1 q.1.2
  rw [Real.norm_eq_abs] at ht
  exact max_le (by linarith) (by linarith [norm_nonneg q])

/-- Joint covector-differential jets on the original slice chart use full
phase order `j+1`. Together with the sharp phase producer this is immersion
order `j+4`; the subsequent epsilon derivative makes it `k+5`
(`app:ch_seed:eq:seed-quotient-integral`, `app:ch_seed:eq:seed-phase-tame`). -/
theorem norm_iteratedFDeriv_canonicalBasePhase_covector_le (Q : _) (z : Euclidean 3)
    {a b : ℝ} (ha : 4 * a < T.family.radius)
    (hb : ball (T.reference.spatialPatch z) b ⊆
      ball (covectorCenter T) (min T.family.radius (3 * T.family.sourceRadius)))
    {q : (ℝ × E) × E}
    (hq : q ∈ sliceAdaptedDomain T a ×ˢ ball (T.reference.spatialPatch z) b) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun w : (ℝ × E) × E ↦
      fderiv ℝ (canonicalBasePhase T Q w.1) w.2) q‖ ≤
      2 ^ (j + 1) * cNorm (closedBall (0, covectorCenter T) T.family.radius) (j + 1)
        (Function.uncurry (LeadingWave.FullModulation.phase T Q)) := by
  let O := (adaptedPhysicalCoordinates T.data.adapted ⁻¹'
      ball 0 (2 * T.family.radius)) ×ˢ ball (covectorCenter T) (2 * T.family.radius)
  have hO : IsOpen O :=
    (isOpen_ball.preimage
      (NullTransport.ActualFlow.adaptedCoordinates T.data.adapted).symm.continuous).prod isOpen_ball
  have hq' : basePhaseInclusion T q ∈ ball (0, covectorCenter T) T.family.radius := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨ball_subset_ball ha.le hq.1,
      ball_subset_ball (min_le_left _ _) (hb hq.2)⟩
  have hqO : q ∈ O := by
    have hh := ball_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius ≤ 2 * T.family.radius) hq'
    change (adaptedPhysicalCoordinates T.data.adapted q.1, q.2) ∈
      ball (0, covectorCenter T) (2 * T.family.radius) at hh
    simpa only [O, mem_prod, mem_preimage, mem_ball, Prod.dist_eq, max_lt_iff] using hh
  let R := physicalDifferentialRestriction (P := ℝ × E) (X := E)
  have he : (fun w : (ℝ × E) × E ↦ fderiv ℝ (canonicalBasePhase T Q w.1) w.2)
      =ᶠ[𝓝 q] (R ∘ fderiv ℝ (Function.uncurry (canonicalBasePhase T Q))) := by
    filter_upwards [hO.mem_nhds hqO] with w hw
    exact (physicalDifferentialRestriction_fderiv
      (((canonicalBasePhase_smooth T Q).contDiffAt (hO.mem_nhds hw)).differentiableAt
        (by simp))).symm
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  have hd := ((canonicalBasePhase_smooth T Q).contDiffAt (hO.mem_nhds hqO)).fderiv_right
    (m := ∞) (by simp)
  have hfirst : ‖iteratedFDeriv ℝ j
      (R ∘ fderiv ℝ (Function.uncurry (canonicalBasePhase T Q))) q‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) (Function.uncurry (canonicalBasePhase T Q)) q‖ := by
    apply (R.norm_iteratedFDeriv_comp_left hd (by simp)).trans
    calc
      _ ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ (Function.uncurry (canonicalBasePhase T Q))) q‖ :=
        mul_le_mul_of_nonneg_right norm_physicalDifferentialRestriction_le (norm_nonneg _)
      _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]
  apply hfirst.trans
  have hball : closedBall ((0 : Euclidean n), covectorCenter T) T.family.radius ⊆
      ball (0, covectorCenter T) (2 * T.family.radius) :=
    closedBall_subset_ball (by linarith [T.family.radius_pos])
  have hlin := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    (basePhaseInclusion T) isOpen_ball (LeadingWave.FullModulation.phase_smooth T Q)
    (hball (ball_subset_closedBall hq')) (j + 1)
  change ‖iteratedFDeriv ℝ (j + 1)
    ((Function.uncurry (LeadingWave.FullModulation.phase T Q)) ∘ basePhaseInclusion T) q‖ ≤ _
  apply hlin.trans
  calc
    _ ≤ cNorm (closedBall (0, covectorCenter T) T.family.radius) (j + 1)
        (Function.uncurry (LeadingWave.FullModulation.phase T Q)) * 2 ^ (j + 1) := by
      apply mul_le_mul
      · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
          (fun w hw ↦ ((LeadingWave.FullModulation.phase_smooth T Q).contDiffAt
            (isOpen_ball.mem_nhds (hball hw))).of_le (by simp))
          (ball_subset_closedBall hq') le_rfl
      · exact pow_le_pow_left₀ (norm_nonneg _) (norm_basePhaseInclusion_le T) _
      · positivity
      · exact cNorm_nonneg _ _ _
    _ = _ := mul_comm _ _

end JanetCartan.RawPrimary.SliceGeometry
