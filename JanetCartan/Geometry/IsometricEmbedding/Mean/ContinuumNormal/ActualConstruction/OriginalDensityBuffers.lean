module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.SourceCoefficients

/-!
# Physical radius from the original density time buffer

The initialized density cover imposes its time restriction before selecting
incidence masks. Testing the complete coefficient product along the adapted
unit normal gives the radius bound used by the source and history constructions.
The coefficient product and all detector supports remain unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open NullTransport ActualFlow FlowAmplitude
open CarrierVariation.FamilyInputs.PositiveReference

/-- The time restriction produced before mask selection bounds the physical
radius of every retained coefficient product, with no change to its masks
(`app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-normalized`).
Producer: `exists_initialized_retained_comparison_carriers_with_original_density_geometry`.
Consumer: `exists_preliminary_cap_for_retained_incidence_coercivity` and the
realized history construction on that same source row. -/
theorem retained_coefficientDomain_radius_le_of_time_bound
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {zRoot : Euclidean 3} {r a L Mc : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hL : 0 < L) (hMc : 0 < Mc)
    {E : Set (Euclidean n × CarrierParameter)}
    (houter : coefficientDomain zRoot r a ⊆ E)
    (htime : ∀ p ∈ E, |(densityCoordinates T p).1| < L / (64 * Mc)) :
    a ≤ L / (64 * Mc) := by
  let b := L / (64 * Mc)
  have hb : 0 < b := div_pos hL (by positivity)
  by_contra h
  have hba : b < a := lt_of_not_ge h
  let t := (a + b) / 2
  have ht : 0 < t := by dsimp only [t]; positivity
  have hta : t < a := by dsimp only [t]; linarith
  have hbt : b < t := by dsimp only [t]; linarith
  have hx : t • T.data.adapted.normal ∈ ball (0 : Euclidean n) a := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      T.data.adapted.normal_unit, mul_one]
    exact hta
  have hp := houter (show (t • T.data.adapted.normal, (zRoot 0, spectatorCenter zRoot)) ∈
      coefficientDomain zRoot r a from ⟨hx, mem_ball_self hr, mem_ball_self ha⟩)
  have hbound := htime _ hp
  change |(adaptedCoordinates T.data.adapted (t • T.data.adapted.normal)).1| < b at hbound
  rw [adaptedCoordinates_apply] at hbound
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, T.data.adapted.normal_unit,
    one_pow, mul_one, abs_of_pos ht] at hbound
  exact (not_lt_of_ge hbt.le) hbound

end JanetCartan.ContinuumNormal.ActualConstruction
