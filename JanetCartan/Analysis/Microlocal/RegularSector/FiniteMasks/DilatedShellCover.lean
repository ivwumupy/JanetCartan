module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ShellCover
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.NestedBounds

/-!
# Normalized covers for the actual common radial collar

`exists_finite_nested_spatial_conicMasks` enlarges the right multiplier's
radial threshold. This file constructs the normalized cover and all its
multiplier budgets for that SAME dilation. Its scale is exactly `1 + ‖ξ‖`,
so both inequalities in the signed retarded constructor hold with constant
one. All supports include the cutoff shoulders.
Source: `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
open Set Metric Function
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteMasks
open CompatibleResponse FourierIntegral.PrimitiveProfiles
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => (Euclidean (d + 1) × Euclidean (d + 1)) × Euclidean (d + 1)

/-- The actual enlarged collar keeps the original angular closed support and
excludes every covector of norm below its fixed threshold (`retarded-kernel`). -/
theorem dilatedConicMask_tsupport_subset (a : E → ℝ) {L : ℝ} (hL : 0 < L) :
    tsupport (dilatedConicMask a L) ⊆
      {ξ | L ≤ ‖ξ‖ ∧ NormedSpace.normalize ξ ∈ tsupport a} := by
  intro ξ hξ
  have hs := conicMask_tsupport_subset a
    (tsupport_comp_subset_preimage (conicMask a) (continuous_id.const_smul L⁻¹) hξ)
  change 1 ≤ ‖L⁻¹ • ξ‖ ∧ NormedSpace.normalize (L⁻¹ • ξ) ∈ tsupport a at hs
  constructor
  · have h := mul_le_mul_of_nonneg_left hs.1 hL.le
    simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL.le),
      mul_one, ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] using h
  · simpa only [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hL)] using hs.2

/-- The same compact angular annulus covers the actual multiplier after the
common radial dilation. This closes normalization without changing masks. -/
theorem mem_normalizedMaskCarrier_of_dilatedConicMask {X : Set (E × E)}
    (a : E → ℝ) {L : ℝ} (hL : 1 ≤ L) {p : P}
    (hp : p ∈ X ×ˢ tsupport (dilatedConicMask a L)) :
    (p.1, (1 + ‖p.2‖)⁻¹ • p.2) ∈ normalizedMaskCarrier X a := by
  have hs := dilatedConicMask_tsupport_subset a (zero_lt_one.trans_le hL) hp.2
  have hn : p.2 ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le (hL.trans hs.1))
  have hr : 0 < 1 + ‖p.2‖ := by positivity
  refine ⟨hp.1, ⟨(‖p.2‖ / (1 + ‖p.2‖), NormedSpace.normalize p.2), ?_, ?_⟩⟩
  · refine ⟨⟨?_, ?_⟩, hs.2, ?_⟩
    · apply (le_div_iff₀ hr).mpr
      have := hL.trans hs.1
      linarith
    · exact (div_le_one hr).mpr (by linarith)
    · simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hn
  · dsimp
    rw [div_eq_inv_mul, mul_smul, NormedSpace.norm_smul_normalize]

/-- Construct the finite shell cover required by
`exists_retardedOperator_signed_integer_bounds_of_primitive_data`, for the
literal dilated right multiplier. The exact normalization also supplies its
upper-scale condition with constant one. The same balls and budgets work at
every derivative order and every larger radial threshold. -/
theorem exists_finite_dilatedConicMask_shell_cover
    {X : Set (E × E)} (hX : IsCompact X) {a : E → ℝ} (ha : ContDiff ℝ ∞ a)
    {U : Set P} (hU : IsOpen U) (hKU : normalizedMaskCarrier X a ⊆ U) :
    ∃ (s : Finset (normalizedMaskCarrier X a))
      (ρ : normalizedMaskCarrier X a → ℝ),
      (∀ p, 0 < ρ p) ∧
      (∀ p ∈ s, closedBall (p : P) (ρ p) ⊆ U) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ p ∈ s, ∀ m,
        BoundedNormalizedSeminorm (closedBall (p : P) (ρ p)) m
          (fun z : P ↦ (dilatedConicMask a L z.2 : ℂ))) ∧
      ∀ L : ℝ, 1 ≤ L →
        ∀ p ∈ X ×ˢ tsupport (fun ξ ↦ (dilatedConicMask a L ξ : ℂ)),
          ∃ q ∈ s, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ closedBall (q : P) (ρ q),
            p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R ∧ R ≤ 1 * (1 + ‖p.2‖) := by
  classical
  let K := normalizedMaskCarrier X a
  let V : Set P := U ∩ {p | p.2 ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_ne.preimage continuous_snd)
  have hKV : K ⊆ V := fun p hp ↦
    ⟨hKU hp, normalizedMaskCarrier_frequency_ne_zero X a hp⟩
  have hball (p : K) : ∃ r > (0 : ℝ), closedBall (p : P) r ⊆ V := by
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hV p (hKV p.property)
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (by linarith : r / 2 < r)).trans hb⟩
  choose ρ hρ hρV using hball
  obtain ⟨s, hs⟩ := (isCompact_normalizedMaskCarrier hX a).elim_finite_subcover
    (fun p : K ↦ ball (p : P) (ρ p)) (fun _ ↦ isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (hρ ⟨p, hp⟩)⟩)
  refine ⟨s, ρ, hρ, fun p _ z hz ↦ (hρV p hz).1, ?_, ?_⟩
  · intro L hL p _ m
    exact boundedNormalizedSeminorm_dilatedConicMask ha hL (isCompact_closedBall _ _)
      (fun z hz ↦ (hρV p hz).2) m
  · intro L hL p hp
    have hv := mem_normalizedMaskCarrier_of_dilatedConicMask a hL
      ⟨hp.1, tsupport_comp_subset Complex.ofReal_zero (dilatedConicMask a L) hp.2⟩
    obtain ⟨q, hq, hvq⟩ := mem_iUnion₂.mp (hs hv)
    refine ⟨q, hq, 1 + ‖p.2‖, by linarith [norm_nonneg p.2],
      (p.1, (1 + ‖p.2‖)⁻¹ • p.2), ball_subset_closedBall hvq, ?_, le_rfl, ?_⟩
    · simp only [smul_inv_smul₀ (by positivity : (1 + ‖p.2‖) ≠ 0)]
    · simp only [one_mul, le_refl]

end JanetCartan.RegularSector.FiniteMasks
