module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Gap.Stability
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.FrozenIncidence.Transversality

/-!
# A fixed product cutoff with a small frozen spatial correction

The physical cutoff is chosen first. Its spatial derivative bound determines
how far to shrink the carrier cutoff, using continuity of the actual frozen
velocity. This supplies the frozen input to
`transverseGap_affineExtension_of_comparison`, independently of the current
frame, in `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual frozen velocity is continuous inside the retained carrier
chart. This supplies the shrinking step in `exists_frozen_affineExtension_cutoff`
(`app:ch_background:eq:bg-derivative-trade`). -/
private theorem frozenVelocity_continuousAt {c C : ℝ} (hP : P.IsValid c C)
    {z : CarrierParameter}
    (hz : CanonicalCarrier.parameter z ∈ parameterInterior (3 * P.radius / 2)) :
    ContinuousAt (frozenVelocity T) z := by
  have hz' : CanonicalCarrier.parameter z ∈ parameterInterior (2 * P.radius) := by
    intro i
    exact (hz i).trans (by linarith [hP.1])
  exact ((FrozenIncidence.patch_gradient_smooth T hP).contDiffAt
    ((isOpen_parameterInterior _).mem_nhds hz')).continuousAt.comp
      CanonicalCarrier.parameter.continuous.continuousAt

/-- The spatial error for `exists_frozen_affineExtension_cutoff` is controlled
by velocity variation times `1 + M * R`, retaining the cutoff derivative
(`app:ch_background:eq:bg-derivative-trade`). -/
private theorem norm_fderiv_frozen_extension_le
    {z₀ z : CarrierParameter} {χ : Euclidean n × CarrierParameter → ℝ}
    {x : Euclidean n} {M R ε : ℝ}
    (hχ : DifferentiableAt ℝ (fun y ↦ χ (y, z)) x)
    (hrange : |χ (x, z)| ≤ 1)
    (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hderiv : ‖fderiv ℝ (fun y ↦ χ (y, z)) x‖ ≤ M)
    (hx : ‖x‖ ≤ R) (hvel : ‖frozenVelocity T z - frozenVelocity T z₀‖ ≤ ε) :
    ‖fderiv ℝ (fun y ↦ affineExtension (frozenSpatialReference T z₀) χ
        (fun p ↦ frozenSpatialReference T p.2 p.1) (y, z)) x -
      frozenSpatialReference T z₀‖ ≤ (1 + M * R) * ε := by
  let A := frozenSpatialReference T z₀
  let B := frozenSpatialReference T z
  have hAB : ‖B - A‖ ≤ ε := (norm_frozenSpatialReference_sub_le T z z₀).trans hvel
  have hv : ‖B x - A x‖ ≤ ε * R := by
    calc
      _ = ‖(B - A) x‖ := rfl
      _ ≤ ‖B - A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * R := mul_le_mul hAB hx (norm_nonneg _) hε
  rw [fderiv_affineExtension _ hχ (frozenSpatialReference T z).differentiableAt]
  change ‖A + χ (x, z) • (fderiv ℝ B x - A) +
    (fderiv ℝ (fun y ↦ χ (y, z)) x).smulRight (B x - A x) - A‖ ≤ _
  rw [ContinuousLinearMap.fderiv, add_assoc, add_sub_cancel_left]
  calc
    _ ≤ ‖χ (x, z) • (B - A)‖ +
        ‖(fderiv ℝ (fun y ↦ χ (y, z)) x).smulRight (B x - A x)‖ := norm_add_le _ _
    _ = |χ (x, z)| * ‖B - A‖ +
        ‖fderiv ℝ (fun y ↦ χ (y, z)) x‖ * ‖B x - A x‖ := by
      rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ 1 * ε + M * (ε * R) := add_le_add
      (mul_le_mul hrange hAB (norm_nonneg _) zero_le_one)
      (mul_le_mul hderiv hv (norm_nonneg _) hM)
    _ = (1 + M * R) * ε := by ring

/-- A fixed product cutoff whose frozen affine extension has spatial derivative
within `1/4` of the frozen reference at the carrier center, everywhere. The
physical factor and its derivative bound are fixed before the carrier buffer
is shrunk. This supplies the frozen hypothesis of
`transverseGap_affineExtension_of_comparison` from the actual patch data,
without any current frame (`app:ch_background:eq:bg-derivative-trade`). -/
theorem exists_frozen_affineExtension_cutoff {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {r cap : ℝ} (hr : 0 < r) (hcap : 0 < cap)
    (hcarrier : closedBall (ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ (a : ℝ) (χ : Euclidean n × CarrierParameter → ℝ) (M : ℝ),
      0 < a ∧ a ≤ r ∧ a < cap ∧ 4 * a < T.physicalRadius ∧
      ContDiff ℝ ∞ χ ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ extensionDomain T ∧
      supportedChart z₀ a ⊆ interior {p | χ p = 1} ∧ 0 < M ∧
      (∀ p ∈ tsupport χ, ‖fderiv ℝ (fun y ↦ χ (y, p.2)) p.1‖ ≤ M) ∧
      ∀ x z,
        ‖fderiv ℝ (fun y ↦ affineExtension
            (frozenSpatialReference T (z₀ 0, ActualComparison.spectatorCenter z₀)) χ
            (fun p ↦ frozenSpatialReference T p.2 p.1) (y, z)) x -
          frozenSpatialReference T (z₀ 0, ActualComparison.spectatorCenter z₀)‖ ≤ 1 / 4 := by
  let R := T.physicalRadius
  have hR : 0 < R := T.physicalRadius_pos
  obtain ⟨β, hβ, hβrange, hβc, hβsupp, hβone⟩ :=
    CompatibleResponse.exists_compact_family_cutoff
      (isCompact_closedBall (0 : Euclidean n) (R / 2)) isOpen_ball
      (closedBall_subset_ball (by linarith : R / 2 < R))
  obtain ⟨B, hB⟩ := hβc.isCompact.exists_bound_of_continuousOn
    (hβ.continuous_fderiv (by simp)).continuousOn
  let M := max 1 B
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hβderiv : ∀ x ∈ tsupport β, ‖fderiv ℝ β x‖ ≤ M :=
    fun x hx ↦ (hB x hx).trans (le_max_right _ _)
  let ε := (1 / 4 : ℝ) / (1 + M * R)
  have hden : 0 < 1 + M * R := by positivity
  have hε : 0 < ε := div_pos (by norm_num) hden
  have hbudget : (1 + M * R) * ε = 1 / 4 := mul_div_cancel₀ _ hden.ne'
  let zc : CarrierParameter := (z₀ 0, ActualComparison.spectatorCenter z₀)
  have hzc : CanonicalCarrier.parameter zc ∈ parameterInterior (3 * P.radius / 2) :=
    hcarrier ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩
  obtain ⟨δ, hδ, hδvel⟩ := Metric.continuousAt_iff.mp
    (frozenVelocity_continuousAt T hP hzc) ε hε
  let ρ := min δ (3 * r)
  have hρ : 0 < ρ := lt_min hδ (by positivity)
  have hρvel : ∀ z ∈ ball zc ρ, ‖frozenVelocity T z - frozenVelocity T zc‖ ≤ ε := by
    intro z hz
    exact (hδvel (lt_of_lt_of_le hz (min_le_left _ _))).le
  have hρcarrier : ball zc ρ ⊆
      CanonicalCarrier.parameter ⁻¹' parameterInterior (3 * P.radius / 2) := by
    intro z hz
    have hz' : dist z zc ≤ 3 * r := (le_of_lt hz).trans (min_le_right _ _)
    rw [Prod.dist_eq, max_le_iff] at hz'
    exact hcarrier ⟨hz'.2, hz'.1⟩
  obtain ⟨γ, hγ, hγrange, hγc, hγsupp, hγone⟩ :=
    CompatibleResponse.exists_compact_family_cutoff
      (isCompact_closedBall zc (ρ / 2)) isOpen_ball
      (closedBall_subset_ball (by linarith : ρ / 2 < ρ))
  obtain ⟨a, ha, haall⟩ := exists_between
    (lt_min (lt_min hr hcap) (lt_min (div_pos hR (by norm_num : (0 : ℝ) < 8)) hρ))
  obtain ⟨⟨har, hacap⟩, haR, haρ⟩ := lt_min_iff.mp haall |>.imp lt_min_iff.mp lt_min_iff.mp
  let χ : Euclidean n × CarrierParameter → ℝ := fun p ↦ β p.1 * γ p.2
  have hχ : ContDiff ℝ ∞ χ := (hβ.comp contDiff_fst).mul (hγ.comp contDiff_snd)
  have hχrange : ∀ p, χ p ∈ Icc (0 : ℝ) 1 := by
    intro p
    exact ⟨mul_nonneg (hβrange p.1).1 (hγrange p.2).1,
      (mul_le_mul (hβrange p.1).2 (hγrange p.2).2 (hγrange p.2).1 zero_le_one).trans_eq
        (mul_one 1)⟩
  have hsprod : tsupport χ ⊆ tsupport β ×ˢ tsupport γ := by
    intro p hp
    exact ⟨tsupport_comp_subset_preimage β continuous_fst (tsupport_mul_subset_left hp),
      tsupport_comp_subset_preimage γ continuous_snd (tsupport_mul_subset_right hp)⟩
  have hχderiv : ∀ p ∈ tsupport χ, ‖fderiv ℝ (fun y ↦ χ (y, p.2)) p.1‖ ≤ M := by
    intro p hp
    have he : fderiv ℝ (fun y ↦ χ (y, p.2)) p.1 = γ p.2 • fderiv ℝ β p.1 := by
      simpa only [χ] using
        ((hβ.differentiable (by simp) p.1).hasFDerivAt.mul_const (γ p.2)).fderiv
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hγrange p.2).1]
    exact (mul_le_mul (hγrange p.2).2 (hβderiv p.1 (hsprod hp).1)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
  refine ⟨a, χ, M, ha, har.le, hacap, by dsimp [R] at haR; linarith,
    hχ, hχrange, ?_, ?_, ?_, hM, hχderiv, ?_⟩
  · exact (hβc.isCompact.prod hγc.isCompact).of_isClosed_subset (isClosed_tsupport χ) hsprod
  · intro p hp
    exact ⟨hβsupp (hsprod hp).1, hρcarrier (hγsupp (hsprod hp).2)⟩
  · intro p hp
    have hx : p.1 ∈ interior {x | β x = 1} :=
      hβone (closedBall_subset_closedBall (by linarith : 4 * a ≤ R / 2) hp.1)
    have hz : p.2 ∈ interior {z | γ z = 1} := by
      apply hγone
      rw [mem_closedBall, Prod.dist_eq]
      exact max_le ((hp.2.1).trans (by linarith)) ((hp.2.2).trans (by linarith))
    have hi : interior {x | β x = 1} ×ˢ interior {z | γ z = 1} ⊆
        interior {p | χ p = 1} := by
      apply interior_maximal _ (isOpen_interior.prod isOpen_interior)
      intro q hq
      change β q.1 * γ q.2 = 1
      rw [show β q.1 = 1 from interior_subset (s := {x | β x = 1}) hq.1,
        show γ q.2 = 1 from interior_subset (s := {z | γ z = 1}) hq.2, mul_one]
    exact hi ⟨hx, hz⟩
  · intro x z
    by_cases hp : (x, z) ∈ tsupport χ
    · have hx : ‖x‖ ≤ R := (mem_ball_zero_iff.mp (hβsupp (hsprod hp).1)).le
      have hc : DifferentiableAt ℝ (fun y ↦ χ (y, z)) x :=
        (hχ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) |>.differentiableAt
      have hrange : |χ (x, z)| ≤ 1 := by
        rw [abs_of_nonneg (hχrange (x, z)).1]
        exact (hχrange (x, z)).2
      exact (norm_fderiv_frozen_extension_le T hc hrange hM.le hε.le
        (hχderiv (x, z) hp) hx (hρvel z (hγsupp (hsprod hp).2))).trans_eq hbudget
    · rw [fderiv_affineExtension_outside _ _ hp, sub_self, norm_zero]
      norm_num

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
