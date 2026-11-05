module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.Sectors

/-!
# Uniform mixed gaps of the selected current chart

The mixed-projection part of `app:ch_response:thm:response-compatible-choice`.
Nondegeneracy is derived from the actual frozen inverse chart. Compactness and
the producer's full momentum derivative comparison give a positive threshold
in the primitive frame seminorm, before choosing the current frame.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.CompatibleResponse

private theorem compact_injective_norm_gap {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set X} (hK : IsCompact K) (A : X → E →L[ℝ] F)
    (hA : ContinuousOn A K) (hinj : ∀ x ∈ K, Function.Injective (A x)) :
    ∃ c > (0 : ℝ), ∀ x ∈ K, ∀ v : E, c * ‖v‖ ≤ ‖A x v‖ := by
  have hc : ContinuousOn (fun q : X × E ↦ ‖A q.1 q.2‖)
      (K ×ˢ sphere (0 : E) 1) :=
    ((hA.comp continuous_fst.continuousOn (fun _ h ↦ h.1)).clm_apply
      continuous_snd.continuousOn).norm
  obtain ⟨c, hcpos, hb⟩ := exists_uniform_positive_bound
    (hK.prod (isCompact_sphere (0 : E) 1)) hc (by
      rintro ⟨x, v⟩ ⟨hx, hv⟩
      apply norm_pos_iff.mpr
      intro hz
      have he : v = 0 := hinj x hx (hz.trans (map_zero _).symm)
      simp [he] at hv)
  refine ⟨c, hcpos, fun x hx v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hs : ‖v‖⁻¹ • v ∈ sphere (0 : E) 1 := by
    simp [norm_smul, inv_mul_cancel₀ hn]
  have hh := mul_le_mul_of_nonneg_right (hb (x, ‖v‖⁻¹ • v) ⟨hx, hs⟩) (norm_nonneg v)
  simpa only [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
    mul_right_comm (‖v‖⁻¹), inv_mul_cancel₀ hn, one_mul] using hh

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Smoothness of the same current inverse coordinates on their retained
target (`app:ch_response:thm:response-compatible-choice`). -/
theorem current_coordinates_smooth (Q : _) :
    ContDiffOn ℝ ∞ (T.currentChart Q).coordinates (T.currentChart Q).target :=
  (T.family.coordinates_smooth Q).mono
    (ball_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius ≤ 2 * T.family.radius))

/-- Both actual canonical projection differentials are equivalences on the
whole selected target. No desired mixed gap is a premise
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergy_projection_equivalences (Q : _) {q : Euclidean n ×
    (ℝ × Euclidean (n - 1))} (hq : q ∈ T.target) :
    (∃ A : (ℝ × Euclidean (n - 1)) ≃L[ℝ] Euclidean n,
      (A : (ℝ × Euclidean (n - 1)) →L[ℝ] Euclidean n) =
        (T.currentChart Q).mixedMomentumDerivative q) ∧
    (∃ B : Euclidean n ≃L[ℝ] (ℝ × Euclidean (n - 1)),
      (B : Euclidean n →L[ℝ] (ℝ × Euclidean (n - 1))) =
        (T.currentChart Q).coordinatePositionDerivative q) :=
  ⟨(T.currentChart Q).exists_mixedMomentumEquiv (T.family.momentum_smooth Q)
    (T.current_coordinates_smooth Q) hq,
    (T.currentChart Q).exists_coordinatePositionEquiv hq⟩

/-- A uniform mixed lower bound on any compact part of the selected target,
valid for every sufficiently close smooth frame. The threshold comes from
the actual producer's `C⁶` frame-to-momentum comparison
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_sectionEnergy_mixed_gap
    {K : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hK : IsCompact K) (hKt : K ⊆ T.target) :
    ∃ γ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ q ∈ K, ∀ η : ℝ × Euclidean (n - 1),
        γ * ‖η‖ ≤ ‖(T.currentChart Q).mixedMomentumDerivative q η‖ := by
  have hm := T.reference.chart.continuousOn_mixedMomentumDerivative
    T.reference.momentum_smooth T.reference.coordinates_smooth
  obtain ⟨g, hg, hgb⟩ := compact_injective_norm_gap hK
    T.reference.chart.mixedMomentumDerivative (hm.mono hKt)
    (fun q hq ↦ T.reference.chart.mixedMomentumDerivative_injective
      T.reference.momentum_smooth T.reference.coordinates_smooth (hKt hq))
  obtain ⟨δ, hδ, hcomp⟩ := T.family.exists_momentum_comparison_threshold (half_pos hg)
  refine ⟨g / 2, half_pos hg, δ, hδ, fun Q hQ q hq η ↦ ?_⟩
  have hc := (hcomp Q hQ q (ball_subset_closedBall (hKt hq))).2.le
  have hdiff : ‖(T.currentChart Q).mixedMomentumDerivative q η -
      T.reference.chart.mixedMomentumDerivative q η‖ ≤ (g / 2) * ‖η‖ := by
    rw [(T.currentChart Q).mixedMomentumDerivative_eq (T.family.momentum_smooth Q)
      (T.current_coordinates_smooth Q) (hKt hq),
      T.reference.chart.mixedMomentumDerivative_eq T.reference.momentum_smooth
        T.reference.coordinates_smooth (hKt hq)]
    have hb := ((fderiv ℝ (T.currentChart Q).chartMomentum q -
      fderiv ℝ T.reference.chart.chartMomentum q).le_opNorm
        ((0 : Euclidean n), η)).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    have hn : ‖((0 : Euclidean n), η)‖ = ‖η‖ := by simp
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      sub_apply, hn] using hb
  have ht := norm_le_norm_sub_add (T.reference.chart.mixedMomentumDerivative q η)
    ((T.currentChart Q).mixedMomentumDerivative q η)
  rw [norm_sub_rev] at ht
  have hb := hgb q hq η
  linarith

/-- The canonical pairing transfers the mixed lower bound to the other
canonical projection, with the factor two from the retained product norm
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergy_coordinate_gap (Q : _)
    {q : Euclidean n × (ℝ × Euclidean (n - 1))} (hq : q ∈ T.target)
    {γ : ℝ} (hγ : 0 < γ)
    (hm : ∀ η, γ * ‖η‖ ≤ ‖(T.currentChart Q).mixedMomentumDerivative q η‖)
    (v : Euclidean n) :
    (γ / 2) * ‖v‖ ≤ ‖(T.currentChart Q).coordinatePositionDerivative q v‖ := by
  obtain ⟨A, hA⟩ := (T.sectionEnergy_projection_equivalences Q hq).1
  let η := A.symm v
  let w := (T.currentChart Q).coordinatePositionDerivative q v
  have hAv : (T.currentChart Q).mixedMomentumDerivative q η = v := by
    rw [← hA]
    exact A.apply_symm_apply v
  have hg : γ * ‖η‖ ≤ ‖v‖ := by simpa only [hAv] using hm η
  have hp := (T.currentChart Q).mixedMomentumDerivative_pairing
    (T.family.momentum_smooth Q) (T.current_coordinates_smooth Q) hq v η
  rw [hAv, real_inner_self_eq_norm_sq] at hp
  have hb : ‖canonicalCovector w η‖ ≤ 2 * ‖w‖ * ‖η‖ := by
    calc
      _ ≤ ‖w.1 * η.1‖ + ‖⟪w.2, η.2⟫_ℝ‖ := norm_add_le _ _
      _ ≤ ‖w.1‖ * ‖η.1‖ + ‖w.2‖ * ‖η.2‖ := by
        rw [norm_mul]
        exact add_le_add le_rfl (norm_inner_le_norm _ _)
      _ ≤ ‖w‖ * ‖η‖ + ‖w‖ * ‖η‖ := add_le_add
        (mul_le_mul (norm_fst_le w) (norm_fst_le η) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (norm_snd_le w) (norm_snd_le η) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  rw [← hp, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hb
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h₁ := mul_le_mul_of_nonneg_left hb hγ.le
  have h₂ := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2 * ‖w‖)
  have hcancel : (γ * ‖v‖) * ‖v‖ ≤ (2 * ‖w‖) * ‖v‖ := by nlinarith
  have h := (mul_le_mul_iff_left₀ hvpos).mp hcancel
  change (γ / 2) * ‖v‖ ≤ ‖w‖
  linarith

/-- Uniform lower bounds for both projection differentials on an arbitrary
compact buffered subset of the same target, from primitive frame closeness
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_sectionEnergy_projection_gaps
    {K : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hK : IsCompact K) (hKt : K ⊆ T.target) :
    ∃ γ > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ q ∈ K,
        (∀ η : ℝ × Euclidean (n - 1),
          γ * ‖η‖ ≤ ‖(T.currentChart Q).mixedMomentumDerivative q η‖) ∧
        (∀ v : Euclidean n,
          γ * ‖v‖ ≤ ‖(T.currentChart Q).coordinatePositionDerivative q v‖) := by
  obtain ⟨g, hg, δ, hδ, hgap⟩ := T.exists_sectionEnergy_mixed_gap hK hKt
  refine ⟨g / 2, half_pos hg, δ, hδ, fun Q hQ q hq ↦ ⟨?_, ?_⟩⟩
  · intro η
    exact (mul_le_mul_of_nonneg_right (by linarith : g / 2 ≤ g) (norm_nonneg η)).trans
      (hgap Q hQ q hq η)
  · exact T.sectionEnergy_coordinate_gap Q (hKt hq) hg (hgap Q hQ q hq)

/-- Choose actual buffered sectors and a physical response ball together with
their uniform projection gaps. All choices precede the frame and requested
frequency (`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_buffered_sectionEnergy_projection_gaps {c C : ℝ} (hP : P.IsValid c C) :
    ∃ (r γ δ : ℝ) (Vin Vout : Set (ℝ × Euclidean (n - 1))),
      0 < r ∧ 0 < γ ∧ 0 < δ ∧ IsOpen Vin ∧ IsOpen Vout ∧
      T.primaryCanonicalCompact ⊆ Vin ∧ closure Vin ⊆ Vout ∧
      closure Vout ⊆ T.sectionEnergyDomain ∧ IsCompact (closure Vout) ∧
      Disjoint (closure Vout) (Neg.neg ⁻¹' closure Vout) ∧
      closedBall (0 : Euclidean n) (2 * r) ⊆ ball 0 T.physicalRadius ∧
      ∀ Q, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ x ∈ closedBall (0 : Euclidean n) (2 * r), ∀ η ∈ closure Vout,
        (∀ u : ℝ × Euclidean (n - 1),
          γ * ‖u‖ ≤ ‖(T.currentChart Q).mixedMomentumDerivative (x, η) u‖) ∧
        (∀ v : Euclidean n,
          γ * ‖v‖ ≤ ‖(T.currentChart Q).coordinatePositionDerivative (x, η) v‖) := by
  obtain ⟨Vin, Vout, hi, ho, hKi, hio, hoD, _hci, hco, hdis⟩ :=
    T.exists_buffered_sectionEnergy_sectors hP
  let r := T.physicalRadius / 4
  have hr : 0 < r := div_pos T.physicalRadius_pos (by norm_num)
  have hball : closedBall (0 : Euclidean n) (2 * r) ⊆ ball 0 T.physicalRadius :=
    closedBall_subset_ball (by dsimp [r]; linarith [T.physicalRadius_pos])
  have htarget : closedBall (0 : Euclidean n) (2 * r) ×ˢ closure Vout ⊆ T.target := by
    rintro ⟨x, η⟩ ⟨hx, hη⟩
    change dist (x, η) (T.data.adapted.embedding T.data.adapted.baseData.1,
      T.data.adapted.baseData.2) < T.family.radius
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, (hoD hη).trans_le (min_le_left _ _)⟩
    have hlt : T.physicalRadius < T.family.radius := by
      have hp := T.physicalRadius_pos
      have hm := min_le_left T.family.radius (3 * T.family.sourceRadius)
      dsimp [physicalRadius] at hp ⊢
      linarith
    simpa only [FrozenPhaseReference.AdaptedSection.baseData, map_zero] using
      (hball hx).trans hlt
  obtain ⟨γ, hγ, δ, hδ, hgap⟩ := T.exists_sectionEnergy_projection_gaps
    ((isCompact_closedBall _ _).prod hco) htarget
  exact ⟨r, γ, δ, Vin, Vout, hr, hγ, hδ, hi, ho, hKi, hio, hoD, hco, hdis,
    hball, fun Q hQ x hx η hη ↦ hgap Q hQ (x, η) ⟨hx, hη⟩⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
