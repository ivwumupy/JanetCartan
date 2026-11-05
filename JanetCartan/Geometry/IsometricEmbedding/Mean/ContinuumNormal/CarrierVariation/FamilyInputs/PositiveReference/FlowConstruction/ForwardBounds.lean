module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.RetainedLift
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.ActualEstimates

/-!
# Uniform forward bounds for the original retained charts

Apply the actual characteristic estimate to the retained autonomous lift.
ODE uniqueness preserves the supplied forward map on the initial open
cylinder; smoothness across its boundary preserves all jets on the original
closed cylinder. No new chart, flow domain or mask is selected.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω K : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R B τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}

/-- The forward-map identity supplied by ODE uniqueness preserves every
closed-cylinder seminorm, including boundary jets (`app:ch_waves:eq:joint-tame`). -/
private theorem retained_chart_forward_cNorm_eq_on_closed_cylinder
    (hR : 0 < R) (hτ : 0 < τ)
    (c c' : Chart T Ω K p₀ R B τ row col F)
    (he : EqOn c.forward c'.forward (Ioo (-τ) τ ×ˢ ball p₀ (R / 8))) (k : ℕ) :
    cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) k c.forward =
      cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) k c'.forward := by
  have hopen : IsOpen (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) := isOpen_Ioo.prod isOpen_ball
  have hwide : IsOpen (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) :=
    isOpen_Ioo.prod isOpen_ball
  have hsub : Icc (-τ) τ ×ˢ closedBall p₀ (R / 8) ⊆
      Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4) := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩,
      (closedBall_subset_ball (by linarith : R / 8 < R / 4)) hq.2⟩
  have hclosure : closure (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) =
      Icc (-τ) τ ×ˢ closedBall p₀ (R / 8) := by
    rw [closure_prod_eq, closure_Ioo (by linarith : -τ ≠ τ),
      closure_ball p₀ (by linarith : R / 8 ≠ 0)]
  have hjets (j : ℕ) : EqOn (iteratedFDeriv ℝ j c.forward)
      (iteratedFDeriv ℝ j c'.forward) (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) := by
    have ho : EqOn (iteratedFDeriv ℝ j c.forward)
        (iteratedFDeriv ℝ j c'.forward) (Ioo (-τ) τ ×ˢ ball p₀ (R / 8)) := by
      intro q hq
      exact ((he.eventuallyEq_of_mem (hopen.mem_nhds hq)).iteratedFDeriv ℝ j).self_of_nhds
    apply ho.of_subset_closure
    · intro q hq
      exact ((c.forward_buffer_smooth.contDiffAt (hwide.mem_nhds (hsub hq))).continuousAt_iteratedFDeriv
        (by simp : (j : WithTop ℕ∞) ≤ ∞)).continuousWithinAt
    · intro q hq
      exact ((c'.forward_buffer_smooth.contDiffAt (hwide.mem_nhds (hsub hq))).continuousAt_iteratedFDeriv
        (by simp : (j : WithTop ℕ∞) ≤ ∞)).continuousWithinAt
    · exact Set.prod_mono Ioo_subset_Icc_self ball_subset_closedBall
    · rw [hclosure]
  unfold cNorm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact Set.image_congr (fun q hq ↦ congrArg norm (hjets j hq))

/-- Derive the forward C1 bound for every original retained chart from its
primitive direction bound and exact existence time. The constant precedes the
immersion and chart; the original coefficient set and entire closed cylinder
are preserved. This instantiates the forward estimates in
`exists_retained_fullAmplitude_comparison_on_selected_geometry` and
`exists_initialScale_for_selected_retained_history_normal_comparison` without
assuming another flow estimate. The inverse is compared only on its original
tube; no equality of its arbitrary exterior extensions is used. Sources:
`app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-Psi`, and
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_retained_chart_forward_bound
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hR : 0 < R) (hB : 0 ≤ B)
    (hτeq : τ = existenceTime R (liftedLowBound T B) / 4)
    (hbuffer : MapsTo (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K) :
    ∃ Mc > (0 : ℝ), ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
      (c : Chart T Ω K p₀ R B τ row col F),
      cNorm (Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)) 1 c.forward ≤ Mc := by
  obtain ⟨C, hC, hflow⟩ := exists_actual_characteristics_cNorm_bound T p₀ hR hB hΩ hK hKΩ hbuffer 1
  refine ⟨C * (1 + B), mul_pos hC (by linarith), ?_⟩
  intro F row col c
  obtain ⟨c', Ψ, hQ, _, hΨ, hf, _, he, _, _⟩ :=
    ContinuumRow.NormalizedChartFamily.exists_retained_chart_lift_enrichment hΩ hK hKΩ
      hR hB hτeq hbuffer c
  have hΨQ := hΨ
  rw [hQ] at hΨQ
  have hb := hflow c.Q row col c.direction_smooth c.direction_bound Ψ hΨQ.smooth
    (fun q hq ↦ hΨQ.initial q (ball_subset_closedBall hq))
    (fun q hq t ht ↦ hΨQ.hasDerivAt (ball_subset_closedBall hq) ht)
    (fun q hq t ht ↦ hΨQ.range q
      (closedBall_subset_closedBall (by linarith : R / 4 ≤ R / 2) hq) t
      (Ioo_subset_Icc_self ht))
  have hτ : 0 < τ := by
    rw [hτeq]
    exact div_pos (existenceTime_pos hR (liftedLowBound_nonneg T hB)) (by norm_num)
  rw [retained_chart_forward_cNorm_eq_on_closed_cylinder hR hτ c c' he.symm 1, hf, hτeq]
  exact (le_add_of_nonneg_right (cNorm_nonneg _ 1 (footpointFromLift Ψ))).trans
    (hb.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) c.direction_bound) hC.le))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction
