module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.Annular

/-!
# The global inverse bound for the frozen phase

The inverse of the frozen momentum map is the literal energy together with
the tangential covector. Its Lipschitz bound supplies the reference estimate
for `app:ch_response:thm:response-literal-transfer`, before transferring it to
the current phase by the published full derivative comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.CompatibleResponse
open ActualCarriers ActualCarriers.FrozenPhaseReference

/-- The literal frozen energy is globally Lipschitz on nonzero covectors.
Smoothness on the unit sphere and positive degree one supply the constant;
this is the scalar input to the frozen canonical inverse estimate in
`app:ch_response:thm:response-literal-transfer`. -/
theorem exists_frozenEnergy_lipschitz (n : ℕ) :
    ∃ L > (0 : ℝ), ∀ p : Euclidean n, p ≠ 0 → ∀ q : Euclidean n, q ≠ 0 →
      ‖(frozenSymbol n).h (0, p) - (frozenSymbol n).h (0, q)‖ ≤ L * ‖p - q‖ := by
  let f : Euclidean n → ℝ := fun p ↦ (frozenSymbol n).h (0, p)
  let K : Set (Euclidean n) := sphere 0 1
  have hsmooth : ∀ p ∈ K, ContDiffAt ℝ ∞ f p := by
    intro p hp
    have hp0 : p ≠ 0 := by intro he; simp [K, he] at hp
    exact ((frozenSymbol_smooth n).contDiffAt
      ((frozenSymbol n).isOpen_domain.mem_nhds (mem_frozenSymbol_domain _ |>.mpr hp0))).comp p
        (contDiffAt_const.prodMk contDiffAt_id)
  have hloc : LocallyLipschitzOn K f := by
    intro p hp
    obtain ⟨L, V, hV, hL⟩ := ((hsmooth p hp).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨L, V, mem_nhdsWithin_of_mem_nhds hV, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact (isCompact_sphere _ _)
  obtain ⟨B, hB, hbound⟩ := ((isCompact_sphere (0 : Euclidean n) 1).image_of_continuousOn
    (fun p hp ↦ (hsmooth p hp).continuousAt.continuousWithinAt)).isBounded.exists_pos_norm_le
  have hhom (p : Euclidean n) {r : ℝ} (hr : 0 < r) : f (r • p) = r * f p :=
    normalizedSymbol_pos_homogeneous (fun _ ↦ cubeStress n) (0, p) hr
  refine ⟨2 * (L : ℝ) + B, by positivity, ?_⟩
  intro p hp q hq
  let u := ‖p‖⁻¹ • p
  let v := ‖q‖⁻¹ • q
  have hpN : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hqN : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hpN.ne']
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hqN.ne']
  have huK : u ∈ K := by simpa [K] using hu
  have hvK : v ∈ K := by simpa [K] using hv
  have hpu : ‖p‖ • u = p := smul_inv_smul₀ hpN.ne' p
  have hqv : ‖q‖ • v = q := smul_inv_smul₀ hqN.ne' q
  have hpq : |‖p‖ - ‖q‖| ≤ ‖p - q‖ := abs_norm_sub_norm_le p q
  have hunit : ‖p‖ * ‖u - v‖ ≤ 2 * ‖p - q‖ := by
    have he : ‖p‖ • (u - v) = (p - q) + (‖q‖ - ‖p‖) • v := by
      rw [smul_sub, hpu, sub_smul, hqv]
      abel
    have hh := norm_add_le (p - q) ((‖q‖ - ‖p‖) • v)
    rw [← he, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpN,
      Real.norm_eq_abs, hv, mul_one, abs_sub_comm] at hh
    linarith
  have hfu : f p = ‖p‖ * f u := by rw [← hhom u hpN, hpu]
  have hfv : f q = ‖q‖ * f v := by rw [← hhom v hqN, hqv]
  have hfuv : ‖f u - f v‖ ≤ (L : ℝ) * ‖u - v‖ := hL.norm_sub_le huK hvK
  have hfvB : ‖f v‖ ≤ B := hbound _ ⟨v, hvK, rfl⟩
  change ‖f p - f q‖ ≤ _
  calc
    _ = ‖‖p‖ * (f u - f v) + (‖p‖ - ‖q‖) * f v‖ := by rw [hfu, hfv]; congr 1; ring
    _ ≤ ‖p‖ * ‖f u - f v‖ + |‖p‖ - ‖q‖| * ‖f v‖ := by
      simpa only [norm_mul, Real.norm_eq_abs, abs_norm] using
        norm_add_le (‖p‖ * (f u - f v)) ((‖p‖ - ‖q‖) * f v)
    _ ≤ ‖p‖ * ((L : ℝ) * ‖u - v‖) + ‖p - q‖ * B :=
      add_le_add (mul_le_mul_of_nonneg_left hfuv hpN.le)
        (mul_le_mul hpq hfvB (norm_nonneg _) (norm_nonneg _))
    _ ≤ (2 * (L : ℝ) + B) * ‖p - q‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hunit L.coe_nonneg]

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Frozen momentum retains the canonical tangential component everywhere on
the selected target, by its actual Hamilton ODE
(`app:ch_response:thm:response-compatible-choice`). -/
theorem reference_chartMomentum_adjoint
    {z : Euclidean n × (ℝ × Euclidean (n - 1))} (hz : z ∈ T.target) :
    T.reference.sectionEmbedding.toContinuousLinearMap.adjoint
      (T.reference.chart.chartMomentum z) = z.2.2 := by
  have ha := T.reference.chart.source_admissible _ (T.reference.chart.maps_to_source z hz)
  change T.reference.sectionEmbedding.toContinuousLinearMap.adjoint
    (T.reference.flow.momentum _) = _
  rw [frozenFlow_momentum_eq_initial T.reference.flow ha.1 ha.2]
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  have he := T.reference.flow.initial_momentum _ ha.2 v
  have hsec : T.reference.flow.sectionMap =
      T.reference.sectionEmbedding.toContinuousLinearMap :=
    T.data.localReference.family.reference_control.section_eq
  rw [hsec] at he
  exact he

/-- A global inverse estimate for the actual frozen conic momentum on the
entire active cone. It follows from the explicit energy/tangential inverse,
independently of pointwise mixed invertibility
(`app:ch_response:thm:response-literal-transfer`, complete complement). -/
theorem exists_reference_conic_inverse_bound :
    ∃ L > (0 : ℝ), ∀ (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ),
      ∀ x : Euclidean n, ∀ η θ : ℝ × Euclidean (n - 1),
      (x, η) ∈ CharacteristicRoot.conicDomain ℓ T.target →
      (x, θ) ∈ CharacteristicRoot.conicDomain ℓ T.target →
      ‖η - θ‖ ≤ L * ‖gradient (fun y ↦ T.reference.chart.conicPhase ℓ (y, η)) x -
        gradient (fun y ↦ T.reference.chart.conicPhase ℓ (y, θ)) x‖ := by
  obtain ⟨L, hL, hLip⟩ := exists_frozenEnergy_lipschitz n
  let J := T.reference.sectionEmbedding.toContinuousLinearMap.adjoint
  refine ⟨L + ‖J‖ + 1, by positivity, ?_⟩
  intro ℓ x η θ hη hθ
  let F := fun η ↦ gradient (fun y ↦ T.reference.chart.conicPhase ℓ (y, η)) x
  have hconic : (frozenSymbol n).ConicHomogeneous := {
    scale_mem := by
      intro z hz a ha
      exact (mem_frozenSymbol_domain _).mpr
        (smul_ne_zero ha.ne' ((mem_frozenSymbol_domain _).mp hz))
    scale_symbol := by
      intro z _ a ha
      exact normalizedSymbol_pos_homogeneous (fun _ ↦ cubeStress n) z ha }
  have hηe := T.reference.chart.conicPhase_eikonal ℓ hconic hη
  have hθe := T.reference.chart.conicPhase_eikonal ℓ hconic hθ
  have hE : ‖η.1 - θ.1‖ ≤ L * ‖F η - F θ‖ := by
    rw [← hηe.2, ← hθe.2]
    change ‖(frozenSymbol n).h (x, F η) - (frozenSymbol n).h (x, F θ)‖ ≤ _
    simp only [frozenSymbol_h]
    simpa only [frozenSymbol_h] using hLip (F η) ((mem_frozenSymbol_domain _).mp hηe.1)
      (F θ) ((mem_frozenSymbol_domain _).mp hθe.1)
  have hJ (ζ : ℝ × Euclidean (n - 1))
      (hζ : (x, ζ) ∈ CharacteristicRoot.conicDomain ℓ T.target) : J (F ζ) = ζ.2 := by
    rw [show F ζ = _ from T.reference.chart.gradient_conicPhase ℓ hζ, map_smul,
      T.reference_chartMomentum_adjoint hζ.2]
    exact smul_inv_smul₀ hζ.1.ne' ζ.2
  have hT : ‖η.2 - θ.2‖ ≤ ‖J‖ * ‖F η - F θ‖ := by
    rw [← hJ η hη, ← hJ θ hθ, ← map_sub]
    exact J.le_opNorm _
  change ‖η - θ‖ ≤ (L + ‖J‖ + 1) * ‖F η - F θ‖
  rw [Prod.norm_def]
  exact max_le (hE.trans (by nlinarith [norm_nonneg J, norm_nonneg (F η - F θ)]))
    (hT.trans (by nlinarith [norm_nonneg (F η - F θ)]))

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
