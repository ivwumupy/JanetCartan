module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.ConicExtension

open Set Filter Metric
open scoped ContDiff Topology
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CanonicalConic
open FullPhaseCharts.ActualComparison
variable {n : ℕ}

/-- Choose the original physical, carrier and angular masks before the
source scale. Their input radial representatives lie in `K`, and the actual
normalized outputs lie in `Q`. Joint forward continuity is produced by
`exists_source_common_local_charts`; no transformed support is assumed.
Every nonzero frequency is allowed (`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_source_normalized_mask_buffer
    {Y : ℝ → Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {K : Set (InputVariables n)} {Q : Set (Variables n × Euclidean 2)}
    (hK : (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ∈ interior K)
    (hf : ContinuousAt (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (0, ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)))
    (hQ : augmentedTransportGradient (Y 0) ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) ∈ interior Q)
    (hne : transportAveragedGradient (Y 0) ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) ≠ 0) :
    let b := ‖transportAveragedGradient (Y 0) ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)‖
    ∃ r > (0 : ℝ), ∃ a > (0 : ℝ), a ≤ r ∧ ∃ ε > (0 : ℝ),
      ∀ σ ∈ Ioo (-ε) ε, ∀ p ∈ conicMaskSupport z₀ ηb r a,
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ K ∧
        transportAveragedGradient (Y σ) p ≠ 0 ∧
        normalizeOutputRadius b (augmentedTransportGradient (Y σ) p) ∈ Q ∧
        scaleInput (b / ‖transportAveragedGradient (Y σ) p‖) p ∈ K := by
  dsimp only
  let p₀ : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
  let q₀ := augmentedTransportGradient (Y 0) p₀
  let b := ‖q₀.1.2.2‖
  have hb : 0 < b := norm_pos_iff.mpr hne
  have hnorm : ContinuousAt (fun q : ℝ × InputVariables n ↦
      normalizeOutputRadius b (augmentedTransportGradient (Y q.1) q.2)) (0, p₀) :=
    (hf.fst.fst.prodMk (hf.fst.snd.fst.prodMk
      ((continuousAt_const.div hf.fst.snd.snd.norm (norm_ne_zero_iff.mpr hne)).smul
        hf.fst.snd.snd))).prodMk hf.snd
  have hnorm0 : normalizeOutputRadius b q₀ = q₀ := normalizeOutputRadius_eq_self hb rfl
  have htarget : ∀ᶠ q : ℝ × InputVariables n in 𝓝 (0, p₀),
      normalizeOutputRadius b (augmentedTransportGradient (Y q.1) q.2) ∈ Q :=
    hnorm (by
      change Q ∈ 𝓝 (normalizeOutputRadius b q₀)
      rw [hnorm0]
      exact mem_interior_iff_mem_nhds.mp hQ)
  have hnonzero : ∀ᶠ q : ℝ × InputVariables n in 𝓝 (0, p₀),
      transportAveragedGradient (Y q.1) q.2 ≠ 0 :=
    hf ((isOpen_ne_fun continuous_fst.snd.snd continuous_const).mem_nhds hne)
  have hinput : ∀ᶠ q : ℝ × InputVariables n in 𝓝 (0, p₀), q.2 ∈ K :=
    continuousAt_snd (mem_interior_iff_mem_nhds.mp hK)
  have hscaled : ContinuousAt (fun q : ℝ × InputVariables n ↦
      scaleInput (b / ‖transportAveragedGradient (Y q.1) q.2‖) q.2) (0, p₀) :=
    continuousAt_snd.fst.prodMk (continuousAt_snd.snd.fst.prodMk
      ((continuousAt_const.div hf.fst.snd.snd.norm (norm_ne_zero_iff.mpr hne)).smul
        continuousAt_snd.snd.snd))
  have hscaled0 : scaleInput (b / ‖transportAveragedGradient (Y 0) p₀‖) p₀ = p₀ := by
    change scaleInput (b / b) p₀ = p₀
    simp only [div_self hb.ne', scaleInput, one_smul]
  have hscaledK : ∀ᶠ q : ℝ × InputVariables n in 𝓝 (0, p₀),
      scaleInput (b / ‖transportAveragedGradient (Y q.1) q.2‖) q.2 ∈ K :=
    hscaled (by
      change K ∈ 𝓝 (scaleInput (b / ‖transportAveragedGradient (Y 0) p₀‖) p₀)
      rw [hscaled0]
      exact mem_interior_iff_mem_nhds.mp hK)
  obtain ⟨d, hd, hnear⟩ := Metric.eventually_nhds_iff_ball.mp (hinput.and (hnonzero.and (htarget.and hscaledK)))
  obtain ⟨r, hr, _, hrd, a, ha, _, har, had⟩ :=
    exists_refined_mask_radii (r := d) (a := d) hd hd hd
  refine ⟨r, hr, a, ha, har, d, hd, ?_⟩
  intro σ hσ p hp
  let t := ‖ηb‖ / ‖p.2.2‖
  have ht : 0 < t := div_pos (norm_pos_iff.mpr hηb) (norm_pos_iff.mpr hp.2.2.1)
  have hp' := conicMaskSupport_radial_section_mem_ball hηb hr ha had hrd hp
  have hh := hnear (σ, scaleInput t p) (by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero]
    exact ⟨abs_lt.mpr hσ, hp'⟩)
  refine ⟨hh.1, ?_, ?_, ?_⟩
  · intro hz
    exact hh.2.1 (by rw [transportAveragedGradient_smul, hz, smul_zero])
  · change normalizeOutputRadius b (augmentedTransportGradient (Y σ) p) ∈ Q
    simpa only [augmentedTransportGradient_scaleInput, normalizeOutputRadius_scale b _ ht] using hh.2.2.1
  · change scaleInput (b / ‖transportAveragedGradient (Y σ) p‖) p ∈ K
    have hh' := hh.2.2.2
    rw [transportAveragedGradient_smul] at hh'
    have hscale : scaleInput (b / ‖t • transportAveragedGradient (Y σ) p‖) (scaleInput t p) =
        scaleInput (b / ‖transportAveragedGradient (Y σ) p‖) p := by
      simp only [scaleInput, norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul]
      congr 3
      field_simp
    exact hscale ▸ hh'

/-- The closure of the transported original support stays in the SAME
common conic target away from zero frequency. This follows from closedness
of the compact normalized target and continuity of normalization; it does
not put the full uncut support in a finite shell (`bg-full-complex-amplitude`). -/
theorem normalized_mask_image_punctured_buffer
    {b : ℝ} {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {Z : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hQ : IsClosed Q) (hQΩ : Q ⊆ Ω)
    (hmask : ∀ p ∈ Z, normalizeOutputRadius b (augmentedTransportGradient Y p) ∈ Q) :
    closure (augmentedTransportGradient Y '' Z) ∩ {q | q.1.2.2 ≠ 0} ⊆
      normalizedConicTarget b Ω := by
  intro q hq
  refine ⟨hq.2, hQΩ ?_⟩
  have hmap : MapsTo (normalizeOutputRadius b) (augmentedTransportGradient Y '' Z) Q := by
    rintro _ ⟨p, hp, rfl⟩
    exact hmask p hp
  have hh := (normalizeOutputRadius_continuousAt b hq.2).continuousWithinAt.mem_closure hq.1 hmap
  exact hQ.closure_eq ▸ hh
end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
