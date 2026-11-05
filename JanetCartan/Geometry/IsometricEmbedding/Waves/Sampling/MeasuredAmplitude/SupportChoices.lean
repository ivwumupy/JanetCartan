module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.NormalData
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Fixed cutoffs inside the retained normal chart

Choose actual smooth cutoffs on the SAME carrier graph and physical working
ball. The carrier cutoff has a nonempty plateau for the original patch weights;
no carrier, covector, Lebesgue measure or raw field is changed. These choices
close the support inputs of `exists_retained_measuredNormalData` in
`app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff
namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open RawKernel ContinuumRow SeparatedSampling

/-- One actual carrier cutoff fits the retained graph ball, incidence interval,
spectator ball and original phase chart simultaneously. Its positive plateau
allows the SAME original compact patch weight to be retained. All choices
precede current fields, histories and frequencies
(`app:ch_waves:thm:sampling`). -/
theorem exists_retained_carrier_cutoff_buffered
    {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hs : 0 < s) :
    ∃ d > (0 : ℝ), ∃ ψ : Point → ℝ, ∃ B > (0 : ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ PatchBounds ψ B 1 ∧
      (∀ z, WithLp.toLp 2 z ∈ closedBall z₀ d → ψ z = 1) ∧
      (∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 →
        (carrierParameters (v, t), T.reference.spatialPatch (carrierParameters (v, t))) ∈
          closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4) ∧
        carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2) ∧
        t ∈ closedBall (z₀ 0) r ∧ v ∈ closedBall (spectatorCenter z₀) (s / 2)) ∧
      ∀ z, ψ z ≠ 0 →
        WithLp.toLp 2 z ∈ parameterCube P.radius ∧
        (WithLp.toLp 2 z, T.reference.spatialPatch (WithLp.toLp 2 z)) ∈
          ball (z₀, T.reference.spatialPatch z₀) (ρ / 4) := by
  have hzbig : z₀ ∈ parameterInterior (2 * P.radius) :=
    parameterCube_subset_doubledInterior hP.1 (fun i ↦ (hz₀ i).le)
  have hgraph : ContinuousAt (fun z ↦ (z, T.reference.spatialPatch z)) z₀ :=
    continuousAt_id.prodMk
      ((T.reference.spatialPatch_smooth hP).continuousOn.continuousAt
        ((isOpen_parameterInterior _).mem_nhds hzbig))
  let O : Set (Euclidean 3) :=
    (fun z ↦ (z, T.reference.spatialPatch z)) ⁻¹'
        ball (z₀, T.reference.spatialPatch z₀) (ρ / 4) ∩
      parameterInterior P.radius ∩
      (fun z ↦ z 0) ⁻¹' ball (z₀ 0) r ∩
      spectatorCenter ⁻¹' ball (spectatorCenter z₀) (s / 2)
  have hO : O ∈ nhds z₀ := by
    apply Filter.inter_mem
    · apply Filter.inter_mem
      · apply Filter.inter_mem
        · exact hgraph.preimage_mem_nhds (ball_mem_nhds _ (by positivity))
        · exact (isOpen_parameterInterior _).mem_nhds hz₀
      · exact (by fun_prop : Continuous (fun z : Euclidean 3 ↦ z 0)).continuousAt.preimage_mem_nhds
          (ball_mem_nhds _ hr)
    · exact (by unfold spectatorCenter; fun_prop : Continuous spectatorCenter).continuousAt.preimage_mem_nhds
        (ball_mem_nhds _ (by positivity))
  obtain ⟨b, hb, hsub⟩ := Metric.mem_nhds_iff.mp hO
  let f : ContDiffBump z₀ := ⟨b / 2, b, by positivity, by linarith⟩
  let ψ : Point → ℝ := fun z ↦ f (WithLp.toLp 2 z)
  have hψ : ContDiff ℝ ∞ ψ := f.contDiff.comp (by fun_prop)
  have hcompact : HasCompactSupport ψ := by
    exact f.hasCompactSupport.comp_homeomorph
      (PiLp.homeomorph (p := 2) (fun _ : Fin 3 ↦ ℝ)).symm
  obtain ⟨B, hB, hnorm⟩ := hcompact.isCompact.isBounded.exists_pos_norm_le
  have hbound : PatchBounds ψ B 1 := {
    radius_nonneg := hB.le
    nonneg := fun z ↦ f.nonneg
    le_bound := fun z ↦ f.le_one
    support := by
      intro z hz i
      exact (show |z i| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i).trans
        (hnorm z (subset_tsupport ψ hz)) }
  have hmem (z : Point) (hn : ψ z ≠ 0) : WithLp.toLp 2 z ∈ O := by
    apply hsub
    have hf : WithLp.toLp 2 z ∈ Function.support f := hn
    rwa [f.support_eq] at hf
  refine ⟨b / 2, by positivity, ψ, B, hB, hψ, hcompact, hbound,
    fun z hz ↦ f.one_of_mem_closedBall hz, ?_, ?_⟩
  · intro t v hn
    have hw : carrierParameters (v, t) ∈ O := by
      simpa only [← carrierParameters_eq_sampling] using hmem _ hn
    refine ⟨ball_subset_closedBall hw.1.1.1, ?_, ball_subset_closedBall hw.1.2, ?_⟩
    · intro i
      have hi := hw.1.1.2 i
      have hrad := hP.1
      linarith
    · have heq : spectatorCenter (carrierParameters (v, t)) = v := by
        ext i
        fin_cases i <;> rfl
      exact ball_subset_closedBall (heq ▸ hw.2)
  · intro z hn
    exact ⟨fun i ↦ ((hmem z hn).1.1.2 i).le, (hmem z hn).1.1.1⟩

/-- One actual carrier cutoff fits the retained graph ball, incidence interval,
spectator ball and original phase chart simultaneously. Its positive plateau
allows the SAME original compact patch weight to be retained. All choices
precede current fields, histories and frequencies
(`app:ch_waves:thm:sampling`). -/
theorem exists_retained_carrier_cutoff
    {m : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hs : 0 < s) :
    ∃ d > (0 : ℝ), ∃ ψ : Point → ℝ, ∃ B > (0 : ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ PatchBounds ψ B 1 ∧
      (∀ z, WithLp.toLp 2 z ∈ closedBall z₀ d → ψ z = 1) ∧
      ∀ t v, ψ (carrierSamplingEquiv (t, v)) ≠ 0 →
        (carrierParameters (v, t), T.reference.spatialPatch (carrierParameters (v, t))) ∈
          closedBall (z₀, T.reference.spatialPatch z₀) (ρ / 4) ∧
        carrierParameters (v, t) ∈ parameterInterior (3 * P.radius / 2) ∧
        t ∈ closedBall (z₀ 0) r ∧ v ∈ closedBall (spectatorCenter z₀) (s / 2) := by
  obtain ⟨d, hd, ψ, B, hB, hsmooth, hc, hb, hone, hsupport, _hbuffer⟩ :=
    exists_retained_carrier_cutoff_buffered T hP hz₀ hρ hr hs
  exact ⟨d, hd, ψ, B, hB, hsmooth, hc, hb, hone, hsupport⟩

/-- An actual nonzero physical bump fits both the SAME retained extension
plateau and the normal geometry's measurement core
(`app:ch_waves:setup:oscillatory`). -/
theorem exists_retained_physical_cutoff {n : ℕ} {ρ s : ℝ}
    (hρ : 0 < ρ) (hs : 0 < s) :
    ∃ χ : ContDiffBump (0 : Euclidean n),
      χ.rOut ≤ ρ / 2 ∧ χ.rOut ≤ s / 4 ∧
      Function.support (χ : Euclidean n → ℝ) ⊆ closedBall 0 (ρ / 2) ∧
      Function.support (χ : Euclidean n → ℝ) ⊆ closedBall 0 (s / 4) := by
  let b := min (ρ / 2) (s / 4)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  let χ : ContDiffBump (0 : Euclidean n) := ⟨b / 2, b, by positivity, by linarith⟩
  refine ⟨χ, min_le_left _ _, min_le_right _ _, ?_, ?_⟩
  · rw [χ.support_eq]
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_left _ _))
  · rw [χ.support_eq]
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_right _ _))

end JanetCartan.Sampling.MeasuredAmplitude
