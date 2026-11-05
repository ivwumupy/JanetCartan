module

public import JanetCartan.Probability.SamplingPrefixes

/-! # Realization on mesh-dependent probability spaces

The finite block enumeration in `app:ch_waves:thm:sampling` changes with the
mesh. This dependent-space version of the all-prefix argument is consumed by
`SamplingRealization`: it uses the same scalar Bernstein and asymptotic lemmas
as `tendsto_allPrefixes_probability_one_of_bernstein`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.Sampling.Realization

variable {ι F : Type*} [NormedAddCommGroup F]
  {Ω : ℝ → Type*} [∀ Λ, MeasurableSpace (Ω Λ)]

/-- `app:ch_waves:eq:sampling-all-prefixes` on the literal, mesh-dependent
finite shift spaces. The concentration estimate is a full-output input; the
positive variance upper bound need not be the actual variance. -/
theorem tendsto_probability_one
    (μ : (Λ : ℝ) → Measure (Ω Λ))
    (hμ : ∀ Λ > 0, IsProbabilityMeasure (μ Λ))
    (s : ℝ → Finset ι) (Δ : (Λ : ℝ) → ι → Ω Λ → F)
    (τ : ℝ → ι → ℝ) (n : ℕ) {A B K ε : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε)
    (hmeas : ∀ Λ, MeasurableSet (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ)))
    (hcard : ∀ᶠ Λ in atTop, ((s Λ).card : ℝ) ≤ K * Λ)
    (htrace : ∀ᶠ Λ in atTop, ∀ k ∈ s Λ,
      0 ≤ τ Λ k ∧ τ Λ k ≤ B * (A * (Λ * samplingMesh ε Λ ^ 3)) * Λ ^ n)
    (hconcentration : ∀ Λ > 0, ∀ k ∈ s Λ, ∀ t > 0,
      let R := A * (Λ * samplingMesh ε Λ ^ 3)
      let v := B * R
      v + R * t / 3 ≤ t ^ 2 →
      μ Λ {ω | t < ‖Δ Λ k ω‖} ≤ ENNReal.ofReal
        (14 * τ Λ k / v * Real.exp (-(t ^ 2 / (2 * (v + R * t / 3)))))) :
    Tendsto (fun Λ => (μ Λ).real (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ)))
      atTop (𝓝 1) := by
  obtain ⟨c, hc, hscale⟩ := eventually_sampling_bernstein_scale hA hB hε
  have hb : ∀ᶠ Λ in atTop,
      μ Λ (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ))ᶜ ≤
        ENNReal.ofReal (14 * K * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hcard, htrace, hscale] with Λ hΛ hN hτ hs
    exact allPrefixes_failure_le_of_bernstein (μ Λ) (s Λ) (Δ Λ) (τ Λ) n hΛ.le
      hs.2.1 hN hτ hs.2.2.2 (fun k hk =>
        hconcentration Λ hΛ k hk _ hs.1 hs.2.2.1)
  have hf : Tendsto (fun Λ =>
      μ Λ (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ))ᶜ) atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal (tendsto_sampling_failure_bound (14 * K) c ε n hc hε)
    simp only [ENNReal.ofReal_zero] at hh
    apply ENNReal.tendsto_nhds_zero.mpr
    intro δ hδ
    filter_upwards [hb, ENNReal.tendsto_nhds_zero.mp hh δ hδ] with Λ hb hd
    exact hb.trans hd
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hf
  simp only [ENNReal.toReal_zero] at hr
  have hh := tendsto_const_nhds.sub hr (a := (1 : ℝ))
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
  let := hμ Λ hΛ
  change 1 - (μ Λ).real (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ))ᶜ = _
  rw [measureReal_compl (hmeas Λ), probReal_univ]
  ring

/-- Intersect a positive-probability event with the almost-sure admissibility
condition in `app:ch_waves:thm:sampling`. No successful sample is assumed. -/
theorem exists_mem_of_positive_of_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {s : Set X} {P : X → Prop}
    (hs : 0 < μ.real s) (hP : ∀ᵐ x ∂μ, P x) : ∃ x ∈ s, P x := by
  have he : s ∩ {x | P x} =ᵐ[μ] s := by
    filter_upwards [hP] with x hx
    simp [hx]
  have hp : 0 < μ.real (s ∩ {x | P x}) := by
    simpa only [measureReal_congr he] using hs
  obtain ⟨x, hx, hPx⟩ := nonempty_of_measureReal_ne_zero hp.ne'
  exact ⟨x, hx, hPx⟩

end JanetCartan.Sampling.Realization
