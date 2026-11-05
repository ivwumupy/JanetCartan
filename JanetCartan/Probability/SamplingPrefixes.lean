module

public import JanetCartan.Probability.SamplingPrefixes.Variance
public import JanetCartan.Probability.SamplingPrefixes.Asymptotics
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Simultaneous sampling over fixed prefixes

This module proves the variance reduction, the finite union argument, and the
sampling asymptotics in `app:ch_waves:thm:sampling`. The operator Bernstein
inequality on the entire output is an explicit input, including its threshold.
It is not proved here. Prefixes are fixed before the random outcome is drawn.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.Sampling

variable {Ω ι F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]

/-- `app:ch_waves:eq:sampling-all-prefixes`: one event controls every fixed prefix.
In the application `Δ K = E_sample^{≤K} - E_h^{≤K}`. -/
def allPrefixesGood (s : Finset ι) (Δ : ι → Ω → F) (t : ℝ) : Set Ω :=
  {ω | ∀ k ∈ s, ‖Δ k ω‖ ≤ t}

/-- `app:ch_waves:eq:sampling-all-prefixes`: a finite union bound needs no
independence between prefixes, so the same samples serve all of them. -/
theorem allPrefixes_failure_le (μ : Measure Ω) (s : Finset ι) (Δ : ι → Ω → F)
    (t b : ℝ) (hb : 0 ≤ b)
    (h : ∀ k ∈ s, μ {ω | t < ‖Δ k ω‖} ≤ ENNReal.ofReal b) :
    μ (allPrefixesGood s Δ t)ᶜ ≤ ENNReal.ofReal ((s.card : ℝ) * b) := by
  have he : (allPrefixesGood s Δ t)ᶜ = ⋃ k ∈ s, {ω | t < ‖Δ k ω‖} := by
    ext ω
    simp [allPrefixesGood]
  rw [he]
  calc
    μ (⋃ k ∈ s, {ω | t < ‖Δ k ω‖}) ≤ ∑ k ∈ s, μ {ω | t < ‖Δ k ω‖} :=
      measure_biUnion_finset_le s _
    _ ≤ ∑ _k ∈ s, ENNReal.ofReal b := Finset.sum_le_sum h
    _ = ENNReal.ofReal ((s.card : ℝ) * b) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hb)]
      simp

/-- `app:ch_waves:thm:sampling`: combine the explicit Bernstein estimate,
the trace upper bound, and the number of fixed prefixes. -/
theorem allPrefixes_failure_le_of_bernstein
    (μ : Measure Ω) (s : Finset ι) (Δ : ι → Ω → F) (τ : ι → ℝ)
    {Λ K R v t c ε : ℝ} (n : ℕ) (hΛ : 0 ≤ Λ) (hv : 0 < v)
    (hcard : (s.card : ℝ) ≤ K * Λ)
    (htrace : ∀ k ∈ s, 0 ≤ τ k ∧ τ k ≤ v * Λ ^ n)
    (hexp : c * Λ ^ (ε / 2) ≤ t ^ 2 / (2 * (v + R * t / 3)))
    (hconcentration : ∀ k ∈ s, μ {ω | t < ‖Δ k ω‖} ≤
      ENNReal.ofReal (14 * τ k / v * Real.exp (-(t ^ 2 / (2 * (v + R * t / 3)))))) :
    μ (allPrefixesGood s Δ t)ᶜ ≤
      ENNReal.ofReal (14 * K * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) := by
  have hprefix : ∀ k ∈ s, μ {ω | t < ‖Δ k ω‖} ≤
      ENNReal.ofReal (14 * Λ ^ n * Real.exp (-c * Λ ^ (ε / 2))) := by
    intro k hk
    apply (hconcentration k hk).trans
    apply ENNReal.ofReal_le_ofReal
    have hratio : 14 * τ k / v ≤ 14 * Λ ^ n := by
      apply (div_le_iff₀ hv).2
      nlinarith [(htrace k hk).2]
    apply mul_le_mul hratio (Real.exp_le_exp.mpr (by linarith))
      (Real.exp_pos _).le (by positivity)
  apply (allPrefixes_failure_le μ s Δ t _ (by positivity) hprefix).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (s.card : ℝ) * (14 * Λ ^ n * Real.exp (-c * Λ ^ (ε / 2))) ≤
        (K * Λ) * (14 * Λ ^ n * Real.exp (-c * Λ ^ (ε / 2))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 14 * K * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2)) := by ring

/-- `app:ch_waves:thm:sampling`: with the paper's mesh and tolerance, the exact
operator concentration formula implies the stated polynomial times stretched
exponential bound. The concentration inequality, trace estimate, and prefix count
are explicit inputs. The variance parameter is a positive upper bound and need
not equal the actual variance norm. -/
theorem eventually_allPrefixes_failure_le
    (μ : ℝ → Measure Ω) (s : ℝ → Finset ι) (Δ : ℝ → ι → Ω → F)
    (τ : ℝ → ι → ℝ) (n : ℕ) {A B K ε : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε)
    (hcard : ∀ᶠ Λ in atTop, ((s Λ).card : ℝ) ≤ K * Λ)
    (htrace : ∀ᶠ Λ in atTop, ∀ k ∈ s Λ,
      0 ≤ τ Λ k ∧ τ Λ k ≤ B * (A * (Λ * samplingMesh ε Λ ^ 3)) * Λ ^ n)
    (hconcentration : ∀ Λ > 0, ∀ k ∈ s Λ, ∀ t > 0,
      let R := A * (Λ * samplingMesh ε Λ ^ 3)
      let v := B * R
      v + R * t / 3 ≤ t ^ 2 →
      μ Λ {ω | t < ‖Δ Λ k ω‖} ≤ ENNReal.ofReal
        (14 * τ Λ k / v * Real.exp (-(t ^ 2 / (2 * (v + R * t / 3)))))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ Λ in atTop,
      μ Λ (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ))ᶜ ≤
        ENNReal.ofReal (14 * K * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2))) := by
  obtain ⟨c, hc, hscale⟩ := eventually_sampling_bernstein_scale hA hB hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ), hcard, htrace, hscale] with Λ hΛ hN hτ hs
  exact allPrefixes_failure_le_of_bernstein (μ Λ) (s Λ) (Δ Λ) (τ Λ) n hΛ.le
    hs.2.1 hN hτ hs.2.2.2 (fun k hk =>
      hconcentration Λ hΛ k hk _ hs.1 hs.2.2.1)

/-- `app:ch_waves:eq:sampling-all-prefixes`: the stated failure estimate
implies convergence of the failure probability to zero, even for measures and
prefix families depending on the band ceiling. -/
theorem tendsto_allPrefixes_failure_of_bound
    (μ : ℝ → Measure Ω) (s : ℝ → Finset ι) (Δ : ℝ → ι → Ω → F)
    {C c ε : ℝ} (n : ℕ) (hc : 0 < c) (hε : 0 < ε)
    (hbound : ∀ᶠ Λ in atTop,
      μ Λ (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ))ᶜ ≤
        ENNReal.ofReal (C * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2)))) :
    Tendsto (fun Λ => μ Λ (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ))ᶜ)
      atTop (𝓝 0) := by
  have hh := ENNReal.tendsto_ofReal (tendsto_sampling_failure_bound C c ε n hc hε)
  simp only [ENNReal.ofReal_zero] at hh
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  filter_upwards [hbound, ENNReal.tendsto_nhds_zero.mp hh δ hδ] with Λ hb hd
  exact hb.trans hd

/-- `app:ch_waves:eq:sampling-all-prefixes`: for measurable good events in
probability spaces, the failure bound gives success probability tending to one. -/
theorem tendsto_allPrefixes_probability_one_of_bound
    (μ : ℝ → Measure Ω) [∀ Λ, IsProbabilityMeasure (μ Λ)]
    (s : ℝ → Finset ι) (Δ : ℝ → ι → Ω → F)
    {C c ε : ℝ} (n : ℕ) (hc : 0 < c) (hε : 0 < ε)
    (hmeas : ∀ Λ, MeasurableSet (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ)))
    (hbound : ∀ᶠ Λ in atTop,
      μ Λ (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ))ᶜ ≤
        ENNReal.ofReal (C * Λ ^ (n + 1) * Real.exp (-c * Λ ^ (ε / 2)))) :
    Tendsto (fun Λ => (μ Λ).real (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ)))
      atTop (𝓝 1) := by
  have hf := tendsto_allPrefixes_failure_of_bound μ s Δ n hc hε hbound
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hf
  simp only [ENNReal.toReal_zero] at hr
  have hh := tendsto_const_nhds.sub hr (a := (1 : ℝ))
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards with Λ
  change 1 - (μ Λ).real (allPrefixesGood (s Λ) (Δ Λ) (samplingTolerance ε Λ))ᶜ = _
  rw [measureReal_compl (hmeas Λ), probReal_univ]
  ring

/-- `app:ch_waves:eq:sampling-all-prefixes`: conditional on the exact full-output
Bernstein inequality, trace bound, and prefix count, the unchanged prefix family
satisfies the sampling tolerance with probability tending to one. -/
theorem tendsto_allPrefixes_probability_one_of_bernstein
    (μ : ℝ → Measure Ω) [∀ Λ, IsProbabilityMeasure (μ Λ)]
    (s : ℝ → Finset ι) (Δ : ℝ → ι → Ω → F)
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
  obtain ⟨c, hc, hb⟩ := eventually_allPrefixes_failure_le μ s Δ τ n
    hA hB hε hcard htrace hconcentration
  exact tendsto_allPrefixes_probability_one_of_bound μ s Δ n hc hε hmeas hb

end JanetCartan.Sampling
