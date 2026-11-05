module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform parameter remainders on a fixed spatial support

The compactness step in the operator differentiation argument of
`app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace JanetCartan.NormalComparison

/-- A parameter derivative vanishes outside the fixed spatial support of a
family, as used in `app:ch_osc:prop:osc-normal`. -/
theorem parameterDerivative_eq_zero_off_support {Z : Type*}
    {t t' : ℝ → Z → ℂ} {K : Set Z}
    (hs : ∀ s z, z ∉ K → t s z = 0)
    (hd : ∀ s z, HasDerivAt (fun r ↦ t r z) (t' s z) s)
    (s : ℝ) {z : Z} (hz : z ∉ K) : t' s z = 0 := by
  have heq : (fun r ↦ t r z) = fun _ ↦ (0 : ℂ) := funext fun r ↦ hs r z hz
  exact (heq ▸ hd s z).unique (hasDerivAt_const s 0)

/-- Joint continuity of the actual parameter derivative gives a uniform first
order remainder on a fixed compact support (`app:ch_osc:prop:osc-normal`).
No uniform convergence or operator differentiability is assumed. -/
theorem eventually_uniform_parameter_remainder {Z : Type*} [PseudoMetricSpace Z]
    {t t' : ℝ → Z → ℂ} {K : Set Z} (hK : IsCompact K)
    (hs : ∀ s z, z ∉ K → t s z = 0)
    (hd : ∀ s z, HasDerivAt (fun r ↦ t r z) (t' s z) s)
    (hc : Continuous (Function.uncurry t')) (s₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝 s₀, ∀ z,
      ‖t s z - t s₀ z - (s - s₀) • t' s₀ z‖ ≤ ε * ‖s - s₀‖ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcK : Continuous (fun p : ℝ × K ↦ t' p.1 p.2) :=
    hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hu := Metric.tendstoUniformly_iff.mp
    (hcK.tendstoUniformly (fun s (z : K) ↦ t' s z) s₀) ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hu
  filter_upwards [Metric.ball_mem_nhds s₀ hδ] with s hsδ
  intro z
  by_cases hz : z ∈ K
  · have hder (r : ℝ) : HasDerivAt
        (fun r ↦ t r z - (r - s₀) • t' s₀ z) (t' r z - t' s₀ z) r := by
      convert (hd r z).sub (((hasDerivAt_id r).sub_const s₀).smul_const (t' s₀ z)) using 1 <;> first | rfl | simp only [one_smul]
    have hb (r : ℝ) (hr : r ∈ Metric.ball s₀ δ) : ‖t' r z - t' s₀ z‖ ≤ ε := by
      have hh := hδbound hr ⟨z, hz⟩
      simpa only [dist_eq_norm, norm_sub_rev] using hh.le
    have hh := (convex_ball s₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r _ ↦ (hder r).hasDerivWithinAt) hb (Metric.mem_ball_self hδ) hsδ
    simpa only [sub_self, zero_smul, sub_zero, sub_right_comm] using hh
  · simp only [hs s z hz, hs s₀ z hz, parameterDerivative_eq_zero_off_support hs hd s₀ hz,
      smul_zero, sub_zero, norm_zero]
    exact mul_nonneg hε.le (norm_nonneg _)

end JanetCartan.NormalComparison
