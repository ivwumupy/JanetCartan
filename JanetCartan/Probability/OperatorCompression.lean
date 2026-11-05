module

public import JanetCartan.Probability.OperatorCompression.FiniteRank
public import JanetCartan.Probability.OperatorCompression.Tail
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Passing concentration bounds through finite-rank compression

The infinite-dimensional limit argument in `app:ch_waves:thm:sampling` of
`paper.tex`, lines 5949–5959. The finite-dimensional Bernstein inequality is an
explicit input; this module does not prove that inequality. The supporting modules
prove norm convergence, variance domination, and the preservation of norm and trace
bounds under compression. No trace-class API is assumed: trace bounds are expressed
by bounds on finite orthonormal diagonal sums.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace JanetCartan.OperatorCompression

variable {𝕜 H Ω : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H] [MeasurableSpace Ω]

/-- Uniform bounds for the finite-dimensional sums pass to the full compact
self-adjoint sum (`app:ch_waves:thm:sampling`, Fatou step). -/
theorem measure_sum_norm_tail_le_of_finite_compressions
    (μ : Measure Ω) (U : ℕ → Submodule 𝕜 H) [∀ n, FiniteDimensional 𝕜 (U n)]
    (hmono : Monotone U) (hdense : (⨆ n, U n).topologicalClosure = ⊤)
    {ι : Type*} (s : Finset ι) (Y : ι → Ω → H →L[𝕜] H)
    (hc : ∀ i ∈ s, ∀ ω, IsCompactOperator (Y i ω))
    (hsa : ∀ i ∈ s, ∀ ω, IsSelfAdjoint (Y i ω))
    (t : ℝ) (B : ℝ≥0∞)
    (hfinite : ∀ n, μ {ω | t < ‖∑ i ∈ s, restrictCompression (U n) (Y i ω)‖} ≤ B) :
    μ {ω | t < ‖∑ i ∈ s, Y i ω‖} ≤ B := by
  apply measure_norm_tail_le_of_tendsto μ
    (fun n ω ↦ ∑ i ∈ s, compress (U n).starProjection (Y i ω)) (fun ω ↦ ∑ i ∈ s, Y i ω)
    (fun ω ↦ tendsto_compress_sum U hmono hdense s (fun i ↦ Y i ω)
      (fun i hi ↦ hc i hi ω) (fun i hi ↦ hsa i hi ω)) t B
  intro n
  simpa only [norm_sum_restrictCompression] using hfinite n

/-- The exact Bernstein tail expression from `app:ch_waves:thm:sampling`.
The variance upper parameter `v` is positive, including when the actual variance is zero. -/
def bernsteinTail (R v τ t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((14 * τ / v) * Real.exp (-(t ^ 2) / (2 * (v + R * t / 3))))

/-- Conditional infinite-dimensional Bernstein extension from
`app:ch_waves:thm:sampling`. The sole concentration input is the displayed
finite-dimensional inequality for the restricted sums, with exactly the same
`R`, positive upper variance parameter `v`, trace upper bound `τ`, and threshold.
The hypotheses needed to establish that input (independence, centering, and the
variance and trace bounds) belong to the finite-dimensional Bernstein application. -/
theorem bernstein_of_finite_compressions
    (μ : Measure Ω) (U : ℕ → Submodule 𝕜 H) [∀ n, FiniteDimensional 𝕜 (U n)]
    (hmono : Monotone U) (hdense : (⨆ n, U n).topologicalClosure = ⊤)
    {ι : Type*} (s : Finset ι) (Y : ι → Ω → H →L[𝕜] H)
    (hc : ∀ i ∈ s, ∀ ω, IsCompactOperator (Y i ω))
    (hsa : ∀ i ∈ s, ∀ ω, IsSelfAdjoint (Y i ω))
    (R v τ : ℝ)
    (hfinite : ∀ n t, 0 ≤ R → 0 < v → 0 < t → v + R * t / 3 ≤ t ^ 2 →
      μ {ω | t < ‖∑ i ∈ s, restrictCompression (U n) (Y i ω)‖} ≤ bernsteinTail R v τ t)
    (hR : 0 ≤ R) (hv : 0 < v) (t : ℝ) (ht : 0 < t) (hthreshold : v + R * t / 3 ≤ t ^ 2) :
    μ {ω | t < ‖∑ i ∈ s, Y i ω‖} ≤ bernsteinTail R v τ t :=
  measure_sum_norm_tail_le_of_finite_compressions μ U hmono hdense s Y hc hsa t
    (bernsteinTail R v τ t) (fun n ↦ hfinite n t hR hv ht hthreshold)

end JanetCartan.OperatorCompression
