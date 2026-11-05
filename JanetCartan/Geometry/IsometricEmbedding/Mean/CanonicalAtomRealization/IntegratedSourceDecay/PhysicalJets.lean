module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WeakDerivatives.IntegralJets

/-!
# Physical jets of the same canonical Fourier integral

The primary Sobolev profile in `main:thm:step` uses derivatives of the final
physical wave. Differentiate the actual finite-band integral, then accumulate
its unchanged Fourier densities. The number of canonical updates does not enter
the resulting mass estimate.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.CanonicalAtomRealization
open RawPrimary RawInputPartition

variable {n N J : ℕ}
    {O : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hO : IsOpen O) (hV : IsOpen V)
    (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {A : Euclidean n × Euclidean (n - 1) → EuclideanSpace ℂ (Fin N)}
    (hA : ContDiffOn ℝ ∞ A (O ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)

include hO hV hceil hA hd hM hb in
/-- The actual physical jet of a raw Hilbert integral is the integral of the
SAME atomic jets, with the original density and frequency window. This applies
to the full corrected displacement before cutoff (`main:eq:joint-physical-profile`,
`app:ch_lag:eq:lag-recurrence`). -/
theorem iteratedFDeriv_wideSuperposition_eq_integral (q : ℕ)
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ O) :
    iteratedFDeriv ℝ q (wideSuperposition A d v) x =
      ∫ η, weightedWideDensity d v η • iteratedFDeriv ℝ q (fun y ↦ A (y, η)) x := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euclidean (n - 1))
      ((2 : ℝ) ^ J))) := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall _ _).measure_lt_top.ne
  have he := iteratedFDeriv_weightedCompactIntegral hO hV
    (isCompact_closedBall _ _) hceil (integrable_wideDensity hd hM hb v).integrableOn
    hA q hx
  change iteratedFDeriv ℝ q (fun y ↦ wideSuperposition A d v y) x =
    wideSuperposition (fun z ↦ iteratedFDeriv ℝ q (fun y ↦ A (y, z.2)) z.1) d v x
  simpa only [wideSuperposition_eq_compact] using he

include hO hV hceil hA hd hM hb in
/-- A uniform physical atomic jet estimate integrates with the literal Fourier
L¹ mass, without a loss depending on the band count
(`main:eq:joint-physical-profile`, `main:eq:variation`). -/
theorem norm_iteratedFDeriv_wideSuperposition_le_integral (q : ℕ)
    (v : WideInput n J) {x : Euclidean n} (hx : x ∈ O) {C : ℝ}
    (hbound : ∀ η ∈ Metric.closedBall 0 ((2 : ℝ) ^ J),
      ‖iteratedFDeriv ℝ q (fun y ↦ A (y, η)) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ q (wideSuperposition A d v) x‖ ≤
      C * ∫ η, ‖weightedWideDensity d v η‖ := by
  rw [iteratedFDeriv_wideSuperposition_eq_integral hO hV hceil hA hd hM hb q v hx]
  calc
    _ ≤ ∫ η, C * ‖weightedWideDensity d v η‖ := by
      apply norm_integral_le_of_norm_le ((integrable_wideDensity hd hM hb v).norm.const_mul C)
      filter_upwards [] with η
      by_cases hη : η ∈ Metric.closedBall 0 ((2 : ℝ) ^ J)
      · rw [norm_smul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hbound η hη) (norm_nonneg _)
      · rw [wideDensity_eq_zero_of_ceiling_le d v
          (le_of_lt (by simpa using hη))]
        simp
    _ = _ := integral_const_mul _ _

include hO hV hA hd hM hb in
/-- Every fixed physical derivative of the zero atom plus the canonical run
is bounded by the original zero-atom jet and the actual accumulated Fourier
masses. This is the finite synthesis input to the primary periodic Sobolev
profile (`main:eq:joint-physical-profile`, `main:eq:variation`). -/
theorem norm_iteratedFDeriv_add_sum_wideSuperposition_le {κ : Type*}
    (s : Finset κ) (Jidx : κ → ℕ) (v : (l : κ) → WideInput n (Jidx l))
    (hceilEach : ∀ l ∈ s, Metric.closedBall 0 ((2 : ℝ) ^ Jidx l) ⊆ V)
    (Z₀ : Euclidean n → EuclideanSpace ℂ (Fin N)) (q : ℕ)
    {x : Euclidean n} (hx : x ∈ O)
    (hZ₀ : ContDiffAt ℝ q Z₀ x) {C₀ C : ℝ}
    (hzero : ‖iteratedFDeriv ℝ q Z₀ x‖ ≤ C₀)
    (hatom : ∀ l ∈ s, ∀ η ∈ Metric.closedBall 0 ((2 : ℝ) ^ Jidx l),
      ‖iteratedFDeriv ℝ q (fun y ↦ A (y, η)) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ q (Z₀ + ∑ l ∈ s, wideSuperposition A d (v l)) x‖ ≤
      C₀ + C * ∑ l ∈ s, ∫ η, ‖weightedWideDensity d (v l) η‖ := by
  have hreg (l : κ) (hl : l ∈ s) : ContDiffAt ℝ q (wideSuperposition A d (v l)) x :=
    ((contDiffOn_wideSuperposition hO hV (hceilEach l hl) hA hd hM hb (v l)).contDiffAt
      (hO.mem_nhds hx)).of_le (by simp)
  have hsum : ContDiffAt ℝ q (∑ l ∈ s, wideSuperposition A d (v l)) x := by
    simpa only [← Finset.sum_apply] using ContDiffAt.sum hreg
  rw [iteratedFDeriv_add_apply hZ₀ hsum, iteratedFDeriv_sum_apply hreg]
  calc
    _ ≤ ‖iteratedFDeriv ℝ q Z₀ x‖ +
        ∑ l ∈ s, ‖iteratedFDeriv ℝ q (wideSuperposition A d (v l)) x‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ C₀ + ∑ l ∈ s, C * ∫ η, ‖weightedWideDensity d (v l) η‖ := by
      apply add_le_add hzero
      exact Finset.sum_le_sum fun l hl ↦
        norm_iteratedFDeriv_wideSuperposition_le_integral hO hV (hceilEach l hl)
          hA hd hM hb q (v l) hx (hatom l hl)
    _ = _ := by rw [Finset.mul_sum]

end JanetCartan.CanonicalAtomRealization
