module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Carrier
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.DerivativeBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.MaskedEstimates

/-!
# Fixed floor-one dyadic square partition for raw Euclidean input

The construction for `app:ch_waves:thm:individual`,
`app:ch_waves:eq:sampling-prefix-normal`, and `app:ch_background:defn:bg-mixed`
is assembled here. The fixed smooth bands have overlap at most two, uniform
rescaled derivatives, and exact square sum one on the complete floor-one
high-pass support. The literal rounded prefix retains precisely `κⱼ ≤ K`,
has plateau at least `K`, and vanishes above `4K`.

The wide-band complex Lebesgue inputs are isometrically identified with two
shared sharp annuli per band. Both quadratures and the literal norm are
preserved. Synthesis, the inverse-Fourier field, and every grouped prefix normal
are unchanged. The reassembled normal has the original smooth square prefix;
sharp indicators are used only for the measurable Hilbert decomposition.
The Fourier and Hilbert constants are independent of the number of scales.

The given detector and high-pass are never replaced. Their measurability,
boundedness and floor-one vanishing must be instantiated by raw-primary.
Smoothness of the radial masks does not assert smoothness or parity of the
detector. The raw tail `rawSquaredCutoff_rounded_tail` keeps both auxiliary
cutoffs at the original `K`; its weighted membership and weight domination
remain current-mean/adjoint inputs. The identification of that datum with the
actual raw adjoint, including its high-pass support, belongs to that producer.
The separate zero atom, phases, physical fields and continuum inverse are not
constructed or truncated by this partition.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RawInputPartition
open RawInputRealization RawInputHilbert

/-- Monotonicity of the literal band count, so all recurrence prefixes sit in
one full input fixed at the largest ceiling
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem cutoffCount_mono {K Λ : ℝ} (hK : 1 ≤ K) (hKL : K ≤ Λ) :
    cutoffCount K ≤ cutoffCount Λ := by
  by_contra h
  have hj := (lt_cutoffCount_iff hK (cutoffCount Λ)).mp (lt_of_not_ge h)
  have hf := (lt_cutoffCount_iff (hK.trans hKL) (cutoffCount Λ)).mpr (hj.trans hKL)
  exact (Nat.lt_irrefl _ hf)

/-- The rounded prefix keeps both sharp components of precisely the original
bands `κⱼ ≤ K`, on the same full finite input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem refinedPrefix_rounded_apply (n J : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (v : RefinedInput n J) (i : RefinedIndex J) :
    refinedPrefix n J (cutoffCount K) v i = if dyadicScale i.1.val ≤ K then v i else 0 := by
  simp only [refinedPrefix_apply, lt_cutoffCount_iff hK]

/-- The literal source high-pass and arbitrary, possibly non-even detector
supply floor-one support of their unchanged product
(`app:ch_background:defn:bg-row`). -/
theorem detector_highPass_floor {n : ℕ} (a : Euclidean (n - 1) → ℂ)
    (χ : Euclidean (n - 1) → ℝ) (hχ : ∀ η, ‖η‖ ≤ 1 → χ η = 0) :
    ∀ η, ‖η‖ ≤ 1 → a η * (χ η : ℂ) = 0 := by
  intro η hη
  simp [hχ η hη]

/-- Every rounded prefix normal on one full ceiling is multiplication by the
original detector square times the same `P_K²` used by the raw cutoff tail
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_background:defn:bg-mixed`). -/
theorem weightedRefinedSynthesis_rounded_normal_coeFn
    {n : ℕ} {K Λ : ℝ} (hK : 1 ≤ K) (hKL : K ≤ Λ)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (hfloor : ∀ η, ‖η‖ ≤ 1 → d η = 0) (f : Output n) :
    weightedRefinedSynthesis hd hM hb
      (refinedPrefix n (cutoffCount Λ) (cutoffCount K)
        ((weightedRefinedSynthesis hd hM hb).adjoint f)) =ᵐ[volume]
      fun η ↦ ((‖η‖ * (‖d η‖ ^ 2 * radialPrefix n (cutoffCount K) η ^ 2) : ℝ) : ℂ) * f η :=
  weightedRefinedSynthesis_prefix_normal_coeFn hd hM hb hfloor (cutoffCount_mono hK hKL) f

/-- For a raw carrier datum supported in the given floor-one high-pass, the
packaged multiplier square is literally the sum of the retained band squares.
This connects the unchanged raw cutoff with the sampled normal, including
frequencies between one and two (`app:ch_background:defn:bg-mixed`). -/
theorem roundedCarrierMask_sq_mul_eq_sum {n : ℕ} (K : ℝ)
    (h : ContinuumRow.CarrierVariable n → ℂ)
    (hs : ∀ᵐ x ∂ContinuumRow.carrierMeasure n, ‖x.2‖ ≤ 1 → h x = 0) :
    ∀ᵐ x ∂ContinuumRow.carrierMeasure n,
      (roundedCarrierMask n K x : ℂ) ^ 2 * h x =
        (∑ j ∈ Finset.range (cutoffCount K), (carrierBand n j x : ℂ) ^ 2) * h x := by
  filter_upwards [carrierPrefixMask_coeFn n (cutoffCount K), hs] with x hx hs
  change (carrierPrefixMask n (cutoffCount K) x : ℂ) ^ 2 * h x = _
  rw [hx]
  by_cases hlow : ‖x.2‖ ≤ 1
  · simp [hs hlow]
  · have he := sum_scalarBand_sq_eq_prefix_sq (cutoffCount K) (le_of_not_ge hlow)
    have hc := congrArg Complex.ofReal he
    push_cast at hc
    change (carrierPrefix n (cutoffCount K) x : ℂ) ^ 2 * h x = _
    exact congrArg (fun t : ℂ ↦ t * h x) hc.symm

end JanetCartan.RawInputPartition
