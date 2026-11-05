module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.SpatialFreezing.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.OperatorDifference.Algebra
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.AllData.Multipliers

/-!
# The scalar full-amplitude freezing error on all L² data

Construct the two-position Taylor operators from primitive amplitude bounds.
Exact compact-frequency kernels and strong exhaustion identify their sum with
the original operator. An output or source coordinate in each term gives the
support-radius factor in the bilinear form. The scalar constant precedes the
amplitude, density budget and support radius. Consumer: the matrix normal
estimate in `SpatialFreezing`; source: `app:ch_background:prop:bg-frame`, Step 3.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace NNReal Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.ActualConstruction
open Pseudodifferential AmplitudeBound
variable {n : ℕ}
local notation "E" => Euclidean n
local notation "P" => Euclidean (2 * n)

/-- Split the two-position Taylor sum into its literal output and source
coordinates (`app:ch_background:prop:bg-frame`, Step 3). -/
private theorem sum_pairedPosition_smul (c : Fin (2 * n) → ℂ) (x y : E) :
    (∑ j, pairedPosition x y j • c j) =
      (∑ i : Fin n, x i • c (physicalOutputIndex i)) +
        ∑ i : Fin n, y i • c (physicalSourceIndex i) := by
  let e : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
    finSumFinEquiv.trans (finCongr (by omega))
  have h := Fintype.sum_equiv e
    (fun i ↦ pairedPosition x y (e i) • c (e i))
    (fun j ↦ pairedPosition x y j • c j) (fun _ ↦ rfl)
  rw [Fintype.sum_sum_type] at h
  rw [← h]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [e, pairedPosition, physicalOutputIndex, Fin.castAdd, Fin.cast]
  · apply Finset.sum_congr rfl
    intro i _
    simp [e, pairedPosition, physicalSourceIndex, Fin.natAdd, Fin.cast]

section OperatorAlgebra
local notation "L²" => Lp ℂ 2 (volume : Measure E)
variable (hn : 0 < n) (R : ℝ)
  (b : Euclidean n → Euclidean (2 * n) → ℂ) (c : Bool → Fin n → Euclidean n → Euclidean (2 * n) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hc : ∀ s i, ContDiff ℝ ∞ (Function.uncurry (c s i)))
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
  (hcs : ∀ s i ξ, SupportedInCenteredBox R (c s i ξ))
  (B C : ℝ) (hB : HasAmplitudeDerivativeBound b (2 * (n + 1)) B)
  (hC : ∀ s i, HasAmplitudeDerivativeBound (c s i) (2 * (n + 1)) C)
  (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
  (heq : ∀ ξ x y, b ξ (pairedPosition x y) =
    (∑ i, (χ x * x i) • c false i ξ (pairedPosition x y)) +
      ∑ i, (χ y * y i) • c true i ξ (pairedPosition x y))

include hc heq in
/-- Finite frequency integration preserves the actual coordinate expansion,
with the existing Fourier normalization (`app:ch_background:prop:bg-frame`). -/
private theorem compactFrequencyAmplitudeKernel_eq_coordinate_sum (ρ : ℝ) (x y : E) :
    compactFrequencyAmplitudeKernel b ρ x y =
      (∑ i, (χ x * x i) • compactFrequencyAmplitudeKernel (c false i) ρ x y) +
        ∑ i, (χ y * y i) • compactFrequencyAmplitudeKernel (c true i) ρ x y := by
  have hi (s : Bool) (i : Fin n) : IntegrableOn (fun ξ : E ↦
      Complex.exp (↑(2 * Real.pi * inner ℝ (x - y) ξ) * Complex.I) *
        c s i ξ (pairedPosition x y)) (Metric.closedBall 0 ρ) := by
    apply ContinuousOn.integrableOn_compact (isCompact_closedBall 0 ρ)
    exact ((by fun_prop : Continuous (fun ξ : E ↦
      Complex.exp (↑(2 * Real.pi * inner ℝ (x - y) ξ) * Complex.I))).mul
      ((hc s i).continuous.comp (continuous_id.prodMk continuous_const))).continuousOn
  have his (s : Bool) (f : Fin n → ℝ) : IntegrableOn (fun ξ : E ↦ ∑ i,
      f i • (Complex.exp (↑(2 * Real.pi * inner ℝ (x - y) ξ) * Complex.I) *
        c s i ξ (pairedPosition x y))) (Metric.closedBall 0 ρ) :=
    integrable_finsetSum _ (fun i _ ↦ (hi s i).smul (f i))
  simp only [compactFrequencyAmplitudeKernel, heq, mul_add, Finset.mul_sum,
    mul_smul_comm]
  rw [integral_add (his false _) (his true _)]
  congr 1
  · simpa only [Pi.smul_apply, integral_smul] using
      integral_finsetSum Finset.univ (fun i _ ↦ (hi false i).smul (χ x * x i))
  · simpa only [Pi.smul_apply, integral_smul] using
      integral_finsetSum Finset.univ (fun i _ ↦ (hi true i).smul (χ y * y i))

include heq in
/-- The compact-frequency L² realization is the sum of the constructed
output- and source-coordinate operators. Every kernel integral is justified
from compact support (`app:ch_background:prop:bg-frame`, Step 3). -/
private theorem twoPositionCompactFrequencyL2Operator_eq_coordinate_sum
    (ρ : ℝ) (f : L²) :
    twoPositionCompactFrequencyL2Operator hn R b hb hs B hB ρ f =
      (∑ i, freezingCoordinateMultiplier χ hχ hχs i
        (twoPositionCompactFrequencyL2Operator hn R (c false i) (hc false i)
          (hcs false i) C (hC false i) ρ f)) +
      ∑ i, twoPositionCompactFrequencyL2Operator hn R (c true i) (hc true i)
        (hcs true i) C (hC true i) ρ (freezingCoordinateMultiplier χ hχ hχs i f) := by
  let X := freezingCoordinateMultiplier χ hχ hχs
  let T := fun s i ↦ twoPositionCompactFrequencyL2Operator hn R (c s i) (hc s i)
    (hcs s i) C (hC s i) ρ
  have hsource (i : Fin n) (x : E) :
      (∫ y, compactFrequencyAmplitudeKernel (c true i) ρ x y * X i f y) =
        ∫ y, (χ y * y i) • (compactFrequencyAmplitudeKernel (c true i) ρ x y * f y) := by
    apply integral_congr_ae
    filter_upwards [freezingCoordinateMultiplier_coeFn χ hχ hχs i f] with y hy
    rw [hy, mul_smul_comm]
  dsimp only [X] at hsource
  have hi (i : Fin n) (x : E) : Integrable (fun y ↦
      (χ y * y i) • (compactFrequencyAmplitudeKernel (c true i) ρ x y * f y)) :=
    (integrable_compactKernel_mul_L2
      (continuous_compactFrequencyAmplitudeKernel (hc true i).continuous ρ)
      (hasCompactSupport_compactFrequencyAmplitudeKernel (hcs true i) ρ) (X i f) x).congr
        ((freezingCoordinateMultiplier_coeFn χ hχ hχs i f).mono
          (fun y hy ↦ by dsimp only [X]; rw [hy, mul_smul_comm]))
  have ho (i : Fin n) (x : E) : Integrable (fun y ↦
      (χ x * x i) • (compactFrequencyAmplitudeKernel (c false i) ρ x y * f y)) :=
    (integrable_compactKernel_mul_L2
      (continuous_compactFrequencyAmplitudeKernel (hc false i).continuous ρ)
      (hasCompactSupport_compactFrequencyAmplitudeKernel (hcs false i) ρ) f x).smul (χ x * x i)
  apply Lp.ext
  filter_upwards [twoPositionCompactFrequencyL2Operator_ae_kernel hn R b hb hs B hB ρ f,
    Lp.coeFn_add (∑ i, X i (T false i f)) (∑ i, T true i (X i f)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ X i (T false i f)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ T true i (X i f)),
    ae_all_iff.mpr (fun i ↦ freezingCoordinateMultiplier_coeFn χ hχ hχs i (T false i f)),
    ae_all_iff.mpr (fun i ↦ twoPositionCompactFrequencyL2Operator_ae_kernel hn R
      (c false i) (hc false i) (hcs false i) C (hC false i) ρ f),
    ae_all_iff.mpr (fun i ↦ twoPositionCompactFrequencyL2Operator_ae_kernel hn R
      (c true i) (hc true i) (hcs true i) C (hC true i) ρ (X i f))]
    with x hx hadd hsumo hsums hX hTo hTs
  change _ = ((∑ i, X i (T false i f)) + ∑ i, T true i (X i f)) x
  rw [hx, hadd, Pi.add_apply, hsumo, hsums]
  simp only [X, T] at hX hTo hTs ⊢
  simp only [hX, hTo, hTs, hsource]
  simp_rw [compactFrequencyAmplitudeKernel_eq_coordinate_sum b c hc χ heq,
    add_mul, Finset.sum_mul, smul_mul_assoc]
  rw [integral_add (integrable_finsetSum _ (fun i _ ↦ ho i x))
    (integrable_finsetSum _ (fun i _ ↦ hi i x)),
    integral_finsetSum _ (fun i _ ↦ ho i x),
    integral_finsetSum _ (fun i _ ↦ hi i x)]
  simp only [integral_smul]

include heq in
/-- Strong frequency exhaustion gives the exact coordinate decomposition on
all L² data, using the original full-amplitude operators
(`app:ch_background:prop:bg-frame`, Step 3). -/
private theorem twoPositionL2Operator_eq_coordinate_sum (f : L²) :
    twoPositionL2Operator hn R b hb hs B hB f =
      (∑ i, freezingCoordinateMultiplier χ hχ hχs i
        (twoPositionL2Operator hn R (c false i) (hc false i)
          (hcs false i) C (hC false i) f)) +
      ∑ i, twoPositionL2Operator hn R (c true i) (hc true i)
        (hcs true i) C (hC true i) (freezingCoordinateMultiplier χ hχ hχs i f) := by
  apply tendsto_nhds_unique
    (tendsto_twoPositionCompactFrequencyL2Operator hn R b hb hs B hB f)
  have ho : ∀ i, Tendsto (fun ρ : ℝ ↦ freezingCoordinateMultiplier χ hχ hχs i
      (twoPositionCompactFrequencyL2Operator hn R (c false i) (hc false i)
        (hcs false i) C (hC false i) ρ f)) atTop
      (𝓝 (freezingCoordinateMultiplier χ hχ hχs i
        (twoPositionL2Operator hn R (c false i) (hc false i)
          (hcs false i) C (hC false i) f))) := fun i ↦
    (freezingCoordinateMultiplier χ hχ hχs i).continuous.continuousAt.tendsto.comp
      (tendsto_twoPositionCompactFrequencyL2Operator hn R (c false i) (hc false i)
        (hcs false i) C (hC false i) f)
  have hsource := fun i ↦ tendsto_twoPositionCompactFrequencyL2Operator hn R
    (c true i) (hc true i) (hcs true i) C (hC true i)
      (freezingCoordinateMultiplier χ hχ hχs i f)
  exact ((tendsto_finsetSum _ (fun i _ ↦ ho i)).add
    (tendsto_finsetSum _ (fun i _ ↦ hsource i))).congr
      (fun ρ ↦ (twoPositionCompactFrequencyL2Operator_eq_coordinate_sum hn R b c
        hb hc hs hcs B C hB hC χ hχ hχs heq ρ f).symm)
include heq hc hcs hC hχ hχs in
/-- Move each output coordinate to the supported test and retain each source
coordinate on the supported datum (`app:ch_background:prop:bg-frame`, Step 3). -/
private theorem abs_inner_twoPositionL2Operator_coordinate_sum_le
    (hC0 : 0 ≤ C) {r : ℝ} (_hr : 0 ≤ r)
    (hplateau : ∀ x ∈ Metric.closedBall (0 : E) r, χ x = 1)
    (f g : L²)
    (hf : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → f x = 0)
    (hg : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → g x = 0) :
    |inner ℝ (twoPositionL2Operator hn R b hb hs B hB f) g| ≤
      (2 * (n : ℝ) * (fixedBoxAmplitudeConstant n R * C)) * r * ‖f‖ * ‖g‖ := by
  let X := freezingCoordinateMultiplier χ hχ hχs
  let T := fun s i ↦ twoPositionL2Operator hn R (c s i) (hc s i) (hcs s i) C (hC s i)
  let K := fixedBoxAmplitudeConstant n R * C
  have hK : 0 ≤ K := mul_nonneg (fixedBoxAmplitudeConstant_nonneg _ _) hC0
  have hXnorm (u : L²)
      (hu : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → u x = 0) (i : Fin n) :
      ‖X i u‖ ≤ r * ‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [freezingCoordinateMultiplier_coeFn χ hχ hχs i u, hu] with x hx hu
    rw [hx]
    by_cases hxball : x ∈ Metric.closedBall (0 : E) r
    · rw [hplateau x hxball, one_mul, norm_smul]
      exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le x i).trans
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxball)) (norm_nonneg _)
    · simp [hu hxball]
  have hsym (i : Fin n) (u v : L²) : inner ℝ (X i u) v = inner ℝ u (X i v) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [freezingCoordinateMultiplier_coeFn χ hχ hχs i u,
      freezingCoordinateMultiplier_coeFn χ hχ hχs i v] with x hu hv
    rw [hu, hv, real_inner_smul_left, real_inner_smul_right]
  have hTnorm (s : Bool) (i : Fin n) (u : L²) : ‖T s i u‖ ≤ K * ‖u‖ :=
    norm_twoPositionL2Operator_apply_le hn R _ _ _ C (hC s i) u
  have hout (i : Fin n) : |inner ℝ (X i (T false i f)) g| ≤ K * r * ‖f‖ * ‖g‖ := by
    rw [hsym]
    calc
      _ ≤ ‖T false i f‖ * ‖X i g‖ := abs_real_inner_le_norm _ _
      _ ≤ (K * ‖f‖) * (r * ‖g‖) :=
        mul_le_mul (hTnorm false i f) (hXnorm g hg i) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hsource (i : Fin n) : |inner ℝ (T true i (X i f)) g| ≤ K * r * ‖f‖ * ‖g‖ := by
    calc
      _ ≤ ‖T true i (X i f)‖ * ‖g‖ := abs_real_inner_le_norm _ _
      _ ≤ (K * (r * ‖f‖)) * ‖g‖ := by
        gcongr
        exact (hTnorm true i (X i f)).trans
          (mul_le_mul_of_nonneg_left (hXnorm f hf i) hK)
      _ = _ := by ring
  rw [twoPositionL2Operator_eq_coordinate_sum hn R b c hb hc hs hcs B C hB hC
    χ hχ hχs heq f, inner_add_left, sum_inner, sum_inner]
  calc
    _ ≤ (∑ i, |inner ℝ (X i (T false i f)) g|) +
        ∑ i, |inner ℝ (T true i (X i f)) g| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
        (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (∑ _ : Fin n, K * r * ‖f‖ * ‖g‖) +
        ∑ _ : Fin n, K * r * ‖f‖ * ‖g‖ :=
      add_le_add (Finset.sum_le_sum (fun i _ ↦ hout i))
        (Finset.sum_le_sum (fun i _ ↦ hsource i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
end OperatorAlgebra

/-- The actual full-amplitude Taylor error is bounded by the support radius
times the displayed primitive budget. All coefficient operators and their
bounds have been constructed (`app:ch_background:prop:bg-frame`, Step 3). -/
private theorem abs_inner_twoPositionL2Operator_of_zero_at_origin_le
    (hn : 0 < n) (R : ℝ) (b : E → P → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ))
    (A : ℝ) (hA : HasAmplitudeDerivativeBound b (2 * (n + 1)) A)
    (hzero : ∀ ξ, b ξ 0 = 0)
    (θ : P → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθbox : ∀ z, θ z ≠ 0 → ∀ j, |z j| ≤ R)
    (hθb : ∀ ξ z, b ξ z ≠ 0 → θ z = 1)
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχθ : ∀ x y, θ (pairedPosition x y) ≠ 0 → χ x = 1 ∧ χ y = 1)
    (B M : ℝ≥0)
    (hB : ∀ k ≤ 2 * (n + 1), ∀ z, ‖iteratedFDeriv ℝ k θ z‖ ≤ B)
    (hM : ∀ ξ k, k ≤ 2 * (n + 1) + 1 → ∀ z, ‖iteratedFDeriv ℝ k (b ξ) z‖ ≤ M)
    {r : ℝ} (hr : 0 ≤ r)
    (hplateau : ∀ x ∈ Metric.closedBall (0 : E) r, χ x = 1)
    (f g : Lp ℂ 2 (volume : Measure E))
    (hf : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → f x = 0)
    (hg : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → g x = 0) :
    |inner ℝ (twoPositionL2Operator hn R b hb hs A hA f) g| ≤
      (2 * (n : ℝ) * (fixedBoxAmplitudeConstant n R *
        fullPositionTaylorBudget B M (2 * (n + 1)))) * r * ‖f‖ * ‖g‖ := by
  let c := fun (s : Bool) (i : Fin n) ↦ maskedFullPositionTaylorAmplitude b θ
    (if s then physicalSourceIndex i else physicalOutputIndex i)
  have hc : ∀ s i, ContDiff ℝ ∞ (Function.uncurry (c s i)) :=
    fun s i ↦ contDiff_maskedFullPositionTaylorAmplitude b θ hb hθ _
  have hcs : ∀ s i ξ, SupportedInCenteredBox R (c s i ξ) :=
    fun s i ξ ↦ supportedInCenteredBox_maskedFullPositionTaylorAmplitude b θ R hθbox _ ξ
  have hC : ∀ s i, HasAmplitudeDerivativeBound (c s i) (2 * (n + 1))
      (fullPositionTaylorBudget B M (2 * (n + 1))) := fun s i ↦
    hasAmplitudeDerivativeBound_maskedFullPositionTaylorAmplitude b θ hb hθ B M _ hB hM _
  have heq (ξ x y : E) : b ξ (pairedPosition x y) =
      (∑ i, (χ x * x i) • c false i ξ (pairedPosition x y)) +
        ∑ i, (χ y * y i) • c true i ξ (pairedPosition x y) := by
    rw [fullAmplitude_eq_sum_maskedFullPositionTaylorAmplitude b θ
      (fun ξ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hzero hθb,
      sum_pairedPosition_smul]
    by_cases ht : θ (pairedPosition x y) = 0
    · simp [c, maskedFullPositionTaylorAmplitude, ht]
    · rw [(hχθ x y ht).1, (hχθ x y ht).2]
      simp only [one_mul, c, Bool.false_eq_true, ↓reduceIte]
  exact abs_inner_twoPositionL2Operator_coordinate_sum_le hn R b c hb hc hs hcs A
    (fullPositionTaylorBudget B M (2 * (n + 1))) hA hC χ hχ hχs heq
    (by unfold fullPositionTaylorBudget; positivity) hr hplateau f g hf hg

/-- One scalar freezing constant precedes the amplitude, its derivative
budget, and the support radius. The only quantitative input on the amplitude
is the EXISTING coordinate derivative interface through `2 * (n + 1) + 1`.
Consumer: matrix normal freezing and the transported-density reference bridge
(`app:ch_background:prop:bg-frame`, Step 3; `bg-local-bound`). -/
theorem exists_scalar_fullAmplitude_small_support_constant
    (hn : 0 < n) (R : ℝ) (θ : P → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθs : HasCompactSupport θ) (hθbox : ∀ z, θ z ≠ 0 → ∀ j, |z j| ≤ R)
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχθ : ∀ x y, θ (pairedPosition x y) ≠ 0 → χ x = 1 ∧ χ y = 1) :
    ∃ C > 0, ∀ (b : E → P → ℂ) (hb : ContDiff ℝ ∞ (Function.uncurry b))
      (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ≥0)
      (hA : HasAmplitudeDerivativeBound b (2 * (n + 1) + 1) A),
      (∀ ξ, b ξ 0 = 0) → (∀ ξ z, b ξ z ≠ 0 → θ z = 1) →
      ∀ r : ℝ, 0 ≤ r → (∀ x ∈ Metric.closedBall (0 : E) r, χ x = 1) →
      ∀ (f g : Lp ℂ 2 (volume : Measure E)),
      (∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → f x = 0) →
      (∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → g x = 0) →
      |inner ℝ (twoPositionL2Operator hn R b hb hs A
        (fun ξ is his ↦ hA ξ is (by omega)) f) g| ≤ C * A * r * ‖f‖ * ‖g‖ := by
  obtain ⟨B, hB0, hB⟩ := hθs.exists_bound_iteratedFDeriv hθ (2 * (n + 1))
  let B' : ℝ≥0 := ⟨B, hB0⟩
  let D : ℝ≥0 := ((2 * n + 1 : ℕ) : ℝ≥0) ^ (2 * (n + 1) + 1)
  let K := fullPositionTaylorBudget B' D (2 * (n + 1))
  let C := 2 * (n : ℝ) * (fixedBoxAmplitudeConstant n R * K)
  have hK : 0 ≤ K := by unfold K fullPositionTaylorBudget; positivity
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (mul_nonneg (fixedBoxAmplitudeConstant_nonneg _ _) hK)
  refine ⟨C + 1, by linarith, ?_⟩
  intro b hb hs A hA hzero hmask r hr hplateau f g hf hg
  have hM (ξ : E) (k : ℕ) (hk : k ≤ 2 * (n + 1) + 1) (z : P) :
      ‖iteratedFDeriv ℝ k (b ξ) z‖ ≤ (D * A : ℝ≥0) := by
    apply (norm_iteratedFDeriv_le_amplitudeBudget
      (fun ξ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hA ξ hk z).trans
    apply mul_le_mul_of_nonneg_right _ A.coe_nonneg
    calc
      ((2 * n : ℕ) : ℝ) ^ k ≤ ((2 * n + 1 : ℕ) : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity) (by norm_cast; omega) k
      _ ≤ _ := by
        simp only [D]
        exact pow_le_pow_right₀ (by norm_cast; omega) hk
  have hbudget : fullPositionTaylorBudget B' (D * A) (2 * (n + 1)) = K * A := by
    simp only [fullPositionTaylorBudget, K, NNReal.coe_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he := abs_inner_twoPositionL2Operator_of_zero_at_origin_le hn R b hb hs A
    (fun ξ is his ↦ hA ξ is (by omega)) hzero θ hθ hθbox hmask χ hχ hχs hχθ
    B' (D * A) hB hM hr hplateau f g hf hg
  rw [hbudget] at he
  calc
    _ ≤ C * A * r * ‖f‖ * ‖g‖ := by simpa only [C, mul_assoc] using he
    _ ≤ _ := by gcongr; linarith

end JanetCartan.ContinuumNormal.ActualConstruction
