module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.PhysicalMean
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.InitialLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparationTransportPrimitives.Characteristic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean.Fields

/-!
# The corrected positive scalar in the same retained physical mean

The actual characteristic formula and Hamilton conservation identify the
normal obtained from `σ * sqrt (1+v)` with the square-root multiple of the
uncorrected normal. Thus the affine tensor mean used by physical cancellation
is literally the mean of the corrected retained scalar. The original ODE
footpoint, Hamilton family, selected minor, weights and measure are unchanged.

This is the scalar/mean identification required before the wider-density
coercivity theorem can be applied and the corrected positive inverse fixed.
It does not assert that positivity by itself proves that coercivity theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PositiveBackground
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier ContinuumAdjoint.Canonical
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedChartMean
open CurrentMean.PreparationTransportPrimitives NormalizedBackground

/-- The SAME retained normal with corrected initial scalar `σ sqrt(1+v)` is
the square-root multiple of its uncorrected normal. The ODE/Hamilton footpoint
identity is proved from the chart and the original coefficient-domain buffer,
not assumed as a matching premise (`app:ch_background:eq:bg-affine-mean`,
`app:ch_background:eq:bg-density-four`, `app:ch_background:prop:bg-positive`). -/
theorem retained_normal_positiveDensityAmplitude
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : PatchQuantitativeFamily P U hU}
    {Ω Kc : Set (Euclidean n × Euclidean 3)}
    {p₀ : Euclidean (n - 1) × Euclidean 3} {Rc M τ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N}
    (c : Chart T Ω Kc p₀ Rc M τ row col F) {cP CP : ℝ} (hP : P.IsValid cP CP)
    (hF : ContDiffOn ℝ ∞ F U) (hrank : HasFullNormalRankOn F U)
    {K : Set (Euclidean n)} (hKU : K ⊆ U) (hτ : 0 < τ)
    (hΩ : Ω ⊆ (ball 0 T.physicalRadius ∩ interior K) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (σ : ℝ) (v : CarrierVariable n → ℝ)
    {p : Euclidean n × CarrierParameter} (hp : densityCoordinates T p ∈ c.D) :
    c.normal (fun q ↦ positiveDensityAmplitude σ (densityOnInitialLabels v q)) p =
      Real.sqrt (1 + v (p.2, transportPosition T c.Q p)) • c.normal (fun _ ↦ σ) p := by
  have hgeom : coordinates (adaptedCoordinates T.data.adapted) ⁻¹' c.D ⊆
      (ball 0 T.physicalRadius ∩ interior K) ×ˢ parameterInterior (3 * P.radius / 2) := by
    intro q hq
    have hh := c.domain_coefficients hq
    have hqΩ : q ∈ Ω := by
      simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hh
    exact hΩ hqΩ
  have hfoot := retainedChart_footpoint_eq c hP hF hrank hKU hτ hgeom hp
  change normalField T c.Q F row col c.forward c.inverse _ p.1 p.2 =
    _ • normalField T c.Q F row col c.forward c.inverse _ p.1 p.2
  rw [normalField_eq_initial_flow, normalField_eq_initial_flow, hfoot]
  have hlabel : densityOnInitialLabels v (transportPosition T c.Q p, parameter p.2) =
      v (p.2, transportPosition T c.Q p) :=
    congrFun (initialScalar_densityOnInitialLabels v) (p.2, transportPosition T c.Q p)
  simp only [hlabel, positiveDensityAmplitude, smul_smul]
  congr 1
  ring

/-- The literal affine physical mean is exactly the mean of the SAME
retained positive initial scalars. The full external support is used for the
characteristic identification; outside it the original weight vanishes.
This is the missing scalar interpretation of the tensor cancelled by
`physicalDensityMean_uncorrected_core_cancellation`
(`app:ch_background:eq:bg-affine-mean`, `app:ch_background:eq:bg-current-identity`). -/
theorem physicalDensityMean_eq_retained_positive_mean
    {n N : ℕ} {A : Type} [Fintype A]
    {P : A → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    {T : (a : A) → PatchQuantitativeFamily (P a) U hU}
    {Ω Kc : A → Set (Euclidean n × Euclidean 3)}
    {p₀ : A → Euclidean (n - 1) × Euclidean 3}
    {Rc M τ : A → ℝ} {row col : A → Fin n} {F : Euclidean n → Euclidean N}
    (c : (a : A) → Chart (T a) (Ω a) (Kc a) (p₀ a)
      (Rc a) (M a) (τ a) (row a) (col a) F)
    {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP)
    (hF : ContDiffOn ℝ ∞ F U) (hrank : HasFullNormalRankOn F U)
    {K : Set (Euclidean n)} (hKU : K ⊆ U) (hτ : ∀ a, 0 < τ a)
    (hΩ : ∀ a, Ω a ⊆ (ball 0 (T a).physicalRadius ∩ interior K) ×ˢ
      parameterInterior (3 * (P a).radius / 2))
    (σ : ℝ) (χ : A → CarrierParameter → ℝ) (v : A → CarrierVariable n → ℝ)
    (hv : ∀ a p, 0 ≤ 1 + v a p)
    {W : Set (Euclidean n)}
    (hflow : ∀ a, MapsTo (densityCoordinates (T a)) (W ×ˢ tsupport (χ a)) (c a).D)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : A → CarrierParameter → Euclidean (n - 1) → ℝ) (high : A → ℝ → ℝ) :
    EqOn (physicalDensityMean (fun a ↦ data (T a) (c a).Q F (row a) (col a)
      (c a).forward (c a).inverse (fun _ ↦ σ) hr hcell (angular a) (high a)) χ v)
      (carrierMean (fun _ ↦ volume.prod volume) (fun a z ↦ χ a z ^ 2)
        (fun a ↦ (c a).normal (fun q ↦ positiveDensityAmplitude σ (densityOnInitialLabels (v a) q)))
        (fun a ↦ covector (c a))) W := by
  intro x hx
  unfold physicalDensityMean carrierMean
  apply Finset.sum_congr rfl
  intro a _
  ext i j
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport (χ a)
  · rw [retained_normal_positiveDensityAmplitude (c a) (hP a) hF hrank hKU (hτ a)
      (hΩ a) σ (v a) (hflow a ⟨hx, hz⟩)]
    change (χ a z ^ 2 * (1 + v a (z, transportPosition (T a) (c a).Q (x, z)))) *
        ‖(c a).normal (fun _ ↦ σ) (x, z)‖ ^ 2 *
          (covector (c a) (x, z) i * covector (c a) (x, z) j) = _
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hv a _)]
    ring
  · simp only [image_eq_zero_of_notMem_tsupport hz, zero_pow (by decide : 2 ≠ 0), zero_mul]

end JanetCartan.PositiveBackground
