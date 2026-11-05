module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.MeasuredData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCharts

/-!
# The common measured data of a supplied normalized retained family

Instantiate the measurement producer on the original finite radii and on the
same seed charts. Image coefficients are constructed from the same reference
that defines the normalized carrier data. The radius, all masks and the image
jet constants precede scale. The normal identity retains the exterior square.
The bounded carrier realizations and their uniform analytic estimates still
have to be supplied by the normalized carrier and adjoint producers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedSelection

open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open CommonMeasurement GeometricProfile AmplitudeBound
open ContinuumNormal.FrozenModel
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction

/-- Construct the image/carrier/exterior DATA on one common measurement
chart from the supplied original retained charts. The scale-dependent image
coefficients are literal coefficients of `sourceDilation H.map σ`; the same
`H.map` defines every normalized carrier. No independently selected row is
identified with these data. All fixed masks and image constants precede scale.

The last clauses carry the supplied local bounded realizations into these
data, retaining both literal integrals and the exterior `(1 - ψ)^2`. They
do not assert the missing uniform carrier or inverse estimates. The scalar
support cap can be imposed through `b` before this construction
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-normalized`,
`new:sec:order-of-choices`). -/
theorem exists_common_measured_normalized_data
    {n : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (H : FlatReference n) (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    (Ω K : ι → Set (Euclidean n × Euclidean 3))
    (p₀ : ι → Euclidean (n - 1) × Euclidean 3) (Rc B τ : ι → ℝ)
    (row col : ι → Fin n)
    (seed : (i : ι) → Chart (T i) (Ω i) (K i) (p₀ i) (Rc i) (B i) (τ i)
      (row i) (col i) H.map)
    (initial : ι → Euclidean (n - 1) × Euclidean 3 → ℝ)
    (a' : ι → ℝ) (ha' : ∀ i, 0 < a' i) (hlocal : ∀ i, 4 * a' i < 1 / 2)
    (zRoot : ι → Euclidean 3) (η₀ : ι → Euclidean (n - 1))
    (width : ι → ℝ) (hwidth : ∀ i, 0 < width i)
    {b R : ℝ} (hb : 0 < b) (hR : 0 < R) :
    ∃ (r : ℝ) (hr : 0 < r) (hcell : 4 * r < 1 / 2),
      6 * r < b ∧ 6 * r < R ∧ 6 * r < 1 / 2 ∧ (∀ i, 6 * r < a' i) ∧
    ∃ χcoeff : Euclidean n → ℝ,
      ContDiff ℝ ∞ χcoeff ∧ (∀ x, χcoeff x ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χcoeff ∧ tsupport χcoeff ⊆ ball 0 (5 * r) ∧
      closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1} ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ (coeff : ℝ → ReducedCoefficientIndex n → C(Torus n, ℝ)) (C : ℕ → ℝ),
      (∀ m, 0 < C m) ∧
      (∀ σ j, IsSmoothPeriodic (coeff σ j)) ∧
      (∀ j z, coeff 0 j z = χcoeff (centeredTorusRepresentative z) *
        ProtectedFlow.reducedCoefficientBackground (fun _ _ ↦ 0)
          (centeredTorusRepresentative z) j) ∧
      (∀ σ ∈ Ioc (0 : ℝ) σ₀, ∀ j z,
        coeff σ j z = χcoeff (centeredTorusRepresentative z) *
          geometricReducedCoefficients (sourceDilation H.map σ)
            (centeredTorusRepresentative z) j) ∧
      (∀ m σ, σ ∈ Ioc (0 : ℝ) σ₀ → ∀ j x,
        ‖iteratedFDeriv ℝ m (periodicLift (coeff σ j - coeff 0 j)) x‖ ≤ C m * σ ∧
        ‖iteratedFDeriv ℝ m (periodicLift (coeff σ j)) x‖ ≤ C m) ∧
    let χ := FixedCutoffs.periodic (n := n) hr hcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hr hcell 2
    let ψ := FixedCutoffs.periodic (n := n) hr hcell 0
    let angular := fun i ↦ angularMask (zRoot i) (η₀ i) (ha' i) (hwidth i)
    let localData := fun σ i ↦ normalizedCarrierData (T i) (seed i).Q H.map
      (row i) (col i) (seed i).forward (seed i).inverse (initial i)
      (ha' i) (hlocal i) (angular i) FixedCutoffs.highFrequency σ
    let d := fun σ i ↦ normalizedCarrierData (T i) (seed i).Q H.map
      (row i) (col i) (seed i).forward (seed i).inverse (initial i)
      hr hcell (angular i) FixedCutoffs.highFrequency σ
    (∀ σ i, (d σ i).angularCutoff = angular i ∧
      (d σ i).highCutoff = FixedCutoffs.highFrequency ∧
      d σ i = commonChartData (localData σ i) (closedBall 0 (4 * r)) χ) ∧
    ∀ (σ : ℝ) (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      (∀ i, ‖restrictCarrier χ (V i)‖ ≤ ‖V i‖) ∧
      (∀ i, (∀ v : carrierInitialTestSpace n,
          V i (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (localData σ i) v.val) →
        ∀ v : carrierInitialTestSpace n,
          restrictCarrier χ (V i) (carrierInitialTestToLp v) =ᵐ[volume]
            carrierTestIntegral (d σ i) v.val) ∧
      (∀ i, (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral (localData σ i) w) 2 (carrierMeasure n) ∧
          (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (localData σ i) w) →
        ∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral (d σ i) w) 2 (carrierMeasure n) ∧
          (restrictCarrier χ (V i)).adjoint w =ᵐ[carrierMeasure n]
            carrierAdjointIntegral (d σ i) w) ∧
      augmentedNormal (imageChannel (coeff σ) χ χsrc) (fun i ↦ restrictCarrier χ (V i)) ψ =
        imageChannel (coeff σ) χ χsrc ∘L (imageChannel (coeff σ) χ χsrc).adjoint +
          (∑ i, cutoffMultiplier χ ∘L
            (carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint) ∘L cutoffMultiplier χ) +
          cutoffMultiplier ((1 - ψ) ^ 2) := by
  classical
  obtain ⟨r, hr, hcell, hrb, hrR, hrhalf, hra, χcoeff, hχ, hχrange, hχcompact,
    hχsupport, hχplateau, hmeasurement⟩ :=
    NormalizedMeasurement.exists_supplied_family_normalized_measurement
      (n := n) (N := embeddingDimension n) a' ha' zRoot η₀ width hwidth hb hR
  obtain ⟨_, _, _, _, _, himage⟩ := hmeasurement
  obtain ⟨σ₀, hσ₀, hσ₁, c₀, c, C, hC, hformula₀, hc₀, _, hformula, hc, _,
    hbounds, _, _⟩ := himage H
  let coeff := fun σ ↦ if hσ : σ ∈ Ioc (0 : ℝ) σ₀ then c σ hσ else c₀
  have hcoeff (σ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : coeff σ = c σ hσ := dite_eq_left hσ
  have hzero : coeff 0 = c₀ := dite_eq_right (by simp)
  refine ⟨r, hr, hcell, hrb, hrR, hrhalf, hra, χcoeff, hχ, hχrange, hχcompact,
    hχsupport, hχplateau, σ₀, hσ₀, hσ₁, coeff, C, hC, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ j
    by_cases hσ : σ ∈ Ioc (0 : ℝ) σ₀
    · rw [hcoeff σ hσ]
      exact hc σ hσ j
    · rw [show coeff σ = c₀ from dite_eq_right hσ]
      exact hc₀ j
  · simpa only [hzero] using hformula₀
  · intro σ hσ j z
    rw [hcoeff σ hσ]
    exact hformula σ hσ j z
  · intro m σ hσ j x
    rw [hcoeff σ hσ, hzero]
    exact hbounds m σ hσ j x
  · intro χ χsrc ψ angular localData d
    refine ⟨fun σ i ↦ ⟨rfl, rfl, rfl⟩, ?_⟩
    intro σ V
    have h i := (normalizedCarrierData_common_measurement (T i) (seed i).Q H.map
      (row i) (col i) (seed i).forward (seed i).inverse (initial i) hr (ha' i)
      hcell (hlocal i) (angular i) FixedCutoffs.highFrequency σ (hra i)).2 (V i)
    refine ⟨fun i ↦ (h i).1, fun i ht ↦ ((h i).2.1 ht).1,
      fun i ↦ (h i).2.2.1, ?_⟩
    rw [augmentedNormal_eq_sum]
    simp only [carrierChannel_restrictCarrier_normal]

end JanetCartan.ContinuumRow.NormalizedSelection
