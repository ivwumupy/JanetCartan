module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedMeasurement.Restriction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.NormalizedImage

/-!
# One supplied-family measurement choice before source scale

`exists_supplied_family_normalized_measurement` takes the original finite
incidence radii and masks supplied by `RetainedFrozen.Row` and `RetainedCover`.
It chooses the measurement radius and coefficient/measurement/source/exterior
cutoffs before the source scale. It then constructs the actual normalized image
coefficients on this SAME cutoff and restricts the supplied carrier data and
operators, on the original index type. It does not call another row selector.

The original full angular supports, source charts and initial buffers are
retained; only the physical measurement factor changes. The row-normal identity
has the original squared exterior complement and both real quadratures.
No coercivity, inverse or normalized carrier estimate is used here.

The enriched normalized selector must instantiate these supplied-family results
on its original finite witnesses. Its carrier construction and uniform gap are
separate obligations. The resulting fixed `r` and `χcoeff` are the inputs of
`ContinuumCommutator.exists_normalized_row_elliptic_estimates`; the same fixed
angular/high masks and measurement functions are used by
`PositiveBackground.exists_small_uncorrectedDensity_of_normal_estimates`.

Sources: paper.tex `app:ch_background:eq:bg-uniform-normalized`,
`app:ch_background:defn:bg-row`, and paper-v2.tex `new:sec:order-of-choices`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.ContinuumRow.NormalizedMeasurement
open CommonMeasurement CanonicalConic GeometricProfile
open PeriodicLocalL2 AmplitudeBound
open ContinuumAdjoint.Canonical.PhaseExtension

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The supplied finite incidence family admits fixed measurement geometry
BEFORE every `σ ∈ (0, σ₀]`. The coefficient array is constructed from the
literal source dilation, and the row uses the supplied carriers on their
original labels, masks and measure. All jet constants precede `σ`.

The geometric inputs are exactly the positive retained `a'` radii, original
mask centers/widths and fixed chart bounds. The later carrier chart identities
are the definitional fields of `CanonicalCarrier.data`, as witnessed by
`commonChartData_canonicalData`. Neither an analytic estimate nor another
existential row is identified with the supplied family
(`bg-uniform-normalized`, `bg-T`, `new:sec:order-of-choices`). -/
theorem exists_supplied_family_normalized_measurement
    (a' : ι → ℝ) (ha' : ∀ i, 0 < a' i)
    (z₀ : ι → Euclidean 3) (θ₀ : ι → Euclidean (n - 1))
    (angleWidth : ι → ℝ) (hangleWidth : ∀ i, 0 < angleWidth i)
    {b R : ℝ} (hb : 0 < b) (hR : 0 < R) :
    ∃ (r : ℝ) (hr : 0 < r) (hcell : 4 * r < 1 / 2),
      6 * r < b ∧ 6 * r < R ∧ 6 * r < 1 / 2 ∧ (∀ i, 6 * r < a' i) ∧
    ∃ χcoeff : Euclidean n → ℝ,
      ContDiff ℝ ∞ χcoeff ∧ (∀ x, χcoeff x ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χcoeff ∧ tsupport χcoeff ⊆ ball 0 (5 * r) ∧
      closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1} ∧
    let χ := FixedCutoffs.periodic (n := n) hr hcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hr hcell 2
    let ψ := FixedCutoffs.periodic (n := n) hr hcell 0
    let angular := fun i ↦ angularMask (z₀ i) (θ₀ i) (ha' i) (hangleWidth i)
    (∀ j : Fin 3, IsSmoothPeriodic (FixedCutoffs.periodic (n := n) hr hcell j)) ∧
    (∀ j : Fin 3, tsupport (FixedCutoffs.physical (n := n) hr j) ⊆
      interior {x | χcoeff x = 1}) ∧
    (∀ (i : ι) (j : Fin 3), tsupport (FixedCutoffs.physical (n := n) hr j) ⊆
      interior {x | FixedCutoffs.physical (ha' i) 1 x = 1}) ∧
    (∀ i, closedBall (0 : Euclidean n) (6 * r) ×ˢ carrierSupport (z₀ i) (r := a' i) ⊆
      supportedChart (z₀ i) (a' i)) ∧
    (∀ (i : ι) (f : Euclidean n × CarrierParameter → CarrierVariable n)
        (χinitial : CarrierVariable n → ℝ),
      MapsTo f (supportedChart (z₀ i) (a' i)) (interior {q | χinitial q = 1}) →
      MapsTo f (closedBall 0 (6 * r) ×ˢ carrierSupport (z₀ i) (r := a' i))
        (interior {q | χinitial q = 1})) ∧
    ∀ H : FlatReference n,
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
    ∃ (c₀ : ReducedCoefficientIndex n → C(Torus n, ℝ))
      (c : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) σ₀ → ReducedCoefficientIndex n → C(Torus n, ℝ))
      (C : ℕ → ℝ),
      (∀ m, 0 < C m) ∧
      (∀ j z, c₀ j z = χcoeff (centeredTorusRepresentative z) *
        ProtectedFlow.reducedCoefficientBackground (fun _ _ ↦ 0)
          (centeredTorusRepresentative z) j) ∧
      (∀ j, IsSmoothPeriodic (c₀ j)) ∧
      (∀ m j x, ‖iteratedFDeriv ℝ m (periodicLift (c₀ j)) x‖ ≤ C m) ∧
      (∀ σ hσ j z, c σ hσ j z = χcoeff (centeredTorusRepresentative z) *
        geometricReducedCoefficients (sourceDilation H.map σ)
          (centeredTorusRepresentative z) j) ∧
      (∀ σ hσ j, IsSmoothPeriodic (c σ hσ j)) ∧
      (∀ σ hσ j x, x ∈ closedBall 0 (4 * r) → periodicLift (c σ hσ j) =ᶠ[nhds x]
        fun y ↦ geometricReducedCoefficients (sourceDilation H.map σ) y j) ∧
      (∀ m σ hσ j x,
        ‖iteratedFDeriv ℝ m (periodicLift (c σ hσ j - c₀ j)) x‖ ≤ C m * σ ∧
        ‖iteratedFDeriv ℝ m (periodicLift (c σ hσ j)) x‖ ≤ C m) ∧
      (∀ σ hσ (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f),
        cutoffMultiplier χ (reducedWeakOperator (c σ hσ) (PeriodicSobolevSpace.ofSmooth 1 f hf))
          =ᵐ[volume] fun z ↦ FixedCutoffs.physical hr 1 (centeredTorusRepresentative z) •
            WithLp.toLp 2 (NullTransport.reducedOperator (sourceDilation H.map σ)
              (fun y i ↦ (StressFrame.geometricCubeStress (sourceDilation H.map σ) y i).val)
              (periodicLift f) (centeredTorusRepresentative z))) ∧
      ∀ (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀)
        (d : ι → CarrierData n N) (hlocal : ∀ i, 4 * a' i < 1 / 2),
      (∀ i, (d i).outputChart = torusChart (closedBall 0 (4 * a' i))) →
      (∀ i x, x ∈ (d i).outputChart → (d i).chartPoint x = centeredTorusRepresentative x) →
      (∀ i, (d i).measurementCutoff = FixedCutoffs.periodic (ha' i) (hlocal i) 1) →
      (∀ i, (d i).angularCutoff = angular i) →
      (∀ i, (d i).highCutoff = FixedCutoffs.highFrequency) →
      let e := fun i ↦ commonChartData (d i) (closedBall 0 (4 * r)) χ
      (∀ i, (e i).angularCutoff = angular i ∧ (e i).highCutoff = FixedCutoffs.highFrequency ∧
        tsupport (Function.uncurry (e i).angularCutoff) =
          tsupport (Function.uncurry (d i).angularCutoff) ∧
        (e i).transportedPosition = (d i).transportedPosition ∧
        (e i).covector = (d i).covector ∧ (e i).normalField = (d i).normalField ∧
        (e i).stressFrame = (d i).stressFrame) ∧
      (∀ i x u, carrierKernel (e i) x u = χ x • carrierKernel (d i) x u) ∧
      ∀ V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        let Aimage := imageChannel (c σ hσ) χ χsrc
        let Vb := fun i ↦ restrictCarrier χ (V i)
        (∀ i, ‖Vb i‖ ≤ ‖V i‖) ∧
        (∀ i, (∀ v : carrierInitialTestSpace n,
            V i (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (d i) v.val) →
          (∀ v : carrierInitialTestSpace n,
            Vb i (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (e i) v.val) ∧
          ∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ (e i).outputChart → Vb i f x = 0) ∧
        (∀ i, (∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral (d i) w) 2 (carrierMeasure n) ∧
            (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (d i) w) →
          ∀ w : ComplexOutputL2 n,
            MemLp (carrierAdjointIntegral (e i) w) 2 (carrierMeasure n) ∧
            (Vb i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) w) ∧
        augmentedNormal Aimage Vb ψ = Aimage ∘L Aimage.adjoint +
          (∑ i, cutoffMultiplier χ ∘L
            (carrierChannel (V i) ∘L (carrierChannel (V i)).adjoint) ∘L cutoffMultiplier χ) +
          cutoffMultiplier ((1 - ψ) ^ 2) := by
  obtain ⟨r, hr, hcell, hrb, hrR, hrhalf, hra, χcoeff, hχ, hχrange, hχcompact,
    hχsupport, hχplateau, hsource, hlocal, _⟩ :=
    exists_measurement_cutoffs_before_scale (n := n) a' ha' hb hR
  refine ⟨r, hr, hcell, hrb, hrR, hrhalf, hra, χcoeff,
    hχ, hχrange, hχcompact, hχsupport, hχplateau, ?_⟩
  intro χ χsrc ψ angular
  refine ⟨FixedCutoffs.periodic_smooth hr hcell, hsource, hlocal,
    (fun i ↦ source_product_subset_original_supportedChart (z₀ i) hr (hra i)),
    (fun i f χinitial ↦ initial_buffer_on_common_source (z₀ i) hr (hra i) f
      (interior {q | χinitial q = 1})), ?_⟩
  intro H
  obtain ⟨σ₀, hσ₀, hσ₁, c₀, c, hformula₀, hc₀, _, hformula, hc, hagree,
    hbounds, _, haction, _⟩ :=
    RetainedAssembly.NormalizedImage.exists_normalized_image_coefficients H
      (by positivity : 0 < 4 * r) (by linarith : 4 * r < 5 * r)
      (by linarith : 5 * r < 6 * r) hrhalf hχ hχsupport hχplateau
  choose C hC hC₀ hCσ using hbounds
  refine ⟨σ₀, hσ₀, hσ₁, c₀, c, C, hC, hformula₀, hc₀, hC₀, hformula, hc, hagree,
    hCσ, ?_, ?_⟩
  · intro σ hσ f hf
    exact haction σ hσ (FixedCutoffs.physical hr 1) (FixedCutoffs.physical hr 1).contDiff
      (FixedCutoffs.physical_tsupport_four hr 1) f hf
  · intro σ hσ d hcell' hchart hpoint hmeas hangular hhigh e
    have hs i := supplied_carrier_common_measurement (d i) hr (ha' i) hcell (hcell' i)
      (hra i) (hchart i) (hpoint i) (hmeas i)
    refine ⟨(fun i ↦ ⟨hangular i, hhigh i, rfl, rfl, rfl, rfl, rfl⟩),
      (fun i ↦ (hs i).2.2.2.2.2.2.2.1), ?_⟩
    intro V Aimage Vb
    have hV i := (hs i).2.2.2.2.2.2.2.2 (V i)
    refine ⟨(fun i ↦ (hV i).1), (fun i ↦ (hV i).2.1),
      (fun i ↦ (hV i).2.2), ?_⟩
    rw [augmentedNormal_eq_sum]
    simp only [Vb, carrierChannel_restrictCarrier_normal]

end JanetCartan.ContinuumRow.NormalizedMeasurement
