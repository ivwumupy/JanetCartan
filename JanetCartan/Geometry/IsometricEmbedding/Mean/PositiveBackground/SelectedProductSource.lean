module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.SelectedProductWeights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.ConstructedPhysicalSource

/-!
# Construct the physical source on the original selected product cells

Choose external weights from the full detector supports at the original
selection point, then construct the source charts and literal physical mean
with the supplied common measurement. The product-cell flow maps exported by
the normalized selector control the entire external-weight support. The source
scale cap and all derivative bounds are fixed before scale varies.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PositiveBackground
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormal.FrozenModel
open PositiveReference PositiveReference.FlowConstruction ContinuumRow CanonicalCarrier LeadingPrimitive
open NormalizedBackground NormalizedBackground.SourceGeometry HamiltonPhase
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartMean
open ProjectedStressFrame UniformStep.Periodization RetainedAssembly.ExternalWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

/-- Choose the original external weights on the selected finite product cells
and construct the actual current charts and physical mean on the SAME supplied
measurement radius. The selected detector support, full weight collar, source
and exterior-independent raw correction identities are retained. The domain
maps follow directly from the selector's product-cell flow inclusion; no second
measurement choice or legacy working-cylinder comparison is required.

The source and mean bounds, normalized jets through zero, and positive
normal-field lower bound precede the varying scale. This instantiates
`RetainedAssembly.NormalizedMeanSource` from the original seed charts and
`NormalizedSelection` geometry; the uniform operator gap, primitive elliptic
bounds and corrected inverse must still be applied to this same family
(`app:ch_background:prop:bg-positive`, `app:ch_background:prop:bg-normalized`,
`app:ch_background:eq:bg-current-raising`, `new:sec:order-of-choices`). -/
theorem exists_constructed_source_on_selected_product_cells
    {n : ℕ} (hn : 5 ≤ n) {A : Type} [Fintype A] (G : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (hUG : U ⊆ G.domain.chart n) (hbounded : Bornology.IsBounded U)
    {P : A → Patch n} {cP CP : ℝ} (hP : ∀ a, (P a).IsValid cP CP)
    (T : (a : A) → PatchQuantitativeFamily (P a) U hU)
    {Ω : A → Set (Euclidean n × Euclidean 3)} (hΩ : ∀ a, IsOpen (Ω a))
    {z₀ : A → Euclidean 3} {ρ Rc M τ δgeometry : A → ℝ}
    {row col : A → Fin n}
    (hKΩ : ∀ a, closedBall ((0 : Euclidean n), z₀ a) (ρ a) ⊆ Ω a)
    (hpatch : ∀ a, Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius))
    (hΩU : ∀ a w, w ∈ Ω a → w.1 ∈ U)
    (hΩscale : ∀ a σ, σ ∈ Ioc (0 : ℝ) 1 →
      MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) (Ω a) (Ω a))
    (hRc : ∀ a, 0 < Rc a) (hM : ∀ a, 0 ≤ M a)
    (hτeq : ∀ a, τ a = existenceTime (Rc a) (liftedLowBound (T a) (M a)) / 4)
    (hδgeometry : ∀ a, 0 < δgeometry a)
    (hbuffer : ∀ a, MapsTo (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀ a)) (Rc a))
      (closedBall ((0 : Euclidean n), z₀ a) (ρ a)))
    (hphysical : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ U)
    (seed : (a : A) → Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
      ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a) G.map)
    (htrans : ∀ a, ∀ q ∈ closedBall (0, (T a).data.center) (T a).data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU (seed a).Q.1 (seed a).Q.2.1).hp q,
        (T a).data.adapted.normal⟫_ℝ ≠ 0)
    (Rcell : A → ℝ) (V : A → Set CarrierParameter) (hV : ∀ a, IsOpen (V a))
    (hRphysical : ∀ a, Rcell a ≤ (T a).physicalRadius)
    (hflow : ∀ a, MapsTo (densityCoordinates (T a))
      (ball (0 : Euclidean n) (Rcell a) ×ˢ V a)
      (outputCylinder ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (τ a)))
    (zRoot : A → Euclidean 3) (θ : A → Euclidean (n - 1))
    (am width : A → ℝ) (ham : ∀ a, 0 < am a) (hwidth : ∀ a, 0 < width a)
    (hselected : ∀ a, ContinuumAdjoint.Canonical.PhaseExtension.supportedChart
      (n := n) (zRoot a) (am a) ⊆ ball (0 : Euclidean n) (Rcell a) ×ˢ V a)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (hram : ∀ a, 6 * r < am a)
    (h6U : closedBall (0 : Euclidean n) (6 * r) ⊆ U) :
    ∃ χ : A → CarrierParameter → ℝ,
      (∀ a, ContDiff ℝ ∞ (χ a)) ∧
      (∀ a z, χ a z ∈ Icc (0 : ℝ) 1) ∧
      (∀ a, HasCompactSupport (χ a)) ∧
      (∀ a, tsupport (χ a) ⊆ V a) ∧
      (∀ a, CanonicalConic.carrierSupport (zRoot a) (r := am a) ⊆
        interior {z | χ a z = 1}) ∧
      (∀ a, IsFiniteMeasure (squaredCarrierMeasure (χ a))) ∧
      (∀ a z η, CanonicalConic.angularMask (zRoot a) (θ a) (ham a) (hwidth a) z η ≠ 0 → χ a z = 1) ∧
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧
    ∃ current : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → (a : A) →
      Chart (T a) (Ω a) (closedBall ((0 : Euclidean n), z₀ a) (ρ a))
        ((0 : Euclidean (n - 1)), z₀ a) (Rc a) (M a) (τ a) (row a) (col a)
        (sourceDilation G.map σ),
      (∀ σ hσ a,
        ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
            ℝ × (Euclidean (n - 1) × Euclidean 3),
          ODE.IsSmoothFlowOn (liftedDirection (T a) (current σ hσ a).Q (row a) (col a))
            (0, ((0 : Euclidean (n - 1)), z₀ a)) (Rc a) (Rc a / 2)
            (existenceTime (Rc a) (liftedLowBound (T a) (M a))) Ψ ∧
          (current σ hσ a).forward = forwardFromLift Ψ ∧
          (current σ hσ a).inverse = footpointFromLift Ψ ∧
          cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
            ((current σ hσ a).Q.1 - fun _ ↦ cubeStress n) < δgeometry a ∧
          EqOn ((current σ hσ a).scalar (fun _ ↦ σ))
            (sourceAmplitude ((seed a).scalar (fun _ ↦ 1)) σ)
            ((coordinates (adaptedCoordinates (T a).data.adapted)) ⁻¹' (current σ hσ a).D) ∧
          ∀ weight : Euclidean (n - 1) × Euclidean 3 → ℝ,
            EqOn ((current σ hσ a).scalar (fun q ↦ σ * weight q))
              (fun w ↦ sourceAmplitude ((seed a).scalar (fun _ ↦ 1)) σ w *
                weight ((current σ hσ a).inverse
                  (coordinates (adaptedCoordinates (T a).data.adapted) w)))
              ((coordinates (adaptedCoordinates (T a).data.adapted)) ⁻¹' (current σ hσ a).D)) ∧
    let d : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → A → CarrierData n (embeddingDimension n) :=
      fun σ hσ a ↦ data (T a) (current σ hσ a).Q (sourceDilation G.map σ)
      (row a) (col a) (current σ hσ a).forward (current σ hσ a).inverse (fun _ ↦ σ)
      hr hcell (CanonicalConic.angularMask (zRoot a) (θ a) (ham a) (hwidth a)) FixedCutoffs.highFrequency
    let e : ℝ → A → CarrierData n (embeddingDimension n) :=
      fun σ a ↦ normalizedCarrierData (T a) (seed a).Q G.map
      (row a) (col a) (seed a).forward (seed a).inverse (fun _ ↦ 1)
      hr hcell (CanonicalConic.angularMask (zRoot a) (θ a) (ham a) (hwidth a)) FixedCutoffs.highFrequency σ
    let H₀ : MetricTensor n := carrierMean (fun _ ↦ volume.prod volume) (fun a z ↦ χ a z ^ 2)
      (fun a ↦ (seed a).normal (fun _ ↦ 1)) (fun a ↦ covector (seed a)) 0
    let H : ℝ → MetricField n := fun σ ↦ physicalDensityMean (e σ) χ 0
    let Q : ℝ → Euclidean n → Fin n → MetricTensor n :=
      fun σ ↦ projectedStress (sourceDilation G.map σ)
    let R : ℝ → MetricField n := fun σ ↦ referenceMeanResidual (sourceDilation G.map σ) H₀ (H σ)
    let J := fun a q ↦ (normalizedPullback (unitAmplitude (seed a)) q,
      normalizedPullback (covector (seed a)) q,
      normalizedPullback ((seed a).normal (fun _ ↦ 1)) q)
    H₀.PosSemidef ∧
      (∀ σ hσ v, EqOn (physicalDensityMean (d σ hσ) χ v)
        (physicalDensityMean (e σ) χ v) (ball 0 (5 * r))) ∧
      (∀ σ hσ a,
        carrierKernel (d σ hσ a) = carrierKernel (e σ a) ∧
        carrierTestIntegral (d σ hσ a) = carrierTestIntegral (e σ a) ∧
        carrierAdjointIntegral (d σ hσ a) = carrierAdjointIntegral (e σ a)) ∧
    ∃ hQ : ∀ σ ∈ Ioc (0 : ℝ) cap, ContDiffOn ℝ ∞ (Q σ) (ball 0 (4 * r)),
    ∃ hR : ∀ σ ∈ Ioc (0 : ℝ) cap, ContDiffOn ℝ ∞ (R σ) (ball 0 (4 * r)),
    ∃ hRphysical : ∀ σ hσ, ContDiffOn ℝ ∞
        (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
        (ball 0 (4 * r)),
      (∀ σ hσ,
        fixedSourceToL2 hr hcell (Q σ)
            (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
            (hQ σ hσ) (hRphysical σ hσ) =
          fixedSourceToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ) ∧
        fixedResidualToL2 hr hcell (Q σ)
            (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
            (hQ σ hσ) (hRphysical σ hσ) =
          fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ) ∧
        ∀ (image : OutputL2 n →L[ℝ] OutputL2 n)
          (B : A → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (ψ : C(Torus n, ℝ)),
          let residualPhysical := fixedResidualToL2 hr hcell (Q σ)
            (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
            (hQ σ hσ) (hRphysical σ hσ)
          let residualNormalized := fixedResidualToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ)
          uncorrectedRawCorrection image B ψ (FixedCutoffs.periodic hr hcell 0) residualPhysical =
            uncorrectedRawCorrection image B ψ (FixedCutoffs.periodic hr hcell 0) residualNormalized ∧
          uncorrectedDensity (d σ hσ) image B ψ (FixedCutoffs.periodic hr hcell 0) residualPhysical =
            uncorrectedDensity (e σ) image B ψ (FixedCutoffs.periodic hr hcell 0) residualNormalized) ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ cap ∧ ∃ cNormal > (0 : ℝ),
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      (∀ a, ContDiffOn ℝ ∞ (J a)
        (Ioo (-2 * σ₀) (2 * σ₀) ×ˢ ball 0 (4 * r) ×ˢ V a)) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ s,
        (periodicSobolevScale n (Euclidean n)).gradeNorm s
          (fixedSourceToL2 hr hcell (Q σ) (R σ) (hQ σ hσ) (hR σ hσ)) ≤ C s * σ ∧
        cNorm (closedBall 0 (4 * r)) s (fun x ↦ H σ x - H₀) ≤ C s * σ ∧
        ∀ a x, x ∈ closedBall 0 (4 * r) → ∀ z ∈ tsupport (χ a),
          ‖iteratedFDeriv ℝ s (J a) (σ, (x, z))‖ ≤ C s) ∧
      (∀ σ (hσ : σ ∈ Ioc (0 : ℝ) cap), σ ≤ σ₀ → ∀ a x,
        x ∈ closedBall 0 (4 * r) → ∀ z ∈ tsupport (χ a),
          cNormal ≤ ‖(current σ hσ a).normal (fun _ ↦ σ) (x, z)‖ ∧
          cNormal ≤ ‖(e σ a).normalField x z‖) ∧
      (∀ a x z, z ∈ tsupport (χ a) → cNormal ≤ ‖(e 0 a).normalField x z‖) ∧
      (∀ σ ∈ Ioc (0 : ℝ) cap, EqOn (R σ) (fun x ↦ H σ x - H₀) (ball 0 (5 * r))) := by
  classical
  let angular : A → CarrierParameter → Euclidean (n - 1) → ℝ :=
    fun a ↦ CanonicalConic.angularMask (zRoot a) (θ a) (ham a) (hwidth a)
  let high : A → ℝ → ℝ := fun _ ↦ FixedCutoffs.highFrequency
  obtain ⟨χ, hχ, hχrange, hχcompact, hχV, hplateau, h6W, _, _, _, hfinite, hmask⟩ :=
    exists_selected_product_external_weights zRoot ham V hV hselected hr hram
  have hdetector := (hmask θ width hwidth).1
  refine ⟨χ, hχ, hχrange, hχcompact, hχV, hplateau, hfinite, hdetector, ?_⟩
  have hτ (a : A) : 0 < τ a := by
    rw [hτeq a]
    exact div_pos (existenceTime_pos (hRc a) (liftedLowBound_nonneg (T a) (hM a))) (by norm_num)
  have hτR (a : A) : τ a ≤ Rc a / 16 := by
    have hh := (existenceTime_le (hRc a) (liftedLowBound_nonneg (T a) (hM a))).1
    rw [hτeq a]
    linarith
  have hpatch' (a : A) : Ω a ⊆ ball 0 (T a).physicalRadius ×ˢ parameterCube (2 * (P a).radius) :=
    fun p hp ↦ ⟨(hpatch a hp).1, fun j ↦ ((hpatch a hp).2 j).le⟩
  obtain ⟨cap, hcap, hcap1, current, hcurrent⟩ :=
    NormalizedChartFamily.exists_finite_source_charts_with_lifts G hUG hbounded T Ω hΩ
      z₀ ρ Rc M τ δgeometry row col hRc hM hδgeometry hτeq hKΩ hpatch'
      hΩU hΩscale hphysical hbuffer seed htrans
  refine ⟨cap, hcap, hcap1, current, ?_, ?_⟩
  · intro σ hσ a
    obtain ⟨Ψ, hΨ, hf, hy, _, _, hsmall, _, _, hscalar, _, hweight⟩ := hcurrent σ hσ a
    exact ⟨Ψ, hΨ, hf, hy, hsmall, hscalar, hweight⟩
  intro d e H₀ H Q R J
  let Hphysical : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → MetricField n :=
    fun σ hσ ↦ carrierMean (fun _ ↦ volume.prod volume) (fun a z ↦ χ a z ^ 2)
    (fun a ↦ (current σ hσ a).normal (fun _ ↦ σ)) (fun a ↦ covector (current σ hσ a))
  let Rphysical : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) cap → MetricField n :=
    fun σ hσ ↦ referenceMeanResidual (sourceDilation G.map σ) H₀ (Hphysical σ hσ)
  let W := fun a ↦ ball (0 : Euclidean n) (Rcell a) ×ˢ V a
  have hseed (a : A) : MapsTo (densityCoordinates (T a)) (W a) (seed a).D :=
    ((hflow a).mono_right (outputCylinder_spec (hRc a) (hτ a)).2).mono_right
      (seed a).small_subset
  have hcurrentDomain (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (a : A) :
      MapsTo (densityCoordinates (T a)) (W a) (current σ hσ a).D :=
    ((hflow a).mono_right (outputCylinder_spec (hRc a) (hτ a)).2).mono_right
      (current σ hσ a).small_subset
  have h5W' (a : A) : ball (0 : Euclidean n) (5 * r) ×ˢ V a ⊆ W a :=
    (prod_mono ((ball_subset_ball (by linarith)).trans ball_subset_closedBall)
      Subset.rfl).trans (h6W a)
  have hχpatch (a : A) (z) (hz : z ∈ tsupport (χ a)) :
      parameter z ∈ parameterInterior (2 * (P a).radius) := by
    have hh := (seed a).domain_coefficients (hseed a
      (@h6W a (0, z) ⟨mem_closedBall_self (by positivity), hχV a hz⟩))
    change (coordinates (adaptedCoordinates (T a).data.adapted)).symm
      (coordinates (adaptedCoordinates (T a).data.adapted) (0, parameter z)) ∈ Ω a at hh
    rw [ContinuousLinearEquiv.symm_apply_apply] at hh
    exact (hpatch a hh).2
  have h5W (a : A) : ball (0 : Euclidean n) (5 * r) ⊆ ball 0 (T a).physicalRadius := by
    intro x hx
    have hz : (zRoot a 0, FullPhaseCharts.ActualComparison.spectatorCenter (zRoot a)) ∈
        CanonicalConic.carrierSupport (zRoot a) (r := am a) :=
      ⟨mem_closedBall_self (half_pos (ham a)).le, mem_closedBall_self (half_pos (ham a)).le⟩
    have hx' : x ∈ closedBall (0 : Euclidean n) (4 * am a) :=
      ((ball_subset_ball (by linarith [hram a])).trans ball_subset_closedBall) hx
    have hp := @hselected a
      (x, (zRoot a 0, FullPhaseCharts.ActualComparison.spectatorCenter (zRoot a))) ⟨hx', hz⟩
    exact (ball_subset_ball (hRphysical a)) hp.1
  have hmean (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) (v : A → CarrierVariable n → ℝ) :
      EqOn (physicalDensityMean (d σ hσ) χ v) (physicalDensityMean (e σ) χ v)
        (ball 0 (5 * r)) := by
    have hscalar (a : A) (x : Euclidean n) (hx : x ∈ ball 0 (5 * r))
        (z : CarrierParameter) (hz : z ∈ tsupport (χ a)) :
        carrierScalarAmplitude (T a) (current σ hσ a).Q (sourceDilation G.map σ)
          (row a) (col a) (current σ hσ a).forward (current σ hσ a).inverse (fun _ ↦ σ)
          (x, parameter z) =
        sourceAmplitude (carrierScalarAmplitude (T a) (seed a).Q G.map
          (row a) (col a) (seed a).forward (seed a).inverse (fun _ ↦ 1)) σ (x, parameter z) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hs, _, _⟩ := hcurrent σ hσ a
      have hp : (x, z) ∈ W a :=
        h5W' a ⟨hx, hχV a hz⟩
      exact @hs (x, parameter z) (hcurrentDomain σ hσ a hp)
    exact physicalDensityMean_eq_normalized_of_scalar_transport T
      (fun a ↦ (seed a).Q) (fun a ↦ (current σ hσ a).Q) G.map row col
      (fun a ↦ (seed a).forward) (fun a ↦ (seed a).inverse)
      (fun a ↦ (current σ hσ a).forward) (fun a ↦ (current σ hσ a).inverse)
      hr hcell angular high χ hP hχpatch G.contDiff
      (fun x hx ↦ G.fullNormalRank x (hUG hx)) hphysical (fun a ↦ (seed a).frame_eq)
      htrans hσ.1 (hσ.2.trans hcap1) (fun a ↦ (current σ hσ a).frame_eq) h5W hscalar v
  have hzero (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) :
      EqOn (Hphysical σ hσ) (H σ) (ball 0 (5 * r)) := by
    simpa only [d, physicalDensityMean_retainedChart_zero] using hmean σ hσ 0
  have hresidual (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) :
      EqOn (Rphysical σ hσ) (R σ) (ball 0 (5 * r)) := by
    intro x hx
    change _ + Hphysical σ hσ x = _ + H σ x
    rw [hzero σ hσ hx]
  obtain ⟨hpos, hQ, hRphysical, σ₀, hσ₀, hσcap, cNormal, hcNormal, C, hC,
    hJ, hbound, hnormal, hfields, hres⟩ :=
    exists_retained_fixedSource_sobolev_bounds hn G hUG hP hΩ hKΩ hpatch hRc hτ hτR
      hbuffer hphysical χ hχ hχcompact W hr hcell h6U V hV hχV h6W seed hseed
      htrans hcap hcap1 current hcurrentDomain
  have h45 : ball (0 : Euclidean n) (4 * r) ⊆ ball 0 (5 * r) := ball_subset_ball (by linarith)
  have hR (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) : ContDiffOn ℝ ∞ (R σ) (ball 0 (4 * r)) :=
    (hRphysical σ hσ).congr (fun x hx ↦ (hresidual σ hσ (h45 hx)).symm)
  have hRliteral (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) cap) : ContDiffOn ℝ ∞
      (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
      (ball 0 (4 * r)) := by
    simpa only [d, physicalDensityMean_retainedChart_zero] using hRphysical σ hσ
  refine ⟨hpos, hmean, ?_, hQ, hR, hRliteral, ?_, σ₀, hσ₀, hσcap,
    cNormal, hcNormal, C, hC, hJ, ?_, ?_, ?_, ?_⟩
  · intro σ hσ a
    have hsupport (x : Torus n) (z : CarrierParameter) (η : Euclidean (n - 1))
        (hx : FixedCutoffs.periodic hr hcell 1 x ≠ 0) (hz : angular a z η ≠ 0) :
        densityCoordinates (T a) (AmplitudeBound.centeredTorusRepresentative x, z) ∈
          Ioo (-τ a) (τ a) ×ˢ ball ((0 : Euclidean (n - 1)), z₀ a) (Rc a / 32) := by
      apply (outputCylinder_spec (hRc a) (hτ a)).2
      apply hflow a
      have hzχ : χ a z ≠ 0 := by rw [hdetector a z η hz]; norm_num
      apply h6W a
      refine ⟨?_, hχV a (subset_tsupport (χ a) hzχ)⟩
      exact closedBall_subset_closedBall (by linarith : 4 * r ≤ 6 * r)
        (FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hx))
    have hdomain : (coordinates (adaptedCoordinates (T a).data.adapted)) ⁻¹'
        (current σ hσ a).D ⊆ ball 0 (T a).physicalRadius ×ˢ parameterInterior (2 * (P a).radius) := by
      intro w hw
      have hh := (current σ hσ a).domain_coefficients hw
      change (coordinates (adaptedCoordinates (T a).data.adapted)).symm
        (coordinates (adaptedCoordinates (T a).data.adapted) w) ∈ Ω a at hh
      rw [ContinuousLinearEquiv.symm_apply_apply] at hh
      exact hpatch a hh
    obtain ⟨_, _, _, _, _, _, _, _, _, hscalar, _, _⟩ := hcurrent σ hσ a
    have hk := NormalizedSelection.carrierKernel_eq_normalized_of_scalar_transport
      (T a) (seed a).Q (current σ hσ a).Q G.contDiff
      (fun x hx ↦ G.fullNormalRank x (hUG hx)) (hphysical a) (seed a).frame_eq (htrans a)
      hσ.1 (hσ.2.trans hcap1) (current σ hσ a).frame_eq (row a) (col a)
      (seed a).forward (seed a).inverse (current σ hσ a).forward (current σ hσ a).inverse
      (fun _ ↦ 1) (fun _ ↦ σ) (hP a) hr hcell (angular a) (high a) hdomain
      (fun x z η hx hz ↦ (current σ hσ a).small_subset (hsupport x z η hx hz)) hscalar
    change carrierKernel (d σ hσ a) = carrierKernel (e σ a) at hk
    refine ⟨hk, ?_, ?_⟩
    · funext v x
      simp only [carrierTestIntegral, hk]
    · funext w u
      simp only [carrierAdjointIntegral, hk]
  · intro σ hσ
    have heq : EqOn
        (referenceMeanResidual (sourceDilation G.map σ) H₀ (physicalDensityMean (d σ hσ) χ 0))
        (R σ) (ball 0 (4 * r)) := by
      simpa only [d, physicalDensityMean_retainedChart_zero] using
        (hresidual σ hσ).mono h45
    have hs := fixedSourceToL2_eq_of_residual_eqOn hr hcell (Q σ) (hQ σ hσ)
      (hRliteral σ hσ) (hR σ hσ) heq
    have hb := fixedResidualToL2_eq_of_residual_eqOn hr hcell (Q σ) (hQ σ hσ)
      (hRliteral σ hσ) (hR σ hσ) heq
    refine ⟨hs, hb, ?_⟩
    intro image B ψ
    dsimp only
    rw [hb]
    exact ⟨rfl, rfl⟩
  · intro σ hσ hs s
    have hb := (hbound σ hσ hs s).1
    rw [fixedSourceToL2_eq_of_residual_eqOn hr hcell (Q σ) (hQ σ hσ)
      (hRphysical σ hσ) (hR σ hσ) ((hresidual σ hσ).mono h45)] at hb
    refine ⟨hb, ?_, (hbound σ hσ hs s).2.2⟩
    have heq : cNorm (closedBall 0 (4 * r)) s (fun x ↦ Hphysical σ hσ x - H₀) =
        cNorm (closedBall 0 (4 * r)) s (fun x ↦ H σ x - H₀) := by
      unfold cNorm
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply Set.image_congr
      intro x hx
      have he : (fun y ↦ Hphysical σ hσ y - H₀) =ᶠ[nhds x] (fun y ↦ H σ y - H₀) := by
        filter_upwards [isOpen_ball.mem_nhds
          (closedBall_subset_ball (by linarith : 4 * r < 5 * r) hx)] with y hy
        rw [hzero σ hσ hy]
      exact congrArg norm ((he.iteratedFDeriv ℝ j).eq_of_nhds)
    rw [← heq]
    exact (hbound σ hσ hs s).2.1
  · intro σ hσ hs a x hx z hz
    have hn' := hnormal σ hσ hs a x hx z hz
    refine ⟨hn', ?_⟩
    change cNormal ≤ ‖normalizedPullback ((seed a).normal (fun _ ↦ 1)) (σ, (x, z))‖
    rw [← (hfields σ hσ a x hx z hz).1]
    exact hn'
  · intro a x z hz
    have hσ : σ₀ ∈ Ioc (0 : ℝ) cap := ⟨hσ₀, hσcap⟩
    have hx : (0 : Euclidean n) ∈ closedBall 0 (4 * r) := mem_closedBall_self (by positivity)
    have hn' := hnormal σ₀ hσ le_rfl a 0 hx z hz
    rw [(hfields σ₀ hσ a 0 hx z hz).1] at hn'
    change cNormal ≤ ‖normalizedPullback ((seed a).normal (fun _ ↦ 1)) (0, (x, z))‖
    simpa only [normalizedPullback, smul_zero, zero_smul] using hn'
  · intro σ hσ x hx
    exact (hresidual σ hσ hx).symm.trans
      ((hres σ hσ hx).trans (congrArg (· - H₀) (hzero σ hσ hx)))

end JanetCartan.PositiveBackground
