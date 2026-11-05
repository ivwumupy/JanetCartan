module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenCoercivity.ImageEnergy

/-!
# Coercivity of the constructed unit-initial frozen row

For `app:ch_background:prop:bg-frame`, the finite incidence construction,
literal carrier realization, Euclidean Fourier gap and periodic/source-mask
image comparison apply to the SAME masks and inverses. Fix the outer radius
before the image-error constant, then choose only the inner support radius.
The augmented row retains the original exterior `(1-ψ)²` and both real
quadratures. No coercivity, energy identification or symbol bound is assumed.

This endpoint concerns the normalized zero-scale unit-initial model. Transfer
to positive source scales, current immersions and nonconstant initial densities
still requires the actual common-family normal variation and row matching.
It does not prove the original wider density class.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenCoercivity
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel ConicChart
open ProjectedStressFrame
open Pseudodifferential AmplitudeBound PeriodicLocalL2
open FrozenModel CommonMeasurement EuclideanSupportGap FrozenImageComparison

/-- Combine the literal frozen energies with the fixed periodic/source-mask image
comparison, choose the inner support, and add the original squared exterior.
Consumer: the supplied retained-family assembly (`app:ch_background:prop:bg-frame`). -/
theorem exists_frozen_row_gap_of_spectral_energy
    {n : ℕ} {ι : Type*} [Fintype ι] (hn : 0 < n)
    (Q : Fin n → MetricTensor n) (b : Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (hecont : Continuous b) {γ B R₀ μ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ k, ‖b k‖ ≤ B) (hnonneg : ∀ k, (b k).PosSemidef)
    (hgap : ∀ k, R₀ ≤ ‖k‖ → ∀ v : Euclidean n,
      γ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (b k *ᵥ v.ofLp))
    (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2)
    (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (henergy : ∀ w : OutputL2 n,
      let f := fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x)
      euclideanFrozenEnergy b f = euclideanFrozenEnergy (frozenImageSymbol Q) f +
        ∑ i, ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2) :
    let image := fixedPeriodicChannel hμ hμcell (frozenImageArrays Q)
    ∃ (r : ℝ) (hr : 0 < r) (hrcell : r < 1 / 2), r ≤ μ ∧
      (∀ w : OutputL2 n,
        (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r → w z = 0) →
        γ / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image V).adjoint w‖ ^ 2) ∧
      0 < NormalAugmentation.globalGap (γ / 2) ‖physicalRow image V‖ ∧
      (∀ w : OutputL2 n,
        NormalAugmentation.globalGap (γ / 2) ‖physicalRow image V‖ * ‖w‖ ^ 2 ≤
          inner ℝ (augmentedNormal image V (innerCutoff hr hrcell) w) w) ∧
      (∀ w : OutputL2 n, ∀ᵐ z ∂volume,
        centeredTorusRepresentative z ∈ closedBall 0 (r / 2) →
          exteriorChannel (innerCutoff hr hrcell) w z = 0) := by
  classical
  let image := fixedPeriodicChannel hμ hμcell (frozenImageArrays Q)
  obtain ⟨C, hC, hcomparison⟩ := exists_imageChannel_energyDifference_le_l1_sq
    hμ hμcell (frozenImageArrays Q)
  obtain ⟨r, hr, hrμ, hsmall⟩ := exists_inner_radius_euclideanFrozenEnergy_gap
    hn b hecont hγ hC hbound hnonneg hgap hμ
  have hrcell : r < 1 / 2 := by linarith only [hrμ, hμ, hμcell]
  have hlocal (w : OutputL2 n)
      (hw : ∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r → w z = 0) :
      γ / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image V).adjoint w‖ ^ 2 := by
    let u := l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) w)
    have hu : u =ᵐ[volume] fun x ↦ euclideanComplexInclusion (toEuclidean (𝕜 := ℝ) w x) :=
      (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL (toEuclidean (𝕜 := ℝ) w)
    have husupp : ∀ᵐ x ∂volume, x ∉ ball (0 : Euclidean n) r → u x = 0 := by
      filter_upwards [hu, toEuclidean_supported_innerBall hμ hμcell hrμ w hw] with x hx hs hxout
      rw [hx, hs hxout, map_zero]
    have hmeasure := measured_eq_zeroExtension hμ hμcell hrμ w hw
    have huMeasure : u =ᵐ[volume] fun x ↦ euclideanComplexInclusion
        (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x) := by
      filter_upwards [hu, hmeasure] with x hx hm
      rw [hm, hx]
    have hL₁ : (∫ x, ‖u x‖) = ∫ x, ‖toEuclidean (𝕜 := ℝ) w x‖ := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx, euclideanComplexInclusion_norm]
    have h := hsmall r hr le_rfl u husupp
    rw [show ‖u‖ ^ 2 = ‖w‖ ^ 2 from complex_zeroExtension_norm_sq w,
      hL₁, euclideanFrozenEnergy_congr_ae _ huMeasure, henergy w] at h
    have himage : euclideanFrozenEnergy (frozenImageSymbol Q)
        (fun x ↦ euclideanComplexInclusion
          (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x)) =
        fourierEnergy (frozenImageArrays Q) (toEuclidean (𝕜 := ℝ) w) := by
      rw [fourierEnergy_eq_euclideanFrozenImageEnergy]
      apply euclideanFrozenEnergy_congr_ae
      exact hmeasure.fun_comp euclideanComplexInclusion
    rw [himage] at h
    have hc := (abs_le.mp (hcomparison r hrμ _ (fun _ _ _ ↦ rfl) w hw)).1
    change -(C * (∫ x, ‖toEuclidean (𝕜 := ℝ) w x‖) ^ 2) ≤
      ‖image.adjoint w‖ ^ 2 -
        fourierEnergy (frozenImageArrays Q) (toEuclidean (𝕜 := ℝ) w) at hc
    rw [physicalRow_adjoint_norm_sq]
    linarith only [h, hc]
  refine ⟨r, hr, hrcell, hrμ, hlocal,
    NormalAugmentation.globalGap_pos (half_pos hγ), ?_,
    inner_exterior_zero_on_core hr hrcell⟩
  intro w
  exact NormalAugmentation.augmentedNormal_gap_of_local_coercivity
    (physicalRow image V) (cutoffMultiplier (innerCutoff hr hrcell))
    (ContinuousLinearMap.isSelfAdjoint_iff'.mpr (cutoffMultiplier_adjoint _))
    (cutoffMultiplier (innerCutoff hr hrcell)).toLinearMap.range (half_pos hγ)
    (fun f ↦ ⟨f, rfl⟩)
    (fun g ⟨f, hf⟩ ↦ hlocal g (hf ▸ innerCutoff_supported hr hrcell f)) w


/-- The actual unit-initial finite frozen row satisfies the local lower bound
and the global augmented gap of `app:ch_background:prop:bg-frame`. All carrier
extensions, adjoints, normal amplitudes and energies below are constructed from
the original geometric inputs. The outer cutoff is fixed before the image
comparison constant and the inner support radius. The exterior is the original
squared complement, with an open core plateau. The same finite refinement and
operator witnesses satisfy every conclusion; no analytic gap premise remains.
This is the frozen endpoint, before current-family and density perturbation. -/
theorem exists_finite_realized_frozen_row_gap {n : ℕ} (hn : 5 ≤ n)
    {D : CoverData n} {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {b s : ℝ} (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hframe : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall (0 : Euclidean n) b)
    (hs : 0 < s) (hsradius : ∀ i, 3 * s < (T i).physicalRadius) (hsb : 3 * s < b)
    (M : ℝ) {κmet κnormal cap : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (hcap : 0 < cap) :
    ∃ R : IncidenceRefinement D, R.IsValid ∧
    ∃ (m : ℕ) (chart : Fin m → Fin R.chartCount) (center : Fin m → Euclidean n)
      (ρ : Fin m → ℝ),
    ∃ scale : (l : Fin m) → Fin (D.patchCount (R.sourceChart (chart l))) → ℝ,
    ∃ d : (l : Fin m) → (a : Fin (D.patchCount (R.sourceChart (chart l)))) →
      FrozenIncidencePatchData (T ⟨R.sourceChart (chart l), a⟩)
        (D.roots (R.sourceChart (chart l)) a (center l))
        ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
          (scale l a • center l)),
    ∃ hcell : ∀ l a, 4 * (d l a).a < 1 / 2,
      (∀ l a, 0 < scale l a ∧ ‖scale l a • center l‖ = 1 / 4 ∧
        NormedSpace.normalize (scale l a • center l) = NormedSpace.normalize (center l) ∧
        NormedSpace.normalize
          ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
            (scale l a • center l)) =
        NormedSpace.normalize
          ((T ⟨R.sourceChart (chart l), a⟩).data.adapted.embedding.toContinuousLinearMap.adjoint
            (center l))) ∧
      (∀ l, center l ∈ sphere (0 : Euclidean n) 1) ∧
      (∀ l, 0 < ρ l) ∧
      (∀ l, ball (center l) (ρ l) ⊆ ball (R.center (chart l)) (R.radius (chart l))) ∧
      (sphere (0 : Euclidean n) 1 ⊆ ⋃ l, ball (center l) (ρ l)) ∧
      (∀ l a, 6 * (d l a).a < cap) ∧
      ∃ μ₀ > (0 : ℝ), 4 * μ₀ < 1 / 2 ∧ (∀ l a, 6 * μ₀ < (d l a).a) ∧
      ∃ δ > (0 : ℝ),
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm (closedBall (0 : Euclidean n) b) 4 F ≤ M →
        (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ v,
          κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ closedBall (0 : Euclidean n) b, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        (∀ i, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ projectedStress F x i - cubeStress n i) < δ) →
        let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
          (∀ l a, (d l a).Geometry ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart l), a⟩⟩) ∧
          (∀ l a, (d l a).UnitRealization
            ⟨projectedStress F, hQ, hlow ⟨R.sourceChart (chart l), a⟩⟩ F (hcell l a)) ∧
          let I := (l : Fin m) × Fin (D.patchCount (R.sourceChart (chart l)))
          let source := fun i : I ↦ ⟨R.sourceChart (chart i.1), i.2⟩
          let T' := fun i : I ↦ T (source i)
          let d' := fun i : I ↦ d i.1 i.2
          let z₀ := fun i : I ↦ D.roots (source i).1 (source i).2 (center i.1)
          let ηb := fun i : I ↦ (T' i).data.adapted.embedding.toContinuousLinearMap.adjoint (scale i.1 i.2 • center i.1)
          let Q' (i : I) : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
              cNorm (closedBall (0 : Euclidean n) (T' i).data.localReference.stateRadius) 6
                (Q - fun _ ↦ cubeStress n) < (T' i).family.threshold} :=
            ⟨projectedStress F, hQ, hlow (source i)⟩
          let u := fun i : I ↦ frozenSymbolInverse (T' i) (Q' i) (z₀ i) (ηb i) (d' i).r (6 * (d' i).a)
          let Ω := fun i : I ↦ frozenSymbolDomain (T' i) (Q' i) (z₀ i) (ηb i) (d' i).r (6 * (d' i).a)
          let J := fun i : I ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (T' i))
            (normalizedTransportPosition (T' i) (Q' i) 0)
          let S := fun i : I ↦ closedBall (spectatorCenter (z₀ i)) ((d' i).a / 2)
          let R₀ := frozenFamilyHighFrequencyRadius T' (fun i ↦ (d' i).G)
          1 ≤ R₀ ∧
          ∀ (Φ Y : I → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3),
          let carrier := fun initial i ↦ canonicalFrozenCarrierSymbol (T' i) (Q' i) F
            (d' i).row (d' i).col (Φ i) (Y i) (initial i) (z₀ i) (d' i).hηb (d' i).hr (d' i).ha
          let e := fun initial ↦ canonicalFrozenMatrixSymbol T' (projectedStress F) hQ
            (fun i ↦ hlow (source i)) F (fun i ↦ (d' i).row) (fun i ↦ (d' i).col) Φ Y initial
            z₀ ηb (fun i ↦ (d' i).r) (fun i ↦ (d' i).a)
            (fun i ↦ (d' i).hηb) (fun i ↦ (d' i).hr) (fun i ↦ (d' i).ha)
          Continuous (e (fun _ _ ↦ 1)) ∧
          (∃ B ≥ (0 : ℝ), ∀ k, ‖e (fun _ _ ↦ 1) k‖ ≤ B) ∧
          (∀ k, (e (fun _ _ ↦ 1) k).PosSemidef) ∧
          ∃ γ > (0 : ℝ),
            (∀ k, R₀ ≤ ‖k‖ → ∀ v : Euclidean n,
              γ * ‖v‖ ^ 2 ≤ dotProduct (fun i ↦ v i) (e (fun _ _ ↦ 1) k *ᵥ (fun i ↦ v i))) ∧
            let C_low := lowFrequencyConstant n γ R₀
            0 ≤ C_low ∧
            (∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)),
              Integrable f → MemLp f 2 volume →
              γ * (∫ x, ‖f x‖ ^ 2) - C_low * (∫ x, ‖f x‖) ^ 2 ≤
                euclideanFrozenEnergy (e (fun _ _ ↦ 1)) f) ∧
            (∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)), MemLp f 2 volume →
              ∀ K : Set (Euclidean n), MeasurableSet K → volume K ≠ ⊤ →
              (∀ᵐ x, x ∉ K → f x = 0) →
              (γ - C_low * (volume K).toReal) * (∫ x, ‖f x‖ ^ 2) ≤
                euclideanFrozenEnergy (e (fun _ _ ↦ 1)) f) ∧
            ∀ (μ : ℝ) (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2),
              (∀ i, 6 * μ < (d' i).a) →
              let data := fun i ↦ normalizedCarrierData (T' i) (Q' i) F (d' i).row (d' i).col
                (Φ i) (Y i) (fun _ ↦ 1) hμ hμcell
                (angularMask (z₀ i) (NormedSpace.normalize (ηb i)) (d' i).ha
                  (angularWidth_spec (d' i).hηb (d' i).hr).1) FixedCutoffs.highFrequency 0
              let a := fun i ↦ coefficientsOfCarrier (data i) (FixedCutoffs.physical hμ 1)
              ∃ (V : I → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
                (A : I → EuclideanL2 n (EuclideanSpace ℂ (Fin n)) →L[ℂ]
                  EuclideanL2 n (EuclideanSpace ℂ (Fin n))),
                (∀ i,
                  (∀ v : carrierInitialTestSpace n,
                    V i (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (data i) v.val) ∧
                  (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ (data i).outputChart → V i f x = 0) ∧
                  (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
                    (∀ v : carrierInitialTestSpace n,
                      W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral (data i) v.val) →
                    W = V i) ∧
                  (∀ w : ComplexOutputL2 n,
                    MemLp (carrierAdjointIntegral (data i) w) 2 (carrierMeasure n) ∧
                    (V i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (data i) w) ∧
                  (realQuadratureChannel (V i)).comp (realQuadratureChannel (V i)).adjoint =
                    realOutputCompression (transferOperator (A i)) ∧
                  (∀ (f : Euclidean n → EuclideanSpace ℂ (Fin n)) (hf : MemLp f 2 volume),
                    ContDiff ℝ ∞ f → HasCompactSupport f →
                    A i (hf.toLp f) =ᵐ[volume] fun x ↦ WithLp.toLp 2
                      (matrixFullAmplitudeOperator
                        (fun x y ξ ↦ fullReflectedMatrixAmplitude (a i) (J i) (u i) (Ω i) (S i)
                          ξ (pairedPosition x y)) (fun y j ↦ f y j) x)) ∧
                  (∀ ξ x y l q,
                    fullReflectedMatrixAmplitude (a i) (J i) (u i) (Ω i) (S i) ξ
                        (pairedPosition x y) l q =
                      (FixedCutoffs.physical hμ 1 x : ℂ) * (FixedCutoffs.physical hμ 1 y : ℂ) *
                        (carrier (fun _ _ ↦ 1) i ((2 * Real.pi) • ξ) l q : ℂ)) ∧
                  ∀ w : OutputL2 n, ‖(realQuadratureChannel (V i)).adjoint w‖ ^ 2 =
                    euclideanFrozenEnergy (carrier (fun _ _ ↦ 1) i)
                      (fun x ↦ euclideanComplexInclusion
                        (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x))) ∧
                let image := fixedPeriodicChannel hμ hμcell (frozenImageArrays (projectedStress F 0))
                ∃ (r : ℝ) (hr : 0 < r) (hrcell : r < 1 / 2), r ≤ μ ∧
                  (∀ w : OutputL2 n,
                    (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r → w z = 0) →
                    γ / 2 * ‖w‖ ^ 2 ≤ ‖(physicalRow image V).adjoint w‖ ^ 2) ∧
                  0 < NormalAugmentation.globalGap (γ / 2) ‖physicalRow image V‖ ∧
                  (∀ w : OutputL2 n,
                    NormalAugmentation.globalGap (γ / 2) ‖physicalRow image V‖ * ‖w‖ ^ 2 ≤
                      inner ℝ (augmentedNormal image V (innerCutoff hr hrcell) w) w) ∧
                  (∀ w : OutputL2 n, ∀ᵐ z ∂volume,
                    centeredTorusRepresentative z ∈ closedBall 0 (r / 2) →
                      exteriorChannel (innerCutoff hr hrcell) w z = 0) := by
  classical
  obtain ⟨R, hR, m, chart, center, ρ, scale, d, hcell, hscale,
    hcenter, hρ, hchart, hcover, hcap', μ₀, hμ₀, hμ₀cell, hμ₀a, δ, hδ, hfamily⟩ :=
    exists_finite_realized_frozen_model_energy hn hD T hBU hframe hs hsradius hsb
      M hκmet hκnormal hcap
  refine ⟨R, hR, m, chart, center, ρ, scale, d, hcell, hscale,
    hcenter, hρ, hchart, hcover, hcap', μ₀, hμ₀, hμ₀cell, hμ₀a, δ, hδ, ?_⟩
  intro F hF hi hrank hM hmet hnormal hclose
  obtain ⟨hlow, hgeom, hreal, hrest⟩ := hfamily F hF hi hrank hM hmet hnormal hclose
  refine ⟨hlow, hgeom, hreal, ?_⟩
  obtain ⟨hR₀, hmodels⟩ := hrest
  refine ⟨hR₀, ?_⟩
  intro Φ Y
  obtain ⟨hecont, hebound, hnonneg, γ, hγ, hgap,
    hlow, hlowEnergy, hsupportEnergy, hconstruct⟩ := hmodels Φ Y
  refine ⟨hecont, hebound, hnonneg, γ, hγ, hgap,
    hlow, hlowEnergy, hsupportEnergy, ?_⟩
  intro μ hμ hμcell hμa
  obtain ⟨V, A, hV, henergy⟩ := hconstruct μ hμ hμcell hμa
  refine ⟨V, A, hV, ?_⟩
  obtain ⟨B, _hB, hbound⟩ := hebound
  exact exists_frozen_row_gap_of_spectral_energy
    (ι := (l : Fin m) × Fin (D.patchCount (R.sourceChart (chart l))))
    (lt_of_lt_of_le (by decide : 0 < 5) hn)
    (projectedStress F 0) _ hecont hγ hbound hnonneg hgap hμ hμcell V
    (fun w ↦ (henergy w).1)

end JanetCartan.ContinuumNormal.FrozenCoercivity
