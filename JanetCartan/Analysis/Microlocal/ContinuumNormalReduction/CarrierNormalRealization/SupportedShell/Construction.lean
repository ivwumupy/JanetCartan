module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Extension
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell.PrimitiveBudget

/-!
# Construct the carrier extension from supported primitive shell norms

Construct the radial masks, uniform complex and real normal bounds, and the
literal uncut carrier extension from the supported full-amplitude bounds.
Only shell containment is localized to the transported original mask support;
all other primitive hypotheses and the full conclusion are retained.
The constant precedes varying fields, the common high budget and cutoff radii.

The consumer `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`
adds the literal adjoint and global PDO identity using the existing limit proofs.
Actual geometric instantiation remains with the canonical-conic parent.
Source: `app:ch_background:prop:bg-frame`, Step 1,
`app:ch_background:eq:bg-full-complex-amplitude`, and
`app:ch_background:eq:bg-real-symbol`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2
variable {n N : ℕ}

/-- Construct the actual complex carrier extension and prove cutoff-independent
complex and real normal bounds from primitive finite norms, keeping a single
high budget and the explicit matrix and fixed-box factors. Every finite operator
is constructed with the compact parameter truncation of the original radial
mask. No operator identity, desired bound, source Fourier integrability or limit
is an input. Source: `app:ch_background:prop:bg-frame`, Step 1,
`app:ch_background:eq:bg-full-complex-amplitude`, and `bg-real-symbol`. -/
theorem exists_carrierL2Extension_supported_and_uniformNormals_of_primitiveNorms
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    (b : Variables n × Euclidean 2) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    {O : Set (Variables n × Euclidean 2)} (hO : IsOpen O)
    (houtput : closedBall b τ ⊆ O)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {M M₀ B₀ δ ε B : ℝ} (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) (hB₀ : 1 ≤ B₀)
    (hδ : 0 < δ) (hε : 0 < ε) (hB : 0 ≤ B)
    (hη : ∀ p ∈ closedBall a ρ, ε ≤ ‖p.2.2‖)
    (D : CoefficientNormCharts n)
    (hfoot : ∀ p ∈ closedBall a ρ, D.Contains p)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ)
    (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1)
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκone : ∀ t ∈ Icc (0 : ℝ) 1, κ t = 1) :
    ∃ C > 0, ∀ (d : Coefficients n N)
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (J : InputVariables n → ℝ) (Ω : Set (Variables n × Euclidean 2))
      (U Z : Set (InputVariables n)) (X R : Set (Variables n)) (H : ℝ),
      ContDiffOn ℝ ∞ Y V → cNorm L 3 Y ≤ M →
      IsOpen Ω → O ⊆ Ω → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) (closedBall b τ) (closedBall a ρ) →
      (∀ q ∈ closedBall a ρ,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      EqOn J (transportAbsoluteJacobian c Y) W → (∀ p ∈ W, J p ≠ 0) →
      (∀ q ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y q) →
      1 ≤ H → 1 + cNorm L (s + 2) Y ≤ B * H →
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ closure (augmentedTransportGradient Y '' Z) →
        (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (closure (augmentedTransportGradient Y '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
      (∀ p : Variables n, ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      ∀ (_hn : 0 < n) (Rbox : ℝ)
        (_hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ Rbox)
        (_hreserve : 2 * (n + 1) ≤ s)
        (e : CarrierData n N) (Zp : Set CarrierParameter) (_hZp : IsCompact Zp)
        (_hangular : ∀ z ∉ Zp, ∀ η, e.angularCutoff z η = 0)
        (Cmask : ℝ) (_hCmask : 0 ≤ Cmask)
        (_hkernel : StronglyMeasurable (Function.uncurry (carrierKernel e)))
        (_hamp : ∀ x z, ‖carrierAmplitude e x z‖ ≤ Cmask * Real.sqrt ‖z.2‖)
        (Kout : Set (Euclidean n)) (_hcell : Kout ⊆ halfOpenCell n)
        (_hchart : e.outputChart = torusChart Kout)
        (_hpoint : ∀ z ∈ e.outputChart, e.chartPoint z = centeredTorusRepresentative z)
        (χ : Euclidean n → ℝ) (_hχ : ∀ y ∉ Kout, χ y = 0)
        (_hχsmooth : ContDiff ℝ ∞ χ) (_hχcompact : HasCompactSupport χ)
        (_hχone : ∀ y, d.measurement y ≠ 0 → χ y = 1)
        (charts : ∀ (Q : ℝ), 1 ≤ Q → ∀ x, x ∈ e.outputChart →
          ∀ y, y ∈ e.outputChart → ChartInputs e (radialCarrierMask κ Q) x y)
        (symbols : ∀ Q hQ x hx y hy, SymbolInputs (charts Q hQ x hx y hy))
        (_ha : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).coefficients =
          regularizedCoefficients {d with high := h} κ Q)
        (_hJac : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).jacobian = J)
        (_hInv : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).inverse = u)
        (_hDom : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).domain = Ω)
        (_hSpec : ∀ Q hQ x hx y hy, (symbols Q hQ x hx y hy).spectatorSupport = S)
        (Cfreq : ℝ) (_hCfreq : 0 ≤ Cfreq)
        (_hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Cfreq * ‖(u p).2‖),
      ∃ Lmask > 0, ∃ Mmask ≥ 0,
      ∃ hmask : ∀ (Q : ℝ), 1 ≤ Q → CarrierRegularization.MaskHypotheses e
        (parameterTruncatedMask Zp (radialCarrierMask κ Q)) Zp (Lmask * Q) Mmask Cmask,
      (∀ (Q : ℝ) (hQ : 1 ≤ Q),
        ‖(hmask Q hQ).operator.comp (hmask Q hQ).operator.adjoint‖ ≤
            (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H)) ∧
          ‖(realQuadratureChannel (hmask Q hQ).operator).comp
            (realQuadratureChannel (hmask Q hQ).operator).adjoint‖ ≤
            (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H))) ∧
      (∀ v : carrierInitialTestSpace n,
        MemLp (carrierTestIntegral e v.val) 2 volume ∧
        (eLpNorm (carrierTestIntegral e v.val) 2 volume).toReal ≤
          Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H))) *
            ‖carrierInitialTestToLp v‖) ∧
      ∃ U : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        ‖U‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H))) ∧
        ‖U.adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H))) ∧
        (∀ v : carrierInitialTestSpace n,
          U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → U f x = 0) ∧
        ∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ v : carrierInitialTestSpace n,
            W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = U := by
  classical
  obtain ⟨C, hC, hbudget⟩ := exists_fullReflectedMatrixAmplitude_supported_regularized_bounds_of_primitiveNorms
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS s hs
    hh hzero htail hκ hcκ
  refine ⟨C, hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize hn Rbox hsupport hreserve e Zp hZp hangular Cmask hCmask
    hkernel hamp Kout hcell hchart hpoint χ hχ hχsmooth hχcompact hχone
    charts symbols ha hJac hInv hDom hSpec Cfreq hCfreq hcomparison
  have hentries := hbudget d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  choose hb hA hop using hentries
  obtain ⟨Lmask, hLmask, Mmask, hMmask, hm⟩ := exists_radialCarrierMask_hypotheses
    e Zp hZp hκ.continuous hcκ hCmask hkernel hamp
  let hmask (Q : ℝ) (hQ : 1 ≤ Q) := hm Q (zero_lt_one.trans_le hQ)
  refine ⟨Lmask, hLmask, Mmask, hMmask, hmask, ?_, ?_⟩
  · intro Q hQ
    exact regularized_normal_norm_bounds hn hangular (hmask Q hQ) hcell hchart hpoint
      χ hχ hχsmooth hχcompact (regularizedCoefficients {d with high := h} κ Q)
      J u Ω S hχone (charts Q hQ) (symbols Q hQ) (ha Q hQ) (hJac Q hQ) (hInv Q hQ)
      (hDom Q hQ) (hSpec Q hQ)
      (regularizedCoefficients_high_hasCompactSupport {d with high := h} hcκ
        (ne_of_gt (zero_lt_one.trans_le hQ)))
      hCfreq hcomparison Rbox (hb Q hQ) hsupport (C * H)
      (fun i j ξ is his ↦ hA Q hQ i j ξ is (his.trans hreserve))
  · exact exists_carrierL2Extension_of_fullReflectedMatrixBounds hn e hangular κ hcκ hκone
      (fun k ↦ hmask (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))) hcell hchart hpoint χ hχ hχsmooth hχcompact
      {d with high := h} J u Ω S hχone
      (fun k ↦ charts (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))) (fun k ↦ symbols (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ ha (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))) (fun k ↦ hJac (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ hInv (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))) (fun k ↦ hDom (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ hSpec (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))) hCfreq hcomparison Rbox hsupport
      (fun k ↦ hb (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))) (C * H) (mul_nonneg hC.le (zero_le_one.trans hH))
      (fun k i j ξ is his ↦ hA (k + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)) i j ξ is (his.trans hreserve))

end JanetCartan.ContinuumRow.CarrierNormalRealization
