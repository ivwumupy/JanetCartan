module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.GlobalIdentification
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell.Construction
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell.SourceBounds

/-!
# Construct the global carrier normal from supported primitive shell norms

Supported-shell counterpart of
`exists_carrierL2Extension_globalNormal_of_primitiveNorms` for
`app:ch_background:prop:bg-frame`, Step 1. Shell containment is required only
on the closure of the image of the original primitive mask support.
The full conclusion and all other primitive hypotheses are preserved.

The supported transport estimates produce the finite normal bounds and source
jets; the existing kernel extension, literal adjoint, PDO identification and
limit proofs then construct the same uncut carrier and its global real normal.
No operator bound, source Fourier convergence or normal identity is assumed.
The reflected amplitude retains its quadrature factor four. Constants are chosen
before varying fields, high budgets and radial radii; coefficient order is `s`,
geometry order is `s + 2`, and the fixed low geometry order is three.
Use `s = 2 * (n + 1) + 1` for the differential commutator reserve.

Consumers: `jc-continuum-canonical-conic-inputs` and `jc-continuum-row`.
The canonical-conic parent remains responsible for constructing every geometric
input and instantiating this theorem; this is not the unconditional row theorem.
Sources: `app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_background:eq:bg-real-symbol`.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2
variable {n N : ℕ}

private theorem supportedPrimitiveControls_lower_order
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : PrimitiveNormChart E} {r s : ℕ} {M B H : ℝ} {f : E → F}
    (h : D.Controls s M B H f) (hrs : r ≤ s) : D.Controls r M B H f :=
  ⟨h.smooth, h.low, (add_le_add (le_refl 1) (cNorm_mono_order hrs)).trans h.high⟩

private theorem supportedCoefficientControls_lower_order
    {D : CoefficientNormCharts n} {r s : ℕ} {M B H : ℝ} {d : Coefficients n N}
    (h : D.Controls s M B H d) (hrs : r ≤ s) : D.Controls r M B H d :=
  ⟨supportedPrimitiveControls_lower_order h.measurement hrs,
    supportedPrimitiveControls_lower_order h.angular hrs, supportedPrimitiveControls_lower_order h.high hrs,
    supportedPrimitiveControls_lower_order h.normal hrs, supportedPrimitiveControls_lower_order h.reduced hrs⟩

set_option maxHeartbeats 1000000 in
/-- Construct the uncut complex carrier and its literal adjoint and identify
its real normal with the GLOBAL full reflected matrix PDO on the entire output
L² space. All analytic estimates, memberships and limits are discharged from
primitive norms and literal chart/kernel data. The two constants precede the
varying coefficients, geometry, high budget and cutoff radii. The PDO entry
reserve is arbitrary above the PDO threshold; one extra derivative supplies
the differential commutator.
Source: `app:ch_background:prop:bg-frame`, Step 1,
`app:ch_background:eq:bg-full-complex-amplitude`, and `bg-real-symbol`. -/
theorem exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms
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
    ∃ C > 0, ∃ Cpdo > 0, ∀ (d : Coefficients n N)
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
      ∃ (hb : ContDiff ℝ ∞ (Function.uncurry
        (fullReflectedMatrixAmplitude {d with high := h} J u Ω S)))
        (hA : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude {d with high := h} J u Ω S ξ z i j)
          s (Cpdo * H)),
      ∃ U : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        ‖U‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H))) ∧
        ‖U.adjoint‖ ≤ Real.sqrt ((n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H))) ∧
        (∀ v : carrierInitialTestSpace n,
          U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) ∧
        (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → U f x = 0) ∧
        (∀ W : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
          (∀ v : carrierInitialTestSpace n,
            W (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral e v.val) → W = U) ∧
        (∀ w : ComplexOutputL2 n,
          MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
          U.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
        (∀ w : ComplexOutputL2 n,
          Filter.Tendsto (fun k : ℕ ↦
            (hmask ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))).operator.adjoint w)
            Filter.atTop (nhds (U.adjoint w))) ∧
        (realQuadratureChannel U).comp (realQuadratureChannel U).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator _hn Rbox
              (fullReflectedMatrixAmplitude {d with high := h} J u Ω S) hb
              (fullReflectedMatrixAmplitude_supportedInCenteredBox
                {d with high := h} J u Ω S Rbox _hsupport)
              (Cpdo * H) (fun i j ξ is his ↦ hA i j ξ is (by omega)))) := by
  classical
  obtain ⟨C, hC, hconstruct⟩ := exists_carrierL2Extension_supported_and_uniformNormals_of_primitiveNorms
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS s hs
    hh hzero htail hκ hcκ hκone
  obtain ⟨Cpdo, hCpdo, hbudget⟩ := exists_fullReflectedMatrixAmplitude_supported_bounds_of_primitiveNorms
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS s hs
    hh hzero htail
  choose Csource hCsource hsource using fun i j : Fin n ↦
    SourceConvergence.exists_reflected_supported_regularized_source_bounds_of_primitiveNorms (N := N)
      c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
      A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS
      hh hzero htail hκ hcκ hκone i j
  refine ⟨C, hC, Cpdo, hCpdo, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize hn Rbox hsupport hreserve e Zp hZp hangular Cmask hCmask
    hkernel hamp Kout hcell hchart hpoint χ hχ hχsmooth hχcompact hχone
    charts symbols ha hJac hInv hDom hSpec Cfreq hCfreq hcomparison
  have hreserve₀ : 2 * (n + 1) ≤ s := by omega
  obtain ⟨Lmask, hLmask, Mmask, hMmask, hmask, hnormals, htests,
      Tcarrier, hT, hTadj, hTtest, hTsupport, hunique⟩ :=
    hconstruct d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
      hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
      hupper hpunctured hnormalize hn Rbox hsupport hreserve₀ e Zp hZp hangular Cmask hCmask
      hkernel hamp Kout hcell hchart hpoint χ hχ hχsmooth hχcompact hχone
      charts symbols ha hJac hInv hDom hSpec Cfreq hCfreq hcomparison
  obtain ⟨hb, hA, _⟩ := hbudget d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  have hsourceHigh : 1 + cNorm L (n + 5) Y ≤ B * H :=
    (add_le_add (le_refl 1) (cNorm_mono_order (by omega : n + 5 ≤ s + 2))).trans hhigh
  have hsourceCoeff : D.Controls (n + 3) M₀ B₀ H d :=
    supportedCoefficientControls_lower_order hcoeff (by omega)
  have hsourceEntries (i j : Fin n) :=
    (hsource i j d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
      hH hsourceHigh hreg hmap hsupp hR hXR hbuffer hshell hsourceCoeff hscale huScale hJScale
      hupper hpunctured hnormalize).1
  have hnormalNonneg : 0 ≤ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (fixedBoxAmplitudeConstant_nonneg n Rbox)
      (mul_nonneg hC.le (zero_le_one.trans hH)))
  let hm (k : ℕ) := hmask ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))
  have hnormal (k : ℕ) := (hnormals ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k))).1
  refine ⟨Lmask, hLmask, Mmask, hMmask, hmask, hnormals, htests, hb, hA,
    Tcarrier, hT, hTadj, hTtest, hTsupport, hunique, ?_, ?_, ?_⟩
  · intro w
    exact ⟨(carrierAdjointIntegral_memLp_bound_of_uniformNormals
        hangular hκone hm hnormalNonneg hnormal w).1,
      carrierRealization_adjoint_eq_literal hangular hκone hm Tcarrier hTtest
        hnormalNonneg hnormal w⟩
  · exact parameterRegularizedOperator_adjoint_tendsto hangular hκone hm Tcarrier hTtest
      hnormalNonneg hnormal
  · exact carrierRealization_realNormal_eq_transfer_fullReflectedMatrixOperator
      hn κ hκ hcκ hκone hangular hm hcell hchart hpoint χ hχ hχsmooth hχcompact
      {d with high := h} J u Ω S hχone
      (fun k ↦ charts ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ symbols ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ ha ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ hJac ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ hInv ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ hDom ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      (fun k ↦ hSpec ((k : ℝ) + 1) (by exact le_add_of_nonneg_left (Nat.cast_nonneg k)))
      hCfreq hcomparison hupper
      (fun Q hQ i j ↦ (hsourceEntries i j Q hQ).1)
      (fun i j _ ↦ Csource i j * H)
      (fun Q hQ i j x y ξ k hk ↦ (hsourceEntries i j Q hQ).2.1 (x, y, ξ) k (by omega))
      Rbox hsupport hb
      (fullReflectedMatrixAmplitude_supportedInCenteredBox {d with high := h} J u Ω S Rbox hsupport)
      (Cpdo * H) (fun i j ξ is his ↦ hA i j ξ is (his.trans hreserve₀))
      Tcarrier hTtest _ hnormalNonneg hnormal

end JanetCartan.ContinuumRow.CarrierNormalRealization
