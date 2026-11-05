module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.PrimitiveBudget.Operators
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.GlobalSmooth
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.SupportedShell

/-!
# Full carrier PDO bounds from supported primitive shell norms

For `app:ch_background:prop:bg-frame`, Step 1, localize shell containment to
`closure (augmentedTransportGradient Y '' Z)`, the transported original mask
support. The supported transport producers supply the global mixed estimates;
the existing smooth zero extension and reflected-amplitude deductions supply
joint smoothness, entry budgets, and the actual full PDO operator bounds.
No transformed-density or operator estimate is assumed.

These two producers supply `exists_carrierL2Extension_supported_and_uniformNormals_of_primitiveNorms`
and `exists_carrierL2Extension_supported_globalNormal_of_primitiveNorms`.
Coefficient order is `s`, geometry order is `s + 2`, and fixed low geometry
order is three. Constants precede the varying fields, common high budget and
radial radii. The original spectator measure and quadrature normalization are
unchanged. The canonical-conic parent must still construct the geometric inputs.
Sources: `app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_background:eq:bg-real-symbol`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open ContinuumNormalReduction TransportSymbol TransportKernel
open Pseudodifferential AmplitudeBound PeriodicLocalL2
variable {n N : ℕ}

/-- The full reflected carrier amplitude has joint smoothness, a single-high
physical entry budget through any prescribed finite reserve `s`, and the
explicit vector/periodic/real operator bounds, all from primitive norms.
Use `s = 2 * (n + 1) + 1` for the translation commutator. Coefficient order
is `s`, geometry order is `s + 2`, and low geometry order is three.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`, and bg-frame Step 1. -/
theorem exists_fullReflectedMatrixAmplitude_supported_bounds_of_primitiveNorms
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
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1) :
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
      ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude {d with high := h} J u Ω S)))
        (hA : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude {d with high := h} J u Ω S ξ z i j) s (C * H)),
      ∀ (hn : 0 < n) (Rbox : ℝ)
        (hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ Rbox)
        (hreserve : 2 * (n + 1) ≤ s),
      let T := vectorTwoPositionL2Operator hn Rbox (fullReflectedMatrixAmplitude {d with high := h} J u Ω S)
        hb (fullReflectedMatrixAmplitude_supportedInCenteredBox {d with high := h} J u Ω S Rbox hsupport)
        (C * H) (fun i j ξ is his ↦ hA i j ξ is (his.trans hreserve))
      ‖T‖ ≤ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H)) ∧
        ‖transferOperator T‖ ≤ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H)) ∧
        ‖realOutputCompression (transferOperator T)‖ ≤
          (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H)) := by
  obtain ⟨C₀, hC₀, hmixed⟩ := exists_transportAmplitude_supported_global_mixed_bound_of_primitiveNorms (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS s hs
    hh hzero htail
  obtain ⟨C₁, hC₁, hphysical⟩ := exists_fullReflectedMatrixAmplitude_bounds_of_mixed (N := N) s
  refine ⟨C₁ * C₀, mul_pos hC₁ hC₀, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  have hm := hmixed d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale hupper
  have hreg' : PrimitiveRegularity {d with high := h} J U := {hreg with high := hh}
  have ha := (amplitude_smooth_and_derivatives_of_punctured_buffer
    {d with high := h} J u (augmentedTransportGradient Y) hΩ hreg' hu hmap
    (augmentedTransportGradient_inverseCoordinates Y u heq) hsupp hpunctured
    hzero hCupper hℓ hlow hupper hS).1
  obtain ⟨hb, hA⟩ := hphysical {d with high := h} J u Ω S ha (C₀ * H)
    (mul_nonneg hC₀.le (zero_le_one.trans hH))
    (fun p ↦ hm p (hnormalize p))
  simp only [← mul_assoc] at hA
  exact ⟨hb, hA, fun hn Rbox hsupport hreserve ↦
    fullReflectedMatrixAmplitude_operator_bounds {d with high := h} J u Ω S hb s
      (C₁ * C₀ * H) hA hn Rbox hsupport hreserve⟩

/-- The actual radial regularizations have the same full-amplitude entry
reserve and explicit operator bounds, uniformly for `Q ≥ 1`. The constant
precedes the fields, the single high budget, and the radius; the radial mask
remains squared inside the amplitude. Use `s = 2 * (n + 1) + 1` for
`ContinuumCommutator.Translation.Assembly`, with geometry shift exactly two.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`, and bg-frame Step 1. -/
theorem exists_fullReflectedMatrixAmplitude_supported_regularized_bounds_of_primitiveNorms
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
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
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
      ∀ Q : ℝ, 1 ≤ Q →
      ∃ (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude (regularizedCoefficients {d with high := h} χ Q) J u Ω S)))
        (hA : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude (regularizedCoefficients {d with high := h} χ Q) J u Ω S ξ z i j) s (C * H)),
      ∀ (hn : 0 < n) (Rbox : ℝ)
        (hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ Rbox)
        (hreserve : 2 * (n + 1) ≤ s),
      let T := vectorTwoPositionL2Operator hn Rbox (fullReflectedMatrixAmplitude (regularizedCoefficients {d with high := h} χ Q) J u Ω S)
        hb (fullReflectedMatrixAmplitude_supportedInCenteredBox (regularizedCoefficients {d with high := h} χ Q) J u Ω S Rbox hsupport)
        (C * H) (fun i j ξ is his ↦ hA i j ξ is (his.trans hreserve))
      ‖T‖ ≤ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H)) ∧
        ‖transferOperator T‖ ≤ (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H)) ∧
        ‖realOutputCompression (transferOperator T)‖ ≤
          (n : ℝ) ^ 2 * (fixedBoxAmplitudeConstant n Rbox * (C * H)) := by
  obtain ⟨C₀, hC₀, hmixed⟩ := exists_transportAmplitude_supported_regularized_global_mixed_bound_of_primitiveNorms (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS s hs
    hh hzero htail hχ hcχ
  obtain ⟨C₁, hC₁, hphysical⟩ := exists_fullReflectedMatrixAmplitude_bounds_of_mixed (N := N) s
  refine ⟨C₁ * C₀, mul_pos hC₁ hC₀, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  have hm := hmixed d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale hupper
  have hreg' : PrimitiveRegularity {d with high := h} J U := {hreg with high := hh}
  intro Q hQ
  have ha := (regularizedAmplitude_smooth_and_derivatives_of_punctured_buffer
    {d with high := h} J u (augmentedTransportGradient Y) hΩ hreg' hu hmap
    (augmentedTransportGradient_inverseCoordinates Y u heq) hsupp hpunctured
    hzero hCupper hℓ hlow hupper hS hχ Q).1
  obtain ⟨hb, hA⟩ := hphysical (regularizedCoefficients {d with high := h} χ Q) J u Ω S ha (C₀ * H)
    (mul_nonneg hC₀.le (zero_le_one.trans hH))
    (fun p ↦ hm Q hQ p (hnormalize p))
  simp only [← mul_assoc] at hA
  exact ⟨hb, hA, fun hn Rbox hsupport hreserve ↦
    fullReflectedMatrixAmplitude_operator_bounds (regularizedCoefficients {d with high := h} χ Q) J u Ω S hb s
      (C₁ * C₀ * H) hA hn Rbox hsupport hreserve⟩

end JanetCartan.ContinuumRow.CarrierNormalRealization
