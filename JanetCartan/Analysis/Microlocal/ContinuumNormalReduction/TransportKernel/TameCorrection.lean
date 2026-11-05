module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.CorrectionKernelBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.GlobalSmooth

/-!
# Primitive bounds for the literal correction and its adjoint

The bounded-frequency error after `app:ch_background:eq:bg-real-symbol` has
finite physical kernel jets controlled by one high norm. This module connects
the primitive-norm amplitude producer to differentiation under the literal
Lebesgue frequency integral. The coefficient order is `s`, the geometric order
is `s+2`, and neither kernel smoothness nor amplitude bounds are assumptions.
The geometric producer must supply annular containment, the conic support
buffer, frequency comparisons and primitive finite norms. The physical slices
in the conclusion specify exactly where those local estimates are available.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius ComplexConjugate
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol
variable {n N : ℕ}

/-- The correction and its literal conjugate transpose have quantitative
physical jets from primitive data, with one high norm and fixed shift two.
This instantiates both the amplitude bound and the smoothness needed for
compact-frequency differentiation. The consumer is the bounded-frequency
term of the normal reduction following `app:ch_background:eq:bg-real-symbol`.
No output measure is transported and no carrier bound is assumed. -/
theorem exists_completionErrorKernel_bound_of_primitiveNorms
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
    {Cupper Clower ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hClower : 0 < Clower)
    (hℓ : 0 < ℓ) (hℓone : ℓ ≤ 1) (hlow : Cupper * ℓ ≤ 1)
    {S : Set (Euclidean 2)} (hS : IsCompact S) (s : ℕ) (hs : 2 ≤ s) :
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
      IsOpen R → completionAnnulus X ℓ Clower ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ completionAnnulus X ℓ Clower, ∀ v ∈ S, (x, v) ∈ Ω → (x, v) ∈ closedBall b τ) →
      D.Controls s M₀ B₀ H d →
      (∀ r : ℝ, r ≤ 1 → d.high r = 0) →
      (∀ r : ℝ, 2 ≤ r → d.high r = 1) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Clower * ‖(u p).2‖) →
      (∀ x ∈ X, (x.1, x.2.1, -x.2.2) ∈ X) →
      (closure (augmentedTransportGradient Y '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
      ∀ x : Euclidean n × Euclidean n,
      (∀ k, ‖k‖ ≤ max 2 (2 * Clower) → (x.1, x.2, k) ∈ X) →
      (∀ k, ‖k‖ ≤ max 2 (2 * Clower) → (x.2, x.1, k) ∈ X) →
      ∀ r ≤ s, ∀ i j : Fin n,
        ‖iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
          completionErrorKernel d J u Ω S i j y.1 y.2) x‖ ≤
            (correctionKernelJetConstant n r (max 2 (2 * Clower)) * C) * H ∧
        ‖iteratedFDeriv ℝ r (fun y : Euclidean n × Euclidean n ↦
          conj (completionErrorKernel d J u Ω S j i y.2 y.1)) x‖ ≤
            (correctionKernelJetConstant n r (max 2 (2 * Clower)) * C) * H := by
  obtain ⟨C, hC, hb⟩ := exists_reflectedCompletionError_bound_of_primitiveNorms
    (N := N) c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hClower hℓ hℓone hlow hS s hs
  refine ⟨C, hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower
    hreflect hpunctured x hx hxswap r hr i j
  have hbound := hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower hreflect
  have hright := augmentedTransportGradient_inverseCoordinates Y u heq
  have ha := (amplitude_smooth_and_derivatives_of_punctured_buffer d J u
    (augmentedTransportGradient Y) hΩ hreg hu hmap hright hsupp hpunctured
    hzero hCupper hℓ hlow hupper hS).1
  have hh := homogeneousAmplitude_contDiffOn_punctured d J u
    (augmentedTransportGradient Y) hΩ hreg hu hmap hright hsupp hpunctured hS
  have he := reflectedCompletionError_contDiff d J u Ω S ha hh
  constructor
  · simpa only [mul_assoc] using norm_iteratedFDeriv_completionErrorKernel_le
      d J u Ω S he hone hClower hlower i j r x
      (fun k hk l hl ↦ hbound _ (hx k hk) l (hl.trans hr))
  · simpa only [mul_assoc] using norm_iteratedFDeriv_completionErrorKernel_adjoint_le
      d J u Ω S he hone hClower hlower i j r x
      (fun k hk l hl ↦ hbound _ (hxswap k hk) l (hl.trans hr))

end JanetCartan.ContinuumRow.TransportKernel
