module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.Cutoff

/-!
# Primitive production of the source convergence inputs

For `app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_background:eq:bg-real-symbol`, instantiate the published primitive
norm producer. Coefficient order `n+3` and geometry order `n+5` produce all
four source integrals, with `n+1` derivatives on the source test. The actual
geometric chart, support buffers and torus-source matching remain with the
normal construction owner.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

/-- Primitive geometric and coefficient norms produce the full reflected
entry's joint source reserve, its linear high-norm majorant, and all four
integrability fields of `realNormal_principal_reduction_of_test_limit`.
No source Fourier integrability, kernel bound, or normal identity is assumed.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`. -/
theorem exists_reflected_source_bounds_of_primitiveNorms
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
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ r, r ≤ 1 → h r = 0) (htail : ∀ r, 2 ≤ r → h r = 1)
    (i j : Fin n) :
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
      1 ≤ H → 1 + cNorm L (n + 5) Y ≤ B * H →
      PrimitiveRegularity d J U → MapsTo (inverseCoordinates u) Ω U →
      (∀ p ∈ U, d.measurement p.1.1 ≠ 0 → d.measurement p.1.2 ≠ 0 →
        d.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Z) →
      IsOpen R → X ⊆ R →
      closure (augmentedTransportGradient Y '' Z) ∩ (R ×ˢ univ) ⊆ Ω →
      (∀ x ∈ X, ∀ v ∈ S, (x, v) ∈ Ω → (x, v) ∈ closedBall b τ) →
      D.Controls (n + 3) M₀ B₀ H d →
      (∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2)) →
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p)) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (closure (augmentedTransportGradient Y '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
      (∀ p : Variables n, ℓ ≤ ‖p.2.2‖ → scaleFrequency (ℓ / ‖p.2.2‖) p ∈ X) →
      let c₀ := fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)
      ContDiff ℝ ∞ (fun p : Variables n ↦ c₀ p.1 p.2.1 p.2.2) ∧
      (∀ p : Variables n, ∀ k ≤ n + 3,
        ‖iteratedFDeriv ℝ k (fun q : Variables n ↦ c₀ q.1 q.2.1 q.2.2) p‖ ≤ C * H) ∧
      ∀ (basis : OrthonormalBasis (Fin n) ℝ (Euclidean n))
        (β : Euclidean n → ℝ), ContDiff ℝ ∞ β →
        ∀ (Bβ : ℕ → ℝ), (∀ k ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ k β y‖ ≤ Bβ k) →
        ∀ (f : Euclidean n → ℂ), ContDiff ℝ (n + 1) f → HasCompactSupport f →
        ∀ x : Euclidean n,
          (∀ ξ, ‖sourceAmplitudeTransform c₀ f x ξ‖ ≤
            sourceTestMajorant f (fun _ ↦ C) ξ * H) ∧
          Integrable (sourceAmplitudeTransform c₀ f x) ∧
          Integrable (sourceAmplitudeTransform (diagonalAmplitude c₀ β) f x) ∧
          Integrable (sourceAmplitudeTransform (diagonalRemainderAmplitude basis c₀ β) f x) ∧
          Integrable (sourceAmplitudeTransform (fullTaylorCoefficient c₀ β) f x) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_transportAmplitude_global_mixed_bound_of_primitiveNorms (N := N)
    c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hℓ hℓone hlow hS
    (n + 3) (by omega) hh hzero htail
  obtain ⟨C₁, hC₁, hentry⟩ := exists_reflectedEntry_joint_bound_of_mixed (N := N) (n + 3) i j
  refine ⟨C₁ * C₀, mul_pos hC₁ hC₀, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale
    hupper hpunctured hnormalize
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hhigh' : 1 + cNorm L (n + 3 + 2) Y ≤ B * H := by
    simpa [Nat.add_assoc] using hhigh
  have hm := hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh' hreg hmap hsupp hR hXR hbuffer hshell hcoeff hscale huScale hJScale hupper
  have hreg' : PrimitiveRegularity {d with high := h} J U := {hreg with high := hh}
  have ha := (amplitude_smooth_and_derivatives_of_punctured_buffer
    {d with high := h} J u (augmentedTransportGradient Y) hΩ hreg' hu hmap
    (augmentedTransportGradient_inverseCoordinates Y u heq) hsupp hpunctured
    hzero hCupper hℓ hlow hupper hS).1
  obtain ⟨hc, hbound⟩ := hentry {d with high := h} J u Ω S ha (C₀ * H)
    (mul_nonneg hC₀.le hH₀) (fun p ↦ hm p (hnormalize p))
  simp only [← mul_assoc] at hbound
  refine ⟨hc, hbound, ?_⟩
  intro basis β hβ Bβ hBβ f hf hfc x
  refine ⟨?_, source_integrability_of_joint_bounds basis
    (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
      (x, y, (2 * Real.pi) • ξ) i j : ℂ)) β f x hc hβ hf hfc
    (fun _ ↦ C₁ * C₀ * H) Bβ (fun k hk y ξ ↦ hbound (x, y, ξ) k hk) hBβ⟩
  intro ξ
  simpa only [sourceTestMajorant_mul] using
    norm_sourceAmplitudeTransform_le_sourceTestMajorant
      (fun x y ξ ↦ (reflectedSymbolAmplitude {d with high := h} J u Ω S
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) hc f hf hfc
      (fun _ ↦ (C₁ * C₀) * H) (fun x y ξ k hk ↦ hbound (x, y, ξ) k (by omega)) x ξ

end JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
