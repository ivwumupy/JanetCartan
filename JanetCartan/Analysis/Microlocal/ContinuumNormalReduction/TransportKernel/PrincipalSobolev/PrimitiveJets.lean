module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.Jets

/-!
# Primitive production of localized diagonal correction jets

The bounded-frequency error after `app:ch_background:eq:bg-real-symbol`
retains one high geometric norm with shift two after physical localization,
for both the operator kernel and its literal adjoint. All kernel estimates
and smoothness are instantiated from the primitive chart and coefficient data.
The parent construction must supply the stated diagonal-slice coverage.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ComplexConjugate
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol
variable {n N : ℕ}

/-- Uniform global physical jets of the localized diagonal error and its literal
adjoint, from primitive data and fixed smooth compact cutoffs. The single high
norm has precisely the producer's shift two
(`app:ch_background:eq:bg-real-symbol`). -/
theorem exists_localizedDiagonalCorrectionKernel_bound_of_primitiveNorms
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
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    (χ β : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    (hχs : HasCompactSupport χ) (hβs : HasCompactSupport β)
    (s : ℕ) (hs : 2 ≤ s) :
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
      (∀ p ∈ tsupport (diagonalCorrectionMask χ β) ∪
          tsupport (diagonalCorrectionMask β χ),
        ∀ k, ‖k‖ ≤ max 2 (2 * Clower) →
          (p.1, p.1, k) ∈ X ∧ (p.2, p.2, k) ∈ X) →
      ∀ r ≤ s, ∀ i j : Fin n, ∀ p : Euclidean n × Euclidean n,
        ‖iteratedFDeriv ℝ r (Function.uncurry
          (localizedDiagonalCorrectionKernel d J u Ω S χ β i j)) p‖ ≤ C * H ∧
        ‖iteratedFDeriv ℝ r (Function.uncurry
          (localizedDiagonalCorrectionAdjointKernel d J u Ω S χ β i j)) p‖ ≤ C * H := by
  obtain ⟨C, hC, hb⟩ := exists_diagonalCompletionErrorKernel_bound_of_primitiveNorms
    (N := N) c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hClower hℓ hℓone hlow hS s hs
  let F := diagonalCorrectionLocalizedJetConstant χ β s (max 2 (2 * Clower))
  let G := diagonalCorrectionLocalizedJetConstant β χ s (max 2 (2 * Clower))
  have hF : 0 ≤ F := diagonalCorrectionLocalizedJetConstant_nonneg _ _ _ _
  have hmax : 0 < max F G + 1 := by have := le_max_left F G; linarith
  refine ⟨(max F G + 1) * C, mul_pos hmax hC, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower
    hreflect hpunctured hcover r hr i j p
  have hbound := hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower
    hreflect hpunctured
  have hright := augmentedTransportGradient_inverseCoordinates Y u heq
  have ha := (amplitude_smooth_and_derivatives_of_punctured_buffer d J u
    (augmentedTransportGradient Y) hΩ hreg hu hmap hright hsupp hpunctured
    hzero hCupper hℓ hlow hupper hS).1
  have hh := homogeneousAmplitude_contDiffOn_punctured d J u
    (augmentedTransportGradient Y) hΩ hreg hu hmap hright hsupp hpunctured hS
  have he := reflectedCompletionError_contDiff d J u Ω S ha hh
  have hCH : 0 ≤ C * H := mul_nonneg hC.le (by linarith)
  constructor
  · refine (norm_iteratedFDeriv_localizedDiagonalCorrectionKernel_le d J u Ω S χ β
      he hone hClower hlower hχ hβ hχs hβs s hCH i j ?_ r hr p).trans ?_
    · intro q hq l hl
      simpa only [mul_assoc] using (hbound q
        (fun k hk ↦ (hcover q (Or.inl hq) k hk).1)
        (fun k hk ↦ (hcover q (Or.inl hq) k hk).2) l hl i j).1
    · change F * (C * H) ≤ _
      calc
        _ ≤ (max F G + 1) * (C * H) := mul_le_mul_of_nonneg_right
          ((le_max_left F G).trans (by linarith)) hCH
        _ = _ := by ring
  · refine (norm_iteratedFDeriv_localizedDiagonalCorrectionAdjointKernel_le d J u Ω S χ β
      he hone hClower hlower hχ hβ hχs hβs s hCH i j ?_ r hr p).trans ?_
    · intro q hq l hl
      simpa only [mul_assoc] using (hbound q
        (fun k hk ↦ (hcover q (Or.inr hq) k hk).1)
        (fun k hk ↦ (hcover q (Or.inr hq) k hk).2) l hl i j).2
    · change G * (C * H) ≤ _
      calc
        _ ≤ (max F G + 1) * (C * H) := mul_le_mul_of_nonneg_right
          ((le_max_right F G).trans (by linarith)) hCH
        _ = _ := by ring

end JanetCartan.ContinuumRow.TransportKernel
