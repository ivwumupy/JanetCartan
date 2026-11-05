module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.PrimitiveJets
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.PrincipalSobolev.OperatorBounds

/-!
# Primitive-input smoothing of the diagonal correction

The bounded-frequency diagonal error following
`app:ch_background:eq:bg-real-symbol` and its literal adjoint map every
Euclidean L² input to every integer Sobolev order. The fixed cutoffs contribute
only their jets and support volumes. At budget order `s ≥ 2`, the bound uses
one high norm with shift two and covers every output order through `s`.
The parent supplies the primitive geometry and coverage of both diagonal
slices; no smoothness, kernel jet, or operator estimate is assumed separately.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ComplexConjugate
namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction TransportSymbol Pseudodifferential
open FiniteChain.Retarded.KernelSobolev
variable {n N : ℕ}

set_option maxHeartbeats 800000 in
/-- The literal diagonal correction in the principal reduction, and its actual
Hilbert adjoint, satisfy uniform L²-to-integer-Sobolev bounds from the primitive
producer. The constant precedes all variable geometry and the high norm `H`;
the only high budget is `1 + cNorm L (s + 2) Y ≤ B * H`. Both diagonal slices
are required on the fixed cutoff supports, exactly as in `PrincipalBounds`
(`app:ch_background:eq:bg-real-symbol`). -/
theorem exists_localizedDiagonalCorrectionOperator_sobolev_of_primitiveNorms
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
      (hone : ∀ r : ℝ, 2 ≤ r → d.high r = 1) →
      (∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖) →
      (hlower : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Clower * ‖(u p).2‖) →
      (∀ x ∈ X, (x.1, x.2.1, -x.2.2) ∈ X) →
      (closure (augmentedTransportGradient Y '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) →
      (∀ p ∈ tsupport (diagonalCorrectionMask χ β) ∪
          tsupport (diagonalCorrectionMask β χ),
        ∀ k, ‖k‖ ≤ max 2 (2 * Clower) →
          (p.1, p.1, k) ∈ X ∧ (p.2, p.2, k) ∈ X) →
      ∃ he : ContDiff ℝ ∞ (reflectedCompletionError d J u Ω S),
        ∀ r ≤ s, ∀ i j : Fin n, ∀ f : Lp ℂ 2 (volume : Measure (Euclidean n)),
          let T := localizedDiagonalCorrectionOperator d J u Ω S χ β he hone hClower
            hlower hχ hβ hχs hβs i j
          (MemFourierSobolev (r : ℝ) (T f) ∧
            fourierSobolevNorm (r : ℝ) (T f) ≤ C * H * ‖f‖) ∧
          (MemFourierSobolev (r : ℝ) (T.adjoint f) ∧
            fourierSobolevNorm (r : ℝ) (T.adjoint f) ≤ C * H * ‖f‖) := by
  obtain ⟨C, hC, hb⟩ := exists_localizedDiagonalCorrectionKernel_bound_of_primitiveNorms
    (N := N) c a b hρ hτ hW hball hK hWK hO houtput hV hL hLV hT hIT hsegT hseg
    A hM hM₀ hB₀ hδ hε hB hη D hfoot hCupper hClower hℓ hℓone hlow hS
    χ β hχ hβ hχs hβs s hs
  let F := compactSupportFactor volume volume (tsupport β) (tsupport χ)
  have hF : 0 ≤ F := compactSupportFactor_nonneg _ _ _ _
  refine ⟨(1 + (n : ℝ)) ^ s * C * (F + 1), by positivity, ?_⟩
  intro d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower
    hreflect hpunctured hcover
  have hbound := hb d Y u J Ω U Z X R H hY hYM hΩ hOΩ hu hrange hgap heq hJ hne hdet
    hH hhigh hreg hmap hsupp hR hXR hbuffer hshell hcoeff hzero hone hupper hlower
    hreflect hpunctured hcover
  have hright := augmentedTransportGradient_inverseCoordinates Y u heq
  have ha := (amplitude_smooth_and_derivatives_of_punctured_buffer d J u
    (augmentedTransportGradient Y) hΩ hreg hu hmap hright hsupp hpunctured
    hzero hCupper hℓ hlow hupper hS).1
  have hh := homogeneousAmplitude_contDiffOn_punctured d J u
    (augmentedTransportGradient Y) hΩ hreg hu hmap hright hsupp hpunctured hS
  have he := reflectedCompletionError_contDiff d J u Ω S ha hh
  refine ⟨he, fun r hr i j f ↦ ?_⟩
  have hCH : 0 ≤ C * H := mul_nonneg hC.le (by linarith)
  obtain ⟨hm, hn⟩ := localizedDiagonalCorrectionOperator_sobolev_of_jets
    d J u Ω S χ β he hone hClower hlower hχ hβ hχs hβs s hCH i j
    (fun l hl p ↦ (hbound l hl i j p).1) f
  obtain ⟨ham, han⟩ := localizedDiagonalCorrectionOperator_adjoint_sobolev_of_jets
    d J u Ω S χ β he hone hClower hlower hχ hβ hχs hβs s hCH j i
    (fun l hl p ↦ (hbound l hl j i p).2) f
  have hr' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hr
  have hconst : ((1 + (n : ℝ)) ^ s * (C * H) * F) * ‖f‖ ≤
      ((1 + (n : ℝ)) ^ s * C * (F + 1)) * H * ‖f‖ := by
    have h : 0 ≤ (1 + (n : ℝ)) ^ s * (C * H) * ‖f‖ := by positivity
    nlinarith only [h]
  refine ⟨⟨hm.mono hr', (fourierSobolevNorm_mono hm hr').trans (hn.trans hconst)⟩,
    ham.mono hr', (fourierSobolevNorm_mono ham hr').trans (han.trans ?_)⟩
  simpa only [F, compactSupportFactor, mul_comm (Real.sqrt (volume.real (tsupport χ)))
    (Real.sqrt (volume.real (tsupport β)))] using hconst

end JanetCartan.ContinuumRow.TransportKernel
