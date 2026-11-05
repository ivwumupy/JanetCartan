module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Assembly

/-!
# Global literal coordinate-inverse primitives

This instantiates the global primitive assembly with the original masked
`j_S U⁻¹` amplitude from `app:ch_response:eq:direct-envelope-profile`.
The only transport inverse input is its zeroth-order gap. The actual Jacobian
and transport annular jets, including their smoothness, remain the response
geometry producer's obligation. No adjoint amplitude is substituted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives
open FourierIntegral

/-- Global primitive representatives for the literal coordinate inverse,
including all source/target/frequency/parameter masks and both positions.
Constants and cutoff are chosen before scale, frequency, phase and transport.
The conclusion supplies the exact global jet interface and agreement on a
neighborhood of the complete selected support. Only primitive annular jets
of `phaseJacobian` and the actual transport, and its value-level inverse gap,
are supplied by geometry; every positive-order inverse jet is derived.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_global_literal_primitives {n r p : ℕ}
    {X V : Set (Euclidean n)} {C : Set (Euclidean p)}
    (hX : IsOpen X) (hV : IsOpen V) (hC : IsOpen C)
    {Ksel : Set (ParameterAmplitudePoint n (Euclidean p))}
    (hKsel : IsCompact Ksel) (hKU : Ksel ⊆ (X ×ˢ X ×ˢ V) ×ˢ C)
    (A F J T Q : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hF : ∀ j, 0 ≤ F j)
    (hJ : ∀ j, 0 ≤ J j) (hT : ∀ j, 0 ≤ T j) (hQ : ∀ j, 0 ≤ Q j)
    (Z M Mt : ℝ) (hZ : 0 ≤ Z) :
    ∃ (χ : ParameterAmplitudePoint n (Euclidean p) → ℝ)
      (Ω : Set (ParameterAmplitudePoint n (Euclidean p))) (G : ℕ → ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ (X ×ˢ X ×ˢ V) ×ˢ C ∧
      IsOpen Ω ∧ Ksel ⊆ Ω ∧ Ω ⊆ (X ×ˢ X ×ˢ V) ×ˢ C ∧
      EqOn χ (fun _ ↦ 1) Ω ∧ (∀ j, 0 ≤ G j) ∧
      ∀ (L ρ : ℝ) (N Rstar : ℕ), 1 ≤ L → 2 ≤ Rstar →
      ∀ (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean p → Euclidean n)
        (t : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
        (χs χt χg : Euclidean n → ℝ) (q : Euclidean p × Euclidean n → ℂ)
        (D : Set (Euclidean n)),
      IsOpen D → Convex ℝ D →
      (∀ c ∈ C, ζ c ∈ D) → (∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D) →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) → ContDiffOn ℝ ∞ ζ C →
      ContDiffOn ℝ ∞ (normalizedReverseMask χs χt χg ρ) (X ×ˢ X ×ˢ D) →
      ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean n × Euclidean n ↦
        phaseJacobian S w.2.1 (ρ • w.2.2)) (X ×ˢ X ×ˢ D) →
      ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean n × Euclidean n ↦
        t w.2.1 (ρ • w.2.2)) (X ×ˢ X ×ˢ D) →
      (∀ w ∈ X ×ˢ X ×ˢ D, IsUnit (t w.2.1 (ρ • w.2.2))) →
      (∀ w ∈ X ×ˢ X ×ˢ D, ‖(t w.2.1 (ρ • w.2.2))⁻¹‖ ≤ Mt) →
      ContDiffOn ℝ ∞ q (C ×ˢ V) →
      ∀ (b K : ℝ), 0 < b → (∀ c ∈ C, Metric.closedBall (ζ c) b ⊆ D) →
      (∀ x ∈ X, ∀ c ∈ C, IsUnit (mixedPhaseOperator S x (ζ c))) →
      (∀ x ∈ X, ∀ c ∈ C, ‖Ring.inverse (mixedPhaseOperator S x (ζ c))‖ ≤ M) →
      0 ≤ K → (∀ x ∈ X, ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K) →
      (∀ ε ∈ V, ‖ε‖ ≤ averagedMixedSelectorRadius b M K) →
      (∀ j ≤ N + 2, ∀ w ∈ X ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry S) w‖ ≤ A j * L ^ (j - Rstar)) →
      (∀ j ≤ N, ∀ w ∈ X ×ˢ X ×ˢ D,
        ‖iteratedFDeriv ℝ j (normalizedReverseMask χs χt χg ρ) w‖ ≤ F j) →
      (∀ j ≤ N, ∀ w ∈ X ×ˢ X ×ˢ D,
        ‖iteratedFDeriv ℝ j (fun v : Euclidean n × Euclidean n × Euclidean n ↦
          phaseJacobian S v.2.1 (ρ • v.2.2)) w‖ ≤ J j * L ^ (j - (Rstar - 2))) →
      (∀ j, 1 ≤ j → j ≤ N → ∀ w ∈ X ×ˢ X ×ˢ D,
        ‖iteratedFDeriv ℝ j (fun v : Euclidean n × Euclidean n × Euclidean n ↦
          t v.2.1 (ρ • v.2.2)) w‖ ≤ T j * L ^ (j - (Rstar - 2))) →
      (∀ j ≤ N, ∀ w ∈ C ×ˢ V, ‖iteratedFDeriv ℝ j q w‖ ≤ Q j) →
      (∀ j, 1 ≤ j → j ≤ N + 1 → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z) →
      tsupport (normalizedParameterAmplitude (ReverseDerivative.literalAmplitude S t χs χt χg) q ζ ρ) ⊆ Ksel →
      ContDiff ℝ ∞ (cutoffExtension χ (selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ)) ∧
      HasCompactSupport (cutoffExtension χ (selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ)) ∧
      tsupport (cutoffExtension χ (selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ)) ⊆ (X ×ˢ X ×ˢ V) ×ˢ C ∧
      tsupport (normalizedParameterAmplitude (ReverseDerivative.literalAmplitude S t χs χt χg) q ζ ρ) ⊆ Ω ∧
      (fun w ↦ (cutoffExtension χ (selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ) w).1) =
        normalizedParameterAmplitude (ReverseDerivative.literalAmplitude S t χs χt χg) q ζ ρ ∧
      (∀ w ∈ Ω, cutoffExtension χ (selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ) =ᶠ[𝓝 w]
        selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ) ∧
      (∀ j w, w ∈ Ω → iteratedFDeriv ℝ j (cutoffExtension χ (selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ))
        =ᶠ[𝓝 w] iteratedFDeriv ℝ j (selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ)) ∧
      ∀ j ≤ N, ∀ w, ‖iteratedFDeriv ℝ j
        (cutoffExtension χ (selectedPrimitives (ReverseDerivative.literalAmplitude S t χs χt χg) q S ζ ρ)) w‖ ≤ G j * L ^ (j + 2 - Rstar) := by
  obtain ⟨χ, Ω, G, hχ, hc, hs, hΩ, hKΩ, hΩU, hp, hG, hbuild⟩ :=
    exists_global_selected_primitives (r := r) hX hV hC hKsel hKU
      A (literalAmplitudeConstant r F J T Mt) Q hA
      (literalAmplitudeConstant_nonneg r hF hJ hT Mt) hQ Z M hZ
  refine ⟨χ, Ω, G, hχ, hc, hs, hΩ, hKΩ, hΩU, hp, hG, ?_⟩
  intro L ρ N Rstar hL hR S ζ t χs χt χg q D hD hcD hζD hbuffer hS hζ
    hmask hj ht htu hgap hq b K hb hball hu hM hK hd hε
    hSjet hmaskjet hjjet htjet hqjet hζjet hsupport
  have ha : ContDiffOn ℝ ∞
      (normalizedFullAmplitude (ReverseDerivative.literalAmplitude S t χs χt χg) ρ)
      (X ×ˢ X ×ˢ D) := by
    apply contDiffOn_infty.mpr
    intro k
    exact normalizedLiteralAmplitude_contDiffOn (hmask.of_le (by simp))
      (hj.of_le (by simp)) (ht.of_le (by simp)) htu
  apply hbuild L ρ N Rstar hL hR S ζ
    (ReverseDerivative.literalAmplitude S t χs χt χg) q D hD hcD hζD hbuffer hS hζ ha hq
    b K hb hball hu hM hK hd hε hSjet _ hqjet hζjet hsupport
  intro j hjN w hw
  exact norm_jet_normalizedLiteralAmplitude_le (hmask.of_le (by simp))
    (hj.of_le (by simp)) (ht.of_le (by simp)) htu (hX.prod (hX.prod hD))
    hF hJ hT hL hmaskjet hjjet htjet hjN hw (hgap w hw)

end JanetCartan.ResponseTransfer.GradedPrimitives
