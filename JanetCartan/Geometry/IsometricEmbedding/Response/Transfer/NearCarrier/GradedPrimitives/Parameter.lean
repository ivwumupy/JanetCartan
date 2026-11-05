module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Parameter.Reverse
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Parameter.Pullback

/-!
# Reserve-graded forward and reverse parameter primitives

Local parameter-coefficient input for the parent `GradedPrimitives` global
assembly and `app:ch_response:eq:direct-envelope-profile`.

`norm_jet_parameterPhaseCoefficient_le` derives `C` from its actual integral
and carrier contraction. `norm_jet_signedReverseParameterCoefficient_le`
derives `-C B⁻¹` in the literal composition order, using the inverse jets
proved in `GradedPrimitives.Mixed`. Constants are defined using only finite
primitive profile constants, carrier jets, and the central inverse gap;
they precede scale and frequency. All derivatives are joint, including
carrier parameters and normalized covectors.

`parameterCoefficients_graded_on_amplitude` retains both physical positions.
The forward phase position is first; the reverse phase position is second,
as in the literal forward and reverse kernel definitions. Both projections
are contractions. The unused physical position remains an independent
variable in the derivative domain.

The independent `PhaseJets` producer supplies mixed and covector Hessian
profiles from the primitive phase jets. Fixed carrier jets through `N+1`,
smoothness on buffered convex charts, and primitive central gap/Lipschitz
data are the other inputs. The parent must instantiate those inputs and
construct fixed cutoff extensions agreeing near the selected support.
These deductions do not assert the unconditional response construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives

local instance parameterAssemblyMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- Joint smoothness and finite reserve-graded jets of the actual forward `C`
and signed reverse `-C B⁻¹` on the full amplitude variables. The reverse
coefficient uses the second physical position, preserving the literal reverse
kernel order. All quantitative inputs concern primitive Hessians, carrier
jets, and the central gap; every coefficient derivative is a conclusion.
Source: `app:ch_response:thm:response-literal-transfer` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem parameterCoefficients_graded_on_amplitude
    {n p : ℕ} {S : Euclidean n → Euclidean n → ℝ}
    {ζ : Euclidean p → Euclidean n} {X Y D V : Set (Euclidean n)} {C : Set (Euclidean p)}
    (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
    (hcD : Convex ℝ D) (hζD : ∀ c ∈ C, ζ c ∈ D)
    (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D))
    (hH : ContDiffOn ℝ ∞
      (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) (X ×ˢ D))
    (hζ : ContDiffOn ℝ ∞ ζ C)
    {b M K : ℝ} (hb : 0 < b) (hball : ∀ c ∈ C, Metric.closedBall (ζ c) b ⊆ D)
    (hu : ∀ x ∈ X, ∀ c ∈ C, IsUnit (mixedPhaseOperator S x (ζ c)))
    (hM : ∀ x ∈ X, ∀ c ∈ C, ‖Ring.inverse (mixedPhaseOperator S x (ζ c))‖ ≤ M)
    (hK : 0 ≤ K)
    (hd : ∀ x ∈ X, ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K)
    (hε : ∀ ε ∈ V, ‖ε‖ ≤ averagedMixedSelectorRadius b M K)
    {N R : ℕ} {A H : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hHnonneg : ∀ j, 0 ≤ H j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hSjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) w‖ ≤
        A j * L ^ (j - R))
    (hHjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) w‖ ≤
        H j * L ^ (j - R))
    (hζjet : ∀ j, 1 ≤ j → j ≤ N + 1 → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z) :
    ContDiffOn ℝ ∞ (fun q : ParameterAmplitudePoint n (Euclidean p) ↦
      parameterPhaseCoefficient S ζ q.1.1 q.1.2.2 q.2) ((X ×ˢ Y ×ˢ V) ×ˢ C) ∧
    ContDiffOn ℝ ∞ (signedReverseParameterCoefficient S ζ ∘
      reverseParameterAmplitudeProjection n p) ((Y ×ˢ X ×ˢ V) ×ˢ C) ∧
    (∀ k ≤ N, ∀ q ∈ (X ×ˢ Y ×ˢ V) ×ˢ C,
      ‖iteratedFDeriv ℝ k (fun w : ParameterAmplitudePoint n (Euclidean p) ↦
        parameterPhaseCoefficient S ζ w.1.1 w.1.2.2 w.2) q‖ ≤
          parameterConstant n p H Z k * L ^ (k - R)) ∧
    (∀ k ≤ N, ∀ q ∈ (Y ×ˢ X ×ˢ V) ×ˢ C,
      ‖iteratedFDeriv ℝ k (signedReverseParameterCoefficient S ζ ∘
        reverseParameterAmplitudeProjection n p) q‖ ≤
          signedReverseParameterConstant n p A H Z M k * L ^ (k - R)) := by
  have hc := parameterPhaseCoefficient_contDiffOn hX hD hV hC hcD hζD hbuffer hH hζ
  have hr := signedReverseParameterCoefficient_contDiffOn hX hD hV hC hcD hζD hbuffer hS hζ
    hb hball hu hM hK hd hε hH
  refine ⟨parameterAmplitude_pullback_contDiffOn hc,
    reverseParameterAmplitude_pullback_contDiffOn hr, ?_, ?_⟩
  · intro k hk q hq
    exact (norm_jet_parameterAmplitude_pullback_le hX hV hC hc hq k).trans
      (norm_jet_parameterPhaseCoefficient_le hX hD hV hC hcD hζD hbuffer hH hζ
        hHnonneg hZ hL hHjet hζjet hk ⟨hq.1.1, hq.1.2.2, hq.2⟩)
  · intro k hk q hq
    exact (norm_jet_reverseParameterAmplitude_pullback_le hX hV hC hr hq k).trans
      (norm_jet_signedReverseParameterCoefficient_le hX hD hV hC hcD hζD hbuffer hS hζ
        hb hball hu hM hK hd hε hH hA hHnonneg hZ hL hSjet hHjet hζjet hk
        ⟨hq.1.2.1, hq.1.2.2, hq.2⟩)

end JanetCartan.ResponseTransfer.GradedPrimitives
