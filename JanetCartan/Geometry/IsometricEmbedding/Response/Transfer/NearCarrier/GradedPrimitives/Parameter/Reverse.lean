module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Parameter.Coefficient
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Mixed

/-!
# The literal signed reverse parameter coefficient

The reverse parameter term in `app:ch_response:thm:response-literal-transfer`
uses `-C B⁻¹`, with this sign and composition order. Its reserve-graded jets
follow from the primitive covector and mixed Hessians and the central inverse
gap. No coefficient or inverse derivative bound is an input. These local
deductions are consumed by the global primitive assembly in `GradedPrimitives`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 4

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives

local instance parameterPrimitiveMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- The literal signed reverse parameter coefficient of
`app:ch_response:thm:response-literal-transfer`. The inverse acts first. -/
def signedReverseParameterCoefficient {n p : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean p → Euclidean n)
    (q : ParameterCoefficientSpace n p) : Euclidean n →L[ℝ] Euclidean p →L[ℝ] ℝ :=
  -((parameterPhaseCoefficient S ζ q.1 q.2.1 q.2.2).comp
    (Ring.inverse (averagedMixedOperator S (ζ q.2.2) 1 q.1 q.2.1)))

/-- Evaluation retains the negative sign and the order `C B⁻¹` from
`app:ch_response:thm:response-literal-transfer`. -/
theorem signedReverseParameterCoefficient_apply {n p : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean p → Euclidean n)
    (q : ParameterCoefficientSpace n p) (v : Euclidean n) (w : Euclidean p) :
    signedReverseParameterCoefficient S ζ q v w =
      -(parameterPhaseCoefficient S ζ q.1 q.2.1 q.2.2
        (Ring.inverse (averagedMixedOperator S (ζ q.2.2) 1 q.1 q.2.1) v) w) := rfl

/-- The finite constant for `-C B⁻¹` in
`app:ch_response:eq:direct-envelope-profile`, fixed before scale or frequency. -/
def signedReverseParameterConstant (n p : ℕ) (A H : ℕ → ℝ) (Z M : ℝ) (k : ℕ) : ℝ :=
  bilinearConstant
    (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n) (Euclidean p →L[ℝ] ℝ))
    (parameterConstant n p H Z) (inverseConstant (2 * M) (mixedConstant n A Z)) k

private theorem inverseConstant_nonneg {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j)
    (M : ℝ) (k : ℕ) : 0 ≤ inverseConstant M A k :=
  compositionConstant_nonneg
    (fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
    hA k

/-- Nonnegativity of the reverse constant in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem signedReverseParameterConstant_nonneg (n p : ℕ) {A H : ℕ → ℝ}
    (hA : ∀ j, 0 ≤ A j) (hH : ∀ j, 0 ≤ H j) {Z : ℝ} (hZ : 0 ≤ Z) (M : ℝ) (k : ℕ) :
    0 ≤ signedReverseParameterConstant n p A H Z M k := by
  exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (parameterConstant_nonneg n p hH hZ _))
      (inverseConstant_nonneg (mixedConstant_nonneg n hA hZ) _ _))

section
variable {n p : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {ζ : Euclidean p → Euclidean n} {X D V : Set (Euclidean n)} {C : Set (Euclidean p)}
  (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
  (hcD : Convex ℝ D) (hζD : ∀ c ∈ C, ζ c ∈ D)
  (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
  (hS : ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D))
  (hζ : ContDiffOn ℝ ∞ ζ C)
  {b M K : ℝ} (hb : 0 < b) (hball : ∀ c ∈ C, Metric.closedBall (ζ c) b ⊆ D)
  (hu : ∀ x ∈ X, ∀ c ∈ C, IsUnit (mixedPhaseOperator S x (ζ c)))
  (hM : ∀ x ∈ X, ∀ c ∈ C, ‖Ring.inverse (mixedPhaseOperator S x (ζ c))‖ ≤ M)
  (hK : 0 ≤ K)
  (hd : ∀ x ∈ X, ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S x) η‖ ≤ K)
  (hε : ∀ ε ∈ V, ‖ε‖ ≤ averagedMixedSelectorRadius b M K)

include hX hD hV hC hcD hζD hbuffer hS hζ hb hball hu hM hK hd hε

/-- Smoothness of the actual inverse on the selected joint chart follows
from the primitive central inverse gap and covector Lipschitz bound
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem averagedMixedInverse_parameter_contDiffOn :
    ContDiffOn ℝ ∞ (fun q : ParameterCoefficientSpace n p ↦
      Ring.inverse (averagedMixedOperator S (ζ q.2.2) 1 q.1 q.2.1)) (X ×ˢ V ×ˢ C) := by
  intro q hq
  have hdiff : ∀ η ∈ D, DifferentiableAt ℝ (mixedPhaseOperator S q.1) η := by
    intro η hη
    have hs := (hS.contDiffAt ((hX.prod hD).mem_nhds ⟨hq.1, hη⟩)).comp η
      (contDiffAt_const.prodMk contDiffAt_id)
    exact ((mixedMatrixOperatorEquiv n).contDiff.contDiffAt.comp η hs).differentiableAt (by simp)
  have hgap := averagedMixedOperator_one_inverse_on_selector hcD hb (hball _ hq.2.2)
    (hu _ hq.1 _ hq.2.2) (hM _ hq.1 _ hq.2.2) hK hdiff (hd _ hq.1) (hε _ hq.2.1)
  have hf : ContDiffAt ℝ ∞ (fun w : ParameterCoefficientSpace n p ↦
      averagedMixedOperator S (ζ w.2.2) 1 w.1 w.2.1) q :=
    (mixedMatrixOperatorEquiv n).contDiff.contDiffAt.comp q
      ((averagedMixedMatrix_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hS hζ).contDiffAt
        ((hX.prod (hV.prod hC)).mem_nhds hq))
  exact ((contDiffOn_ringInverse_units.contDiffAt (Units.isOpen.mem_nhds hgap.1)).comp q
    hf).contDiffWithinAt

variable
  (hH : ContDiffOn ℝ ∞
    (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) (X ×ˢ D))

include hH

/-- Smoothness of the literal signed reverse coefficient is deduced from
primitive chart smoothness and the central gap
(`app:ch_response:thm:response-literal-transfer`). -/
theorem signedReverseParameterCoefficient_contDiffOn :
    ContDiffOn ℝ ∞ (signedReverseParameterCoefficient S ζ) (X ×ˢ V ×ˢ C) := by
  exact ((parameterPhaseCoefficient_contDiffOn hX hD hV hC hcD hζD hbuffer hH hζ).clm_comp
    (averagedMixedInverse_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hS hζ
      hb hball hu hM hK hd hε)).neg

/-- Finite joint reserve-graded derivatives of `-C B⁻¹`, with all inverse
jets derived by `norm_jet_averagedMixed_inverse_le` from primitive data.
The Leibniz order is split between `C` and `B⁻¹`, retaining one reserve.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_signedReverseParameterCoefficient_le
    {N k R : ℕ} {A H : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hHnonneg : ∀ j, 0 ≤ H j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hSjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) w‖ ≤
        A j * L ^ (j - R))
    (hHjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j
        (fun z : Euclidean n × Euclidean n ↦ fderiv ℝ (fderiv ℝ (S z.1)) z.2) w‖ ≤
        H j * L ^ (j - R))
    (hζjet : ∀ j, 1 ≤ j → j ≤ N + 1 → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (signedReverseParameterCoefficient S ζ) q‖ ≤
      signedReverseParameterConstant n p A H Z M k * L ^ (k - R) := by
  have hc := parameterPhaseCoefficient_contDiffOn hX hD hV hC hcD hζD hbuffer hH hζ
  have hi := averagedMixedInverse_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hS hζ
    hb hball hu hM hK hd hε
  unfold signedReverseParameterCoefficient
  change ‖iteratedFDeriv ℝ k (-(fun w : ParameterCoefficientSpace n p ↦
    (parameterPhaseCoefficient S ζ w.1 w.2.1 w.2.2).comp
      (Ring.inverse (averagedMixedOperator S (ζ w.2.2) 1 w.1 w.2.1)))) q‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  apply norm_jet_bilinear_le
    (ContinuousLinearMap.compL ℝ (Euclidean n) (Euclidean n) (Euclidean p →L[ℝ] ℝ))
    (hX.prod (hV.prod hC)) (hc.of_le (by simp : (N : ℕ∞ω) ≤ ∞)) (hi.of_le (by simp)) hk hq
    (parameterConstant n p H Z) (inverseConstant (2 * M) (mixedConstant n A Z))
    (parameterConstant_nonneg n p hHnonneg hZ)
    (inverseConstant_nonneg (mixedConstant_nonneg n hA hZ) _) hL R
  · intro j hj
    exact norm_jet_parameterPhaseCoefficient_le hX hD hV hC hcD hζD hbuffer hH hζ
      hHnonneg hZ hL hHjet hζjet (hj.trans hk) hq
  · intro j hj
    exact (norm_jet_averagedMixed_inverse_le hX hD hV hC hcD hζD hbuffer hS hζ
      hA hZ hL hSjet (fun i hi hiN ↦ hζjet i hi (by omega)) (hj.trans hk) hq
      hb (hball _ hq.2.2) (hu _ hq.1 _ hq.2.2) (hM _ hq.1 _ hq.2.2) hK
      (hd _ hq.1) (hε _ hq.2.1)).2.2.1

end
end JanetCartan.ResponseTransfer.GradedPrimitives
