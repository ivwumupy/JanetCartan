module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Segment
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed

/-!
# Reserve-graded averaged mixed matrices and their actual inverses

The `B` and `B⁻¹` primitives in `app:ch_response:eq:direct-envelope-profile`
are differentiated jointly in physical position, normalized displacement and
carrier parameter. The inverse estimate is deduced from primitive mixed
Hessian jets and the central inverse gap via the proved selector argument.
It does not use the older `L^j` inverse estimate. Matrix norms are Frobenius
norms, with explicit fixed conversions to and from the Euclidean operator.

The response geometry producer supplies the smooth phase on the buffered
convex chart, its finite reserve-graded mixed Hessian jets, central gap and
fixed covector Lipschitz bound. The carrier is fixed with bounded finite jets.
These local estimates are to be extended with fixed cutoffs before applying
the global primitive interface in `SymbolBudget` and `BranchRealization`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives

local instance mixedPrimitiveMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- The fixed operator conversion of the segment constant in
`app:ch_response:eq:direct-envelope-profile`. -/
def mixedConstant (n : ℕ) (A : ℕ → ℝ) (Z : ℝ) (k : ℕ) : ℝ :=
  ‖(mixedMatrixOperatorEquiv n).toContinuousLinearMap‖ * segmentConstant A Z k

/-- Nonnegativity of the primitive operator constant. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem mixedConstant_nonneg (n : ℕ) {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j)
    {Z : ℝ} (hZ : 0 ≤ Z) (k : ℕ) : 0 ≤ mixedConstant n A Z k :=
  mul_nonneg (norm_nonneg (mixedMatrixOperatorEquiv n).toContinuousLinearMap)
    (segmentConstant_nonneg hA hZ k)

/-- Identification with the literal averaged mixed matrix; no rescaling or
adjoint substitution occurs (`app:ch_response:eq:direct-envelope-profile`). -/
theorem averagedMixedMatrix_eq_normalizedSegmentAverage {n p : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean p → Euclidean n) :
    (fun q : ParameterCoefficientSpace n p ↦ averagedMixedMatrix S (ζ q.2.2) 1 q.1 q.2.1) =
      normalizedSegmentAverage (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) ζ := by
  funext q
  simp only [normalizedSegmentAverage, averagedMixedMatrix, one_smul, Function.uncurry_apply_pair]

section
variable {n p : ℕ} {S : Euclidean n → Euclidean n → ℝ}
  {ζ : Euclidean p → Euclidean n} {X D V : Set (Euclidean n)} {C : Set (Euclidean p)}
  (hX : IsOpen X) (hD : IsOpen D) (hV : IsOpen V) (hC : IsOpen C)
  (hcD : Convex ℝ D) (hζD : ∀ c ∈ C, ζ c ∈ D)
  (hbuffer : ∀ c ∈ C, ∀ ε ∈ V, ζ c + ε ∈ D)
  (hS : ContDiffOn ℝ ∞ (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) (X ×ˢ D))
  (hζ : ContDiffOn ℝ ∞ ζ C)

include hX hD hV hC hcD hζD hbuffer hS hζ

/-- Joint smoothness of the literal normalized `B`, including carrier
parameters (`app:ch_response:eq:direct-envelope-profile`). -/
theorem averagedMixedMatrix_parameter_contDiffOn :
    ContDiffOn ℝ ∞ (fun q : ParameterCoefficientSpace n p ↦
      averagedMixedMatrix S (ζ q.2.2) 1 q.1 q.2.1) (X ×ˢ V ×ˢ C) := by
  rw [averagedMixedMatrix_eq_normalizedSegmentAverage]
  exact normalizedSegmentAverage_contDiffOn hX hD hV hC hcD hζD hbuffer hS hζ

/-- Reserve-graded finite joint jets of the actual averaged mixed matrix.
Only primitive phase and fixed carrier jets occur as quantitative inputs
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem norm_jet_averagedMixedMatrix_le {N k R : ℕ} {A : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hSjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) w‖ ≤
        A j * L ^ (j - R))
    (hζjet : ∀ j, 1 ≤ j → j ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      averagedMixedMatrix S (ζ w.2.2) 1 w.1 w.2.1) q‖ ≤
        segmentConstant A Z k * L ^ (k - R) := by
  rw [averagedMixedMatrix_eq_normalizedSegmentAverage]
  exact norm_jet_normalizedSegmentAverage_le hX hD hV hC hcD hζD hbuffer hS hζ
      hA hZ hL hSjet hζjet hk hq

/-- Conversion of the joint `B` profile to the Euclidean operator norm,
for inversion in `app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_averagedMixedOperator_le {N k R : ℕ} {A : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hSjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) w‖ ≤
        A j * L ^ (j - R))
    (hζjet : ∀ j, 1 ≤ j → j ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C) :
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      averagedMixedOperator S (ζ w.2.2) 1 w.1 w.2.1) q‖ ≤
        mixedConstant n A Z k * L ^ (k - R) := by
  apply ((mixedMatrixOperatorEquiv n).toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    ((averagedMixedMatrix_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hS hζ).contDiffAt
      ((hX.prod (hV.prod hC)).mem_nhds hq)) (by simp)).trans
  rw [mixedConstant, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (norm_jet_averagedMixedMatrix_le hX hD hV hC hcD hζD hbuffer hS hζ
      hA hZ hL hSjet hζjet hk hq) (norm_nonneg _)

/-- Actual inverse coefficient bounds from the central primitive inverse gap
and the proved selector radius. No derivative of the inverse is an input.
The constant is fixed before `L` and carrier frequency. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_averagedMixed_inverse_le {N k R : ℕ} {A : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hSjet : ∀ j ≤ N, ∀ w ∈ X ×ˢ D,
      ‖iteratedFDeriv ℝ j (Function.uncurry (FourierIntegral.mixedPhaseMatrix S)) w‖ ≤
        A j * L ^ (j - R))
    (hζjet : ∀ j, 1 ≤ j → j ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z)
    (hk : k ≤ N) {q : ParameterCoefficientSpace n p} (hq : q ∈ X ×ˢ V ×ˢ C)
    {b M K : ℝ} (hb : 0 < b) (hball : Metric.closedBall (ζ q.2.2) b ⊆ D)
    (hu : IsUnit (mixedPhaseOperator S q.1 (ζ q.2.2)))
    (hM : ‖Ring.inverse (mixedPhaseOperator S q.1 (ζ q.2.2))‖ ≤ M) (hK : 0 ≤ K)
    (hd : ∀ η ∈ D, ‖fderiv ℝ (mixedPhaseOperator S q.1) η‖ ≤ K)
    (hε : ‖q.2.1‖ ≤ averagedMixedSelectorRadius b M K) :
    IsUnit (averagedMixedOperator S (ζ q.2.2) 1 q.1 q.2.1) ∧
    ‖Ring.inverse (averagedMixedOperator S (ζ q.2.2) 1 q.1 q.2.1)‖ ≤ 2 * M ∧
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      Ring.inverse (averagedMixedOperator S (ζ w.2.2) 1 w.1 w.2.1)) q‖ ≤
        inverseConstant (2 * M) (mixedConstant n A Z) k * L ^ (k - R) ∧
    ‖iteratedFDeriv ℝ k (fun w : ParameterCoefficientSpace n p ↦
      (averagedMixedMatrix S (ζ w.2.2) 1 w.1 w.2.1)⁻¹) q‖ ≤
        (‖(mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap‖ *
          inverseConstant (2 * M) (mixedConstant n A Z) k) * L ^ (k - R) := by
  have hdiff : ∀ η ∈ D, DifferentiableAt ℝ (mixedPhaseOperator S q.1) η := by
    intro η hη
    have hs := (hS.contDiffAt ((hX.prod hD).mem_nhds ⟨hq.1, hη⟩)).comp η
      (contDiffAt_const.prodMk contDiffAt_id)
    exact ((mixedMatrixOperatorEquiv n).contDiff.contDiffAt.comp η hs).differentiableAt
      (by simp)
  have hgap := averagedMixedOperator_one_inverse_on_selector hcD hb hball hu hM hK hdiff hd hε
  let f := fun w : ParameterCoefficientSpace n p ↦
    averagedMixedOperator S (ζ w.2.2) 1 w.1 w.2.1
  have hf : ContDiffAt ℝ ∞ f q :=
    (mixedMatrixOperatorEquiv n).contDiff.contDiffAt.comp q
      ((averagedMixedMatrix_parameter_contDiffOn hX hD hV hC hcD hζD hbuffer hS hζ).contDiffAt
        ((hX.prod (hV.prod hC)).mem_nhds hq))
  have hi := norm_jet_inverse_le (hf.of_le (by simp : (N : ℕ∞ω) ≤ ∞)) hk hgap.1 hgap.2
    (mixedConstant n A Z) (mixedConstant_nonneg n hA hZ) hL R
    (fun j _ hj ↦ norm_jet_averagedMixedOperator_le hX hD hV hC hcD hζD hbuffer hS hζ
      hA hZ hL hSjet hζjet (hj.trans hk) hq)
  refine ⟨hgap.1, hgap.2, hi, ?_⟩
  have hi₀ : ContDiffAt ℝ ∞
      (Ring.inverse : (Euclidean n →L[ℝ] Euclidean n) → (Euclidean n →L[ℝ] Euclidean n))
      (f q) := contDiffOn_ringInverse_units.contDiffAt (Units.isOpen.mem_nhds hgap.1)
  have his : ContDiffAt ℝ ∞ (fun w ↦ Ring.inverse (f w)) q := hi₀.comp q hf
  have he : (fun w : ParameterCoefficientSpace n p ↦
      (averagedMixedMatrix S (ζ w.2.2) 1 w.1 w.2.1)⁻¹) =
      (mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap ∘ (fun w ↦ Ring.inverse (f w)) := by
    funext w
    exact (mixedMatrixOperatorEquiv_symm_inverse _).symm
  rw [he, mul_assoc]
  exact ((mixedMatrixOperatorEquiv n).symm.toContinuousLinearMap.norm_iteratedFDeriv_comp_left
    his (by simp)).trans (mul_le_mul_of_nonneg_left hi (norm_nonneg _))

end
end JanetCartan.ResponseTransfer.GradedPrimitives
