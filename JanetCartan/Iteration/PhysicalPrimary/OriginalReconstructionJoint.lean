module

public import JanetCartan.Iteration.PhysicalPairs.Coefficients
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.Algebraic.LocalCalculus

/-!
# Reserve-preserving joint lifts of the physical reconstruction coefficients

The native physical-history profiles live on the spatial coefficient ball.
Projection onto the physical variable gives the joint profile consumed by
`completedVariationComplex_joint_response_graded`, with the SAME reserve and
constant; no torus-history theorem or parameter-dependent coefficients enter.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology

namespace JanetCartan.PhysicalPrimary.OriginalReconstructionJoint
open CurrentCoefficientProfiles ArbitraryAccuracy.SelectedLocalization

/-- A spatial reconstruction coefficient lifts to the full physical/parameter
jet without spending reserve, increasing its constant, or adding a scale
factor. The two hypotheses are the actual outputs of
`OriginalReconstructionProfiles.{value,derivative,source}_entries`
(`app:ch_response:eq:response-reconstruction-grading`). -/
theorem spatial_reconstruction_joint_profile_with_reserve {n : ℕ}
    {r scale : ℝ} {C : ℕ → ℝ} {f : Euclidean n → ℂ} {reserve : ℕ}
    (hf : ∀ x ∈ closedBall (0 : Euclidean n) r, ContDiffAt ℝ ∞ f x)
    (hp : HasDerivativeProfile (closedBall (0 : Euclidean n) r) f reserve scale C) :
    ContDiffOn ℝ ∞
        (fun q : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦ f q.1)
        (closedBall 0 r ×ˢ univ) ∧
      ∀ m q, q ∈ closedBall 0 r ×ˢ univ →
        ‖iteratedFDeriv ℝ m
          (fun p : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦ f p.1) q‖ ≤
            C m * scale^(m-reserve) := by
  let pr : Euclidean n × (Euclidean 3 × Euclidean (n-1)) →L[ℝ] Euclidean n :=
    ContinuousLinearMap.fst ℝ _ _
  refine ⟨fun q hq ↦ ((hf q.1 hq.1).comp q contDiffAt_fst).contDiffWithinAt, ?_⟩
  intro m q hq
  have hpr : ‖pr‖^m ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg pr)
      (ContinuousLinearMap.norm_fst_le ℝ (Euclidean n) (Euclidean 3 × Euclidean (n-1))) m
  have h := algebraic_norm_iteratedFDeriv_comp_linear_at_le pr (hf q.1 hq.1) m
  apply h.trans
  apply (mul_le_of_le_one_right (norm_nonneg _) hpr).trans
  exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
    (fun x hx ↦ (hf x hx).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) hq.1 le_rfl).trans (hp m)

end JanetCartan.PhysicalPrimary.OriginalReconstructionJoint
