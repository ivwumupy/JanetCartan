module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Segment

/-!
# Primitive budgets for the literal Hessian and mixed-gradient averages

The two actual segment averages in `paper-v2.tex`,
`new:eq:carrier-coefficient`. This produces the positive-order input of the
inverse-adjoint deduction in `exists_transferCoefficient_jet_profile`, for
`paper.tex`, `app:ch_response:eq:direct-envelope-profile`. Critical-map high
jets are derived from the critical equation, never assumed.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint reserve-graded budgets for both literal segment averages, derived
from primitive joint phase jets and the same averaged-Hessian inverse gap.
The critical equation supplies every high critical-map bound, and the
phase loses precisely two orders (`new:eq:carrier-coefficient`). -/
theorem exists_averagedPhase_jet_profile
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (R : ℕ), 1 ≤ R → ∀ (L : ℝ), 1 ≤ L → ∀ (N : ℕ),
      ∀ (f : E → CarrierVariables n → ℝ) (w₀ : E → CarrierVariables n)
        (U : Set E) (D : Set (CarrierVariables n)),
      IsOpen U → IsOpen D → Convex ℝ D →
      ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D) →
      ContDiffOn ℝ ∞ w₀ U → MapsTo w₀ U D →
      (∀ q ∈ U, gradient (f q) (w₀ q) = 0) →
      (∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w)) →
      (∀ q ∈ U, ∀ w ∈ D, ‖Ring.inverse (averagedPhaseHessian f w₀ q w)‖ ≤ B) →
      (∀ j ≤ N + 2, ∀ z ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ j (Function.uncurry f) z‖ ≤ A j * L ^ (j - (R + 2))) →
      ∀ e : E, ‖e‖ ≤ 1 → ∀ k ≤ N, ∀ z ∈ U ×ˢ D,
        ‖iteratedFDeriv ℝ k (Function.uncurry (averagedPhaseHessian f w₀)) z‖ ≤
            C k * L ^ (k - R) ∧
          ‖iteratedFDeriv ℝ k (Function.uncurry (averagedExternalGradient f w₀ e)) z‖ ≤
            C k * L ^ (k - R) := by
  let G : ℕ → ℝ := fun j ↦ if hj : 1 ≤ j then
    (exists_criticalGraph_jet_bound_of_phase_profile (n := n) (E := E)
      (fun i ↦ A (i + 1)) (fun i ↦ hA (i + 1)) hB j hj).choose else 1
  have hG (j : ℕ) : 1 ≤ G j := by
    dsimp [G]
    split_ifs with hj
    · exact (exists_criticalGraph_jet_bound_of_phase_profile (n := n) (E := E)
        (fun i ↦ A (i + 1)) (fun i ↦ hA (i + 1)) hB j hj).choose_spec.1
    · exact le_rfl
  let S := GradedPrimitives.compositionConstant (fun j ↦ A (j + 2)) (fun j ↦ 1 + G j)
  have hS (j : ℕ) : 0 ≤ S j :=
    GradedPrimitives.compositionConstant_nonneg (fun i ↦ hA (i + 2))
      (fun i ↦ by linarith [hG i]) j
  refine ⟨S, hS, ?_⟩
  intro R hR L hL N f w₀ U D hU hD hcD hf hw₀ h₀ hc hu hi hp e he k hk z hz
  have hwjet (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (q : E) (hq : q ∈ U) :
      ‖iteratedFDeriv ℝ j (fun p ↦ (p, w₀ p)) q‖ ≤ G j * L ^ (j - R) := by
    dsimp only [G]
    rw [dite_eq_left hj]
    apply (exists_criticalGraph_jet_bound_of_phase_profile (n := n) (E := E)
      (fun i ↦ A (i + 1)) (fun i ↦ hA (i + 1)) hB j hj).choose_spec.2
      R hR L hL f w₀ U D hU hD hf q hq (h₀ hq) (hw₀.contDiffAt (hU.mem_nhds hq))
      hc (hu q hq _ (h₀ hq)) (hi q hq _ (h₀ hq))
    intro i _ hij
    exact (hp (i + 1) (by omega) (q, w₀ q) ⟨hq, h₀ hq⟩).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (hA _))
  have hHjet (j : ℕ) (hj : j ≤ N) (q : E × CarrierVariables n) (hq : q ∈ U ×ˢ D) :
      ‖iteratedFDeriv ℝ j
        (fun p : E × CarrierVariables n ↦ fderiv ℝ (gradient (f p.1)) p.2) q‖ ≤
        A (j + 2) * L ^ (j - R) := by
    apply (norm_jet_jointPhaseHessian_le_phase hU hD hf j hq).trans
    simpa only [Nat.add_sub_add_right] using hp (j + 2) (by omega) q hq
  have hEjet (j : ℕ) (hj : j ≤ N) (q : E × CarrierVariables n) (hq : q ∈ U ×ˢ D) :
      ‖iteratedFDeriv ℝ j
        (fun p : E × CarrierVariables n ↦ gradient (externalDerivative f e p.1) p.2) q‖ ≤
        A (j + 2) * L ^ (j - R) := by
    apply (norm_jet_jointExternalGradient_le_phase hU hD hf e j hq).trans
    apply (mul_le_of_le_one_left (norm_nonneg _) he).trans
    simpa only [Nat.add_sub_add_right] using hp (j + 2) (by omega) q hq
  have hHbound (j : ℕ) (hj : j ≤ N) (q : E × CarrierVariables n) (hq : q ∈ U ×ˢ D) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (averagedPhaseHessian f w₀)) q‖ ≤
        S j * L ^ (j - R) :=
    norm_jet_criticalSegmentAverage_le hU hD hcD (contDiffOn_jointPhaseHessian hU hD hf)
      hw₀ h₀ hR (fun j ↦ A (j + 2)) G (fun j ↦ hA (j + 2))
      (fun j ↦ zero_le_one.trans (hG j)) hL hHjet hwjet hj hq
  have hEbound (j : ℕ) (hj : j ≤ N) (q : E × CarrierVariables n) (hq : q ∈ U ×ˢ D) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (averagedExternalGradient f w₀ e)) q‖ ≤
        S j * L ^ (j - R) :=
    norm_jet_criticalSegmentAverage_le hU hD hcD (contDiffOn_jointExternalGradient hU hD hf e)
      hw₀ h₀ hR (fun j ↦ A (j + 2)) G (fun j ↦ hA (j + 2))
      (fun j ↦ zero_le_one.trans (hG j)) hL hEjet hwjet hj hq
  exact ⟨hHbound k hk z hz, hEbound k hk z hz⟩

end JanetCartan.ResponseTransfer.DirectEvolution
