module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Averages

/-!
# Uniform finite-jet budgets for the literal transfer coefficient

The coefficient estimate `paper-v2.tex`, `new:eq:carrier-coefficient`, used
for the original two-scale estimate `paper.tex`,
`app:ch_response:eq:direct-envelope-profile`.

Only primitive joint phase jets, smooth critical matching, containment in
the same open convex product and the literal averaged-Hessian inverse gap
are inputs. The critical jets, segment jets and inverse jets are derived.
The coefficient reserve is independent of the input reserve and scale:
there is no input scale or frequency in this deduction. The compatible
primary-phase construction and small-time two-time Hamilton geometry still
have to instantiate the primitive hypotheses in the parent construction.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.DirectEvolution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Uniform reserve-graded jets of the actual inverse-adjoint coefficient
in `new:eq:carrier-coefficient`. Exactly two primitive phase orders are
spent. The constants precede the reserve, scale, requested finite order,
phase family and unit external direction. All critical-map high bounds
are derived from its equation; the zero-critical-value hypothesis used in
the phase trade is not needed for this estimate. -/
theorem exists_transferCoefficient_jet_profile
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
        ‖iteratedFDeriv ℝ k (Function.uncurry (transferCoefficient f w₀ e)) z‖ ≤
          C k * L ^ (k - R) := by
  obtain ⟨S, hS, haverage⟩ := exists_averagedPhase_jet_profile (n := n) (E := E) A hA hB
  let I := GradedPrimitives.inverseConstant B S
  have hI (j : ℕ) : 0 ≤ I j :=
    GradedPrimitives.compositionConstant_nonneg
      (fun i ↦ mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (zero_le_one.trans (le_max_left 1 B)) _)) hS j
  let T : (CarrierVariables n →L[ℝ] CarrierVariables n) →L[ℝ]
      (CarrierVariables n →L[ℝ] CarrierVariables n) :=
    (ContinuousLinearMap.adjoint :
      (CarrierVariables n →L[ℝ] CarrierVariables n) ≃ₗᵢ[ℝ]
        (CarrierVariables n →L[ℝ] CarrierVariables n)).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨GradedPrimitives.bilinearConstant T I S, ?_, ?_⟩
  · intro j
    exact mul_nonneg (norm_nonneg T) (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hI i)) (hS (j - i)))
  intro R hR L hL N f w₀ U D hU hD hcD hf hw₀ h₀ hc hu hi hp e he k hk z hz
  have hH := contDiffOn_averagedPhaseHessian hU hD hcD hf hw₀ h₀
  have hE := contDiffOn_averagedExternalGradient hU hD hcD hf hw₀ h₀ e
  have hHbound (j : ℕ) (hj : j ≤ N) (q : E × CarrierVariables n) (hq : q ∈ U ×ˢ D) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (averagedPhaseHessian f w₀)) q‖ ≤
        S j * L ^ (j - R) :=
    (haverage R hR L hL N f w₀ U D hU hD hcD hf hw₀ h₀ hc hu hi hp e he j hj q hq).1
  have hEbound (j : ℕ) (hj : j ≤ N) (q : E × CarrierVariables n) (hq : q ∈ U ×ˢ D) :
      ‖iteratedFDeriv ℝ j (Function.uncurry (averagedExternalGradient f w₀ e)) q‖ ≤
        S j * L ^ (j - R) :=
    (haverage R hR L hL N f w₀ U D hU hD hcD hf hw₀ h₀ hc hu hi hp e he j hj q hq).2
  have hInv : ContDiffOn ℝ ∞
      (fun q : E × CarrierVariables n ↦ Ring.inverse (averagedPhaseHessian f w₀ q.1 q.2))
      (U ×ˢ D) := by
    intro q hq
    exact (((contDiffOn_ringInverse_units (N := ∞)).contDiffAt
      (Units.isOpen.mem_nhds (hu q.1 hq.1 q.2 hq.2))).comp q
        (hH.contDiffAt ((hU.prod hD).mem_nhds hq))).contDiffWithinAt
  exact GradedPrimitives.norm_jet_bilinear_le T (hU.prod hD)
    (hInv.of_le (by simp : (N : ℕ∞ω) ≤ ∞)) (hE.of_le (by simp)) hk hz I S hI hS hL R
    (fun j hj ↦ GradedPrimitives.norm_jet_inverse_le
      ((hH.contDiffAt ((hU.prod hD).mem_nhds hz)).of_le (by simp : (N : ℕ∞ω) ≤ ∞))
      (hj.trans hk) (hu z.1 hz.1 z.2 hz.2) (hi z.1 hz.1 z.2 hz.2) S hS hL R
      (fun i _ hij ↦ hHbound i (hij.trans (hj.trans hk)) z hz))
    (fun j hj ↦ hEbound j (hj.trans hk) z hz)

end JanetCartan.ResponseTransfer.DirectEvolution
