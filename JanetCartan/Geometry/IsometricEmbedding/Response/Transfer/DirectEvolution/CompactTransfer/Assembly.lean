module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.IntegralSum
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CoefficientJets.Smooth

/-!
# Compact carrier transfer from primitive smooth critical geometry

The complete finite identity of `paper-v2.tex`, `new:eq:carrier-ibp`, and the
shared coefficient/input budget needed by `app:ch_response:eq:direct-envelope-profile`.
The published coefficient-smoothness producer is instantiated here. Neither a
transfer identity nor a bound on the output is an input. Strong limits, the
quantitative coefficient profile and operator estimates remain with the consumer.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
open Pseudodifferential

variable {n : ℕ} {P M V F ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [Fintype ι]

/-- Finite compact derivative transfer from primitive geometry, with a finite
sum of actual oscillatory integrals and the exact shared order `k+j=q`.
The original input appears only through its actual ordered source/parameter
derivatives. The coefficient smoothness premise is discharged by
`contDiffOn_transferCoefficient`; all integral hypotheses follow from the same
compact support. This applies to `elapsedCarrierPhase Ψ r φ` and to
`adjointCarrierPhase (elapsedPhase Ψ r) φ` with their respective critical geometry.
Source: `new:eq:carrier-ibp` and the derivative count immediately following it. -/
theorem orderedTransferAction_integral_expansion
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (B : M →L[ℝ] V →L[ℝ] F)
    {f : (Euclidean n × P) → CarrierVariables n → ℝ}
    {w₀ : (Euclidean n × P) → CarrierVariables n}
    {U : Set (Euclidean n × P)} {D K : Set (CarrierVariables n)}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ D))
    {α : (Euclidean n × P) → CarrierVariables n → M} {a : Euclidean n × P → V}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (hcritical : ∀ q ∈ U, gradient (f q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, f q (w₀ q) = 0)
    (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D, IsUnit (averagedPhaseHessian f w₀ q w))
    (ρ : ℝ) (es : List (Euclidean n × P)) {q : Euclidean n × P} (hq : q ∈ U) :
    (orderedTransferAction (fun e h p => fderiv ℝ h p e) es
        (fun p => ∫ w, oscillation f ρ p w • B (α p w) (sourceDatum a p w)) q =
      ((jointTransferTerms b es).map fun t =>
        ∫ w, oscillation f ρ q w • jointTransferTermValue b B f w₀ α a t q w).sum) ∧
    (∀ t : JointTransferTerm n P M ι, t ∈ jointTransferTerms b es →
      t.amplitude.derivativeCost + t.datumWord.length = es.length) := by
  have hA := contDiffOn_transferCoefficient hU hD hcD hf hw₀ h₀ hinv
  constructor
  · rw [orderedTransferAction_integral_eq_jointTransferTerms b B hU hD hcD hK hKD hf hα ha hs
      (fun p hp => (hw₀.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
      hcritical hvalue (fun p hp => h₀ hp) hinv hA ρ es hq]
    exact integral_oscillation_jointTransferTerms_eq_sum b B hU hD hK hKD hf hα ha hs hA ρ es hq
  · exact jointTransferTerms_order_budget b es

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
