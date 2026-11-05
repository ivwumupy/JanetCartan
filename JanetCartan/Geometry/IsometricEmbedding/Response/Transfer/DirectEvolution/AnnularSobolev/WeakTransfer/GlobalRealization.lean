module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Supported
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.SourceTests

/-!
# Global supported kernel identities for the same physical annular operators

The primitive compact geometry is used only on the original output support.
Outside that support the actual branch integrands vanish. These identities
instantiate the normalized-kernel premises of the tempered and parameter
weak-transfer theorems for the published forward and reversed operators.
Source: `new:eq:carrier-ibp` and `app:ch_response:lem:energy-carrier-jets`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open FourierIntegral FourierIntegral.FullLowBounds CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual forward branch has its literal normalized kernel globally.
Only the original supported geometry and the physical test realization enter;
output regularity and derivative transfer are conclusions downstream.
Source: `new:eq:carrier-ibp`. -/
theorem annularBranchOperator_ae_jointIntegral_of_output_support
    (b : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (elapsed : ℝ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    {U : Set (E × P)} {D K : Set (CarrierVariables (d + 1))}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (elapsedCarrierPhase Ψ elapsed φ)) (U ×ˢ D))
    {α : (E × P) → CarrierVariables (d + 1) → Mat} {a : E × P → Fin r → ℂ}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D,
      IsUnit (averagedPhaseHessian (elapsedCarrierPhase Ψ elapsed φ) w₀ q w))
    {Ksource S : Set E} (hKsource : IsCompact Ksource) (hS : IsOpen S) (hKS : Ksource ⊆ S)
    (has : ∀ q, q.1 ∉ Ksource → a q = 0)
    (es : List (E × P)) (t : JointTransferTerm (d + 1) P Mat ι)
    (ht : t ∈ jointTransferTerms b es)
    {X : Set E} (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    (c : P) (hXU : ∀ x ∈ X, (x, c) ∈ U)
    (hcφ : Continuous (fun x => φ x c)) (hφ : ContDiffOn ℝ ∞ (fun x => φ x c) S)
    (hreal : ∀ u : graphTestSpace (d + 1) r,
      fullGraphOperator (elapsedPhase Ψ elapsed) (modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c))
        (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (elapsedPhase Ψ elapsed) (modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c)) u)
    (hΘ : ∀ x z θ, modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c) x z (lam • θ) ≠ 0 →
        elapsedPhase Ψ elapsed x (lam • θ) = lam * elapsedPhase Ψ elapsed x θ)
 :
    annularBranchOperator b Ψ elapsed lam p φ w₀ α t c hcφ
      (graphTestToLp (originalDatumTest a ha hKsource has t.datumWord c)) =ᵐ[volume]
        fun x => WithLp.toLp 2
          (normalizedBranchIntegral b (elapsedCarrierPhase Ψ elapsed φ) w₀ α a t lam p (x, c)) := by
  have h := annularBranchOperator_ae_jointIntegral (W := univ)
    b Ψ elapsed hlam p φ w₀ α a t c hcφ hS hφ
    (originalDatumTest a ha hKsource has t.datumWord c)
    ((originalDatumTest_support a ha hKsource has t.datumWord c).trans hKS)
    (originalDatumTest_apply a ha hKsource has t.datumWord c) hreal
    (fun x _ => hΘ x)
    (fun x _ => integrable_jointBranch_of_output_support b hU hD hcD hK hKD hf hα ha hs hw₀ h₀
      hinv lam es t ht houtput c hXU x) MeasurableSet.univ
  simpa only [Measure.restrict_univ] using h

/-- The actual reversed branch has its literal normalized kernel globally.
Only the original supported geometry and the physical test realization enter;
output regularity and derivative transfer are conclusions downstream.
Source: `new:eq:carrier-ibp`. -/
theorem reverseAnnularBranchOperator_ae_jointIntegral_of_output_support
    (b : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (elapsed : ℝ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    {U : Set (E × P)} {D K : Set (CarrierVariables (d + 1))}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ)) (U ×ˢ D))
    {α : (E × P) → CarrierVariables (d + 1) → Mat} {a : E × P → Fin r → ℂ}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry α) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support (α q) ⊆ K)
    (hw₀ : ContDiffOn ℝ ∞ w₀ U)
    (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D,
      IsUnit (averagedPhaseHessian (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ q w))
    {Ksource S : Set E} (hKsource : IsCompact Ksource) (hS : IsOpen S) (hKS : Ksource ⊆ S)
    (has : ∀ q, q.1 ∉ Ksource → a q = 0)
    (es : List (E × P)) (t : JointTransferTerm (d + 1) P Mat ι)
    (ht : t ∈ jointTransferTerms b es)
    {X : Set E} (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    (c : P) (hXU : ∀ x ∈ X, (x, c) ∈ U)
    (hcφ : Continuous (fun x => φ x c)) (hφ : ContDiffOn ℝ ∞ (fun x => φ x c) S)
    (hreal : ∀ u : graphTestSpace (d + 1) r,
      (fullGraphOperator (elapsedPhase Ψ elapsed) (fun x z ξ =>
        (modifiedAmplitude lam p (normalizedTermAmplitude b
          (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c) z x ξ).conjTranspose)).adjoint
        (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
      (reverseGraphOperator (elapsedPhase Ψ elapsed) (fun y z ξ =>
        modifiedAmplitude lam p (normalizedTermAmplitude b
          (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c) z y ξ)
        (fun y => (u.val y).ofLp) x))
    (hΘ : ∀ x z θ, modifiedAmplitude lam p
        (normalizedTermAmplitude b (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c)
          x z (lam • θ) ≠ 0 →
        elapsedPhase Ψ elapsed z (lam • θ) = lam * elapsedPhase Ψ elapsed z θ)
 :
    reverseAnnularBranchOperator b Ψ elapsed lam p φ w₀ α t c hcφ
      (graphTestToLp (originalDatumTest a ha hKsource has t.datumWord c)) =ᵐ[volume]
        fun x => WithLp.toLp 2
          (normalizedBranchIntegral b (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α a t lam p (x, c)) := by
  have h := reverseAnnularBranchOperator_ae_jointIntegral (W := univ)
    b Ψ elapsed hlam p φ w₀ α a t c hcφ hS hφ
    (originalDatumTest a ha hKsource has t.datumWord c)
    ((originalDatumTest_support a ha hKsource has t.datumWord c).trans hKS)
    (originalDatumTest_apply a ha hKsource has t.datumWord c) hreal
    (fun x _ => hΘ x)
    (fun x _ => integrable_jointBranch_of_output_support b hU hD hcD hK hKD hf hα ha hs hw₀ h₀
      hinv lam es t ht houtput c hXU x) MeasurableSet.univ
  simpa only [Measure.restrict_univ] using h

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
