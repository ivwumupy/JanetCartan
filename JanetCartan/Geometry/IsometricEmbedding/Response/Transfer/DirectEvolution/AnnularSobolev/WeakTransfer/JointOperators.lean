module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.GlobalRealization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.JointExpansion

/-!
# Actual joint weak derivatives of the published annular operators

The complete compact expansion is realized by the SAME forward or reversed
annular branch operators. Parameter differentiation is in the original L²
norm, and spatial differentiation is in tempered distributions. Every branch
acts on its recorded derivative of the ORIGINAL datum. The only independent
operator inputs are physical low-calculus test realizations.
Source: `app:ch_response:lem:energy-carrier-jets`, `new:eq:carrier-ibp`, and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory LineDeriv
open scoped ContDiff Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open Pseudodifferential FourierIntegral FourierIntegral.FullLowBounds CompactTransfer BranchAmplitudes ModifiedLow
open RegularSector.Characteristic.EvolutionIntegral
variable {d r : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [Fintype ι]
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The actual forward annular family has the exact joint expansion.
Its physical graph, elapsed time and frequency are fixed while the carrier
parameter varies. The low-calculus realization is the only operator premise;
all output regularity and derivative identities are proved. Source:
`app:ch_response:lem:energy-carrier-jets` and `new:eq:carrier-ibp`. -/
theorem annularBranchFamily_joint_derivative_expansion
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
    (hcritical : ∀ q ∈ U, gradient (elapsedCarrierPhase Ψ elapsed φ q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, elapsedCarrierPhase Ψ elapsed φ q (w₀ q) = 0)
    (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D,
      IsUnit (averagedPhaseHessian (elapsedCarrierPhase Ψ elapsed φ) w₀ q w))
    {Ksource S : Set E} (hKsource : IsCompact Ksource) (hS : IsOpen S) (hKS : Ksource ⊆ S)
    (has : ∀ q, q.1 ∉ Ksource → a q = 0)
    (ps : List P) (is : List (Fin (d + 1)))
    {X : Set E} (hX : IsCompact X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    {C : Set P} (hC : IsOpen C) (hXU : X ×ˢ C ⊆ U)
    (hcφ : ∀ c, Continuous (fun x => φ x c))
    (hφ : ∀ c ∈ C, ContDiffOn ℝ ∞ (fun x => φ x c) S)
    (hreal : ∀ c ∈ C, ∀ es : List (E × P), es.length ≤ is.length + ps.length →
      ∀ t ∈ jointTransferTerms b es,
      ∀ u : graphTestSpace (d + 1) r,
      fullGraphOperator (elapsedPhase Ψ elapsed) (modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c))
        (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (elapsedPhase Ψ elapsed) (modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c)) u)
    (hΘ : ∀ c ∈ C, ∀ es : List (E × P), es.length ≤ is.length + ps.length →
      ∀ t ∈ jointTransferTerms b es, ∀ x z θ, modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c) x z (lam • θ) ≠ 0 →
        elapsedPhase Ψ elapsed x (lam • θ) = lam * elapsedPhase Ψ elapsed x θ)
    (c : P) (hc : c ∈ C) :
    let T := fun c t => annularBranchOperator b Ψ elapsed lam p φ w₀ α t c (hcφ c)
      (graphTestToLp (originalDatumTest a ha hKsource has t.datumWord c))
    orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
      ((orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
        (fun c => T c initialJointTransferTerm) c : H) : 𝓢'(E, EuclideanSpace ℂ (Fin r))) =
      ((jointTransferTerms b ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++
        ps.map (fun v => ((0 : E), v)))).map
          fun t => (T c t : 𝓢'(E, EuclideanSpace ℂ (Fin r)))).sum := by
  let T := fun c t => annularBranchOperator b Ψ elapsed lam p φ w₀ α t c (hcφ c)
    (graphTestToLp (originalDatumTest a ha hKsource has t.datumWord c))
  have hkernel (c : P) (hc : c ∈ C) (es : List (E × P))
      (hes : es.length ≤ is.length + ps.length)
      (t : JointTransferTerm (d + 1) P Mat ι) (ht : t ∈ jointTransferTerms b es) :
      T c t =ᵐ[volume] fun x => WithLp.toLp 2
        (normalizedBranchIntegral b (elapsedCarrierPhase Ψ elapsed φ) w₀ α a t lam p (x, c)) :=
    annularBranchOperator_ae_jointIntegral_of_output_support b Ψ elapsed hlam p φ w₀
      hU hD hcD hK hKD hf hα ha hs hw₀ h₀ hinv hKsource hS hKS has es t ht
      houtput c (fun x hx => hXU ⟨hx, hc⟩) (hcφ c) (hφ c hc)
      (hreal c hc es hes t ht) (hΘ c hc es hes t ht)
  exact realizedBranchFamily_joint_derivative_expansion b hU hD hcD hK hKD hf hα ha hs hw₀
    hcritical hvalue h₀ hinv lam p ps is hX houtput hC hXU hc
    (fun c => T c initialJointTransferTerm)
    (fun c hc => hkernel c hc [] (Nat.zero_le _) initialJointTransferTerm
      (by simp [jointTransferTerms, orderedTransferAction])) (T c)
    (fun js hjs t ht => hkernel c hc _ (by simpa using Nat.add_le_add_right hjs ps.length) t ht)

/-- The actual reversed annular family has the exact joint expansion.
Its physical graph, elapsed time and frequency are fixed while the carrier
parameter varies. The low-calculus realization is the only operator premise;
all output regularity and derivative identities are proved. Source:
`app:ch_response:lem:energy-carrier-jets` and `new:eq:carrier-ibp`. -/
theorem reverseAnnularBranchFamily_joint_derivative_expansion
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
    (hcritical : ∀ q ∈ U, gradient (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ q) (w₀ q) = 0)
    (hvalue : ∀ q ∈ U, adjointCarrierPhase (elapsedPhase Ψ elapsed) φ q (w₀ q) = 0)
    (h₀ : MapsTo w₀ U D)
    (hinv : ∀ q ∈ U, ∀ w ∈ D,
      IsUnit (averagedPhaseHessian (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ q w))
    {Ksource S : Set E} (hKsource : IsCompact Ksource) (hS : IsOpen S) (hKS : Ksource ⊆ S)
    (has : ∀ q, q.1 ∉ Ksource → a q = 0)
    (ps : List P) (is : List (Fin (d + 1)))
    {X : Set E} (hX : IsCompact X)
    (houtput : ∀ q ∈ tsupport (Function.uncurry α), q.1.1 ∈ X)
    {C : Set P} (hC : IsOpen C) (hXU : X ×ˢ C ⊆ U)
    (hcφ : ∀ c, Continuous (fun x => φ x c))
    (hφ : ∀ c ∈ C, ContDiffOn ℝ ∞ (fun x => φ x c) S)
    (hreal : ∀ c ∈ C, ∀ es : List (E × P), es.length ≤ is.length + ps.length →
      ∀ t ∈ jointTransferTerms b es,
      ∀ u : graphTestSpace (d + 1) r,
      (fullGraphOperator (elapsedPhase Ψ elapsed) (fun x z ξ =>
        (modifiedAmplitude lam p (normalizedTermAmplitude b
          (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c) z x ξ).conjTranspose)).adjoint
        (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
      (reverseGraphOperator (elapsedPhase Ψ elapsed) (fun y z ξ =>
        modifiedAmplitude lam p (normalizedTermAmplitude b
          (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c) z y ξ)
        (fun y => (u.val y).ofLp) x))
    (hΘ : ∀ c ∈ C, ∀ es : List (E × P), es.length ≤ is.length + ps.length →
      ∀ t ∈ jointTransferTerms b es, ∀ x z θ, modifiedAmplitude lam p
        (normalizedTermAmplitude b (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c)
          x z (lam • θ) ≠ 0 →
        elapsedPhase Ψ elapsed z (lam • θ) = lam * elapsedPhase Ψ elapsed z θ)
    (c : P) (hc : c ∈ C) :
    let T := fun c t => reverseAnnularBranchOperator b Ψ elapsed lam p φ w₀ α t c (hcφ c)
      (graphTestToLp (originalDatumTest a ha hKsource has t.datumWord c))
    orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
      ((orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
        (fun c => T c initialJointTransferTerm) c : H) : 𝓢'(E, EuclideanSpace ℂ (Fin r))) =
      ((jointTransferTerms b ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++
        ps.map (fun v => ((0 : E), v)))).map
          fun t => (T c t : 𝓢'(E, EuclideanSpace ℂ (Fin r)))).sum := by
  let T := fun c t => reverseAnnularBranchOperator b Ψ elapsed lam p φ w₀ α t c (hcφ c)
    (graphTestToLp (originalDatumTest a ha hKsource has t.datumWord c))
  have hkernel (c : P) (hc : c ∈ C) (es : List (E × P))
      (hes : es.length ≤ is.length + ps.length)
      (t : JointTransferTerm (d + 1) P Mat ι) (ht : t ∈ jointTransferTerms b es) :
      T c t =ᵐ[volume] fun x => WithLp.toLp 2
        (normalizedBranchIntegral b (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α a t lam p (x, c)) :=
    reverseAnnularBranchOperator_ae_jointIntegral_of_output_support b Ψ elapsed hlam p φ w₀
      hU hD hcD hK hKD hf hα ha hs hw₀ h₀ hinv hKsource hS hKS has es t ht
      houtput c (fun x hx => hXU ⟨hx, hc⟩) (hcφ c) (hφ c hc)
      (hreal c hc es hes t ht) (hΘ c hc es hes t ht)
  exact realizedBranchFamily_joint_derivative_expansion b hU hD hcD hK hKD hf hα ha hs hw₀
    hcritical hvalue h₀ hinv lam p ps is hX houtput hC hXU hc
    (fun c => T c initialJointTransferTerm)
    (fun c hc => hkernel c hc [] (Nat.zero_le _) initialJointTransferTerm
      (by simp [jointTransferTerms, orderedTransferAction])) (T c)
    (fun js hjs t ht => hkernel c hc _ (by simpa using Nat.add_le_add_right hjs ps.length) t ht)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
