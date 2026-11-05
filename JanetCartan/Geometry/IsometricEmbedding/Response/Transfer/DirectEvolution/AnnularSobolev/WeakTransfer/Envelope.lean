module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.JointOperators
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.ReverseBranches.Initial

/-!
# Joint derivatives of the fixed physical annular envelope and its adjoint

The normalized amplitude is the literal full masked elapsed amplitude. Thus
parameter differentiation changes only the carrier and original datum, with
the physical operator, elapsed time, frequency and every mask fixed. The
initial-branch identities identify the SAME published annular envelope and its
literal Hilbert adjoint. Source: `app:ch_response:lem:energy-carrier-jets` and
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

/-- Joint derivatives of the actual fixed physical annular envelope.
The exact weak branch expansion retains every original mask, the Fourier
constant and the frequency Jacobian. Only primitive supported geometry and
literal low-calculus realizations are premises (`new:eq:carrier-ibp`). -/
theorem annularEnvelope_joint_derivative_expansion
    (b : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (A : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed : ℝ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    {U : Set (E × P)} {D K : Set (CarrierVariables (d + 1))}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (elapsedCarrierPhase Ψ elapsed φ)) (U ×ˢ D))
    {a : E × P → Fin r → ℂ}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p)) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support ((normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) q) ⊆ K)
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
    (houtput : ∀ q ∈ tsupport (Function.uncurry (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p)), q.1.1 ∈ X)
    {C : Set P} (hC : IsOpen C) (hXU : X ×ˢ C ⊆ U)
    (hcφ : ∀ c, Continuous (fun x => φ x c))
    (hφ : ∀ c ∈ C, ContDiffOn ℝ ∞ (fun x => φ x c) S)
    (hreal : ∀ c ∈ C, ∀ es : List (E × P), es.length ≤ is.length + ps.length →
      ∀ t ∈ jointTransferTerms b es,
      ∀ u : graphTestSpace (d + 1) r,
      fullGraphOperator (elapsedPhase Ψ elapsed) (modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) t c))
        (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (elapsedPhase Ψ elapsed) (modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) t c)) u)
    (hΘ : ∀ c ∈ C, ∀ es : List (E × P), es.length ≤ is.length + ps.length →
      ∀ t ∈ jointTransferTerms b es, ∀ x z θ, modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) t c) x z (lam • θ) ≠ 0 →
        elapsedPhase Ψ elapsed x (lam • θ) = lam * elapsedPhase Ψ elapsed x θ)
    (c : P) (hc : c ∈ C) :
    let T := fun c t => annularBranchOperator b Ψ elapsed lam p φ w₀ (normalizedAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) t c (hcφ c)
      (graphTestToLp (originalDatumTest a ha hKsource has t.datumWord c))
    orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
      ((orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
        (fun c => annularEnvelopeOperator Ψ A χout χsource β π elapsed lam
          (fun x => φ x c) (hcφ c)
          (graphTestToLp (originalDatumTest a ha hKsource has [] c))) c : H) : 𝓢'(E, EuclideanSpace ℂ (Fin r))) =
      ((jointTransferTerms b ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++
        ps.map (fun v => ((0 : E), v)))).map
          fun t => (T c t : 𝓢'(E, EuclideanSpace ℂ (Fin r)))).sum := by
  have h := annularBranchFamily_joint_derivative_expansion b Ψ elapsed hlam p φ w₀
    hU hD hcD hK hKD hf hα ha hs hw₀ hcritical hvalue h₀ hinv hKsource hS hKS has
    ps is hX houtput hC hXU hcφ hφ hreal hΘ c hc
  dsimp only at h ⊢
  simp only [annularBranchOperator_initial_eq b Ψ A χout χsource β π elapsed hlam.ne' p φ w₀] at h
  simpa only [initialJointTransferTerm] using h

/-- Joint derivatives of the actual fixed physical annular Hilbert adjoint.
The exact weak branch expansion retains every original mask, the Fourier
constant and the frequency Jacobian. Only primitive supported geometry and
literal low-calculus realizations are premises (`new:eq:carrier-ibp`). -/
theorem annularEnvelope_adjoint_joint_derivative_expansion
    (b : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (A : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (elapsed : ℝ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (φ : E → P → ℝ) (w₀ : E × P → CarrierVariables (d + 1))
    {U : Set (E × P)} {D K : Set (CarrierVariables (d + 1))}
    (hU : IsOpen U) (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ)) (U ×ˢ D))
    {a : E × P → Fin r → ℂ}
    (hα : ContDiffOn ℝ ∞ (Function.uncurry (normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p)) (U ×ˢ D)) (ha : ContDiff ℝ ∞ a)
    (hs : ∀ q ∈ U, Function.support ((normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) q) ⊆ K)
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
    (houtput : ∀ q ∈ tsupport (Function.uncurry (normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p)), q.1.1 ∈ X)
    {C : Set P} (hC : IsOpen C) (hXU : X ×ˢ C ⊆ U)
    (hcφ : ∀ c, Continuous (fun x => φ x c))
    (hφ : ∀ c ∈ C, ContDiffOn ℝ ∞ (fun x => φ x c) S)
    (hreal : ∀ c ∈ C, ∀ es : List (E × P), es.length ≤ is.length + ps.length →
      ∀ t ∈ jointTransferTerms b es,
      ∀ u : graphTestSpace (d + 1) r,
      (fullGraphOperator (elapsedPhase Ψ elapsed) (fun x z ξ =>
        (modifiedAmplitude lam p (normalizedTermAmplitude b
          (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ (normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) t c) z x ξ).conjTranspose)).adjoint
        (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
      (reverseGraphOperator (elapsedPhase Ψ elapsed) (fun y z ξ =>
        modifiedAmplitude lam p (normalizedTermAmplitude b
          (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ (normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) t c) z y ξ)
        (fun y => (u.val y).ofLp) x))
    (hΘ : ∀ c ∈ C, ∀ es : List (E × P), es.length ≤ is.length + ps.length →
      ∀ t ∈ jointTransferTerms b es, ∀ x z θ, modifiedAmplitude lam p
        (normalizedTermAmplitude b (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ (normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) t c)
          x z (lam • θ) ≠ 0 →
        elapsedPhase Ψ elapsed z (lam • θ) = lam * elapsedPhase Ψ elapsed z θ)
    (c : P) (hc : c ∈ C) :
    let T := fun c t => reverseAnnularBranchOperator b Ψ elapsed lam p φ w₀ (normalizedAdjointAnnularElapsedAmplitude (P := P) A χout χsource β π elapsed lam p) t c (hcφ c)
      (graphTestToLp (originalDatumTest a ha hKsource has t.datumWord c))
    orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
      ((orderedTransferAction (fun v F c => fderiv ℝ F c v) ps
        (fun c => (annularEnvelopeOperator Ψ A χout χsource β π elapsed lam
          (fun x => φ x c) (hcφ c)).adjoint
          (graphTestToLp (originalDatumTest a ha hKsource has [] c))) c : H) : 𝓢'(E, EuclideanSpace ℂ (Fin r))) =
      ((jointTransferTerms b ((is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++
        ps.map (fun v => ((0 : E), v)))).map
          fun t => (T c t : 𝓢'(E, EuclideanSpace ℂ (Fin r)))).sum := by
  have h := reverseAnnularBranchFamily_joint_derivative_expansion b Ψ elapsed hlam p φ w₀
    hU hD hcD hK hKD hf hα ha hs hw₀ hcritical hvalue h₀ hinv hKsource hS hKS has
    ps is hX houtput hC hXU hcφ hφ hreal hΘ c hc
  dsimp only at h ⊢
  simp only [reverseAnnularBranchOperator_initial_eq_adjoint b Ψ A χout χsource β π elapsed hlam.ne' p φ w₀] at h
  simpa only [initialJointTransferTerm] using h

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
