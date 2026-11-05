module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Compact
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.InactiveSource.Realization

/-!
# Literal annular branch kernels of the published L² operators

Carrier multiplication preserves the compact smooth test domain under phase
smoothness only on the source support. The low-calculus realization of each
physical branch then identifies the SAME annular operator with the normalized
joint integral. The input is the actual derivative of the original datum.
Source: restoration after `new:eq:carrier-ibp` and the annular part of
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open FourierIntegral FourierIntegral.FullLowBounds CompactTransfer BranchAmplitudes ModifiedLow
open JanetCartan.ResponseTransfer.Complement RegularSector.Characteristic.EvolutionIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Modulation of the original compact test, using phase regularity only on a
neighborhood of its support. This supplies the actual low-calculus input for
`new:eq:carrier-ibp`; no global smooth phase extension is required. -/
def graphTestModulation (lam : ℝ) (φ : E → ℝ) {S : Set E} (hS : IsOpen S)
    (hφ : ContDiffOn ℝ ∞ φ S) (u : graphTestSpace n r) (hs : tsupport u.val ⊆ S) :
    graphTestSpace n r :=
  ⟨fun x => carrier lam φ x • u.val x,
    InactiveSource.contDiff_carrier_source (d := n) (F := V) hS lam φ u.val hφ u.property.1.contDiffOn hs,
    u.property.2.smul_left (f := carrier lam φ)⟩

/-- Test modulation is exactly the published unit-modulus L² multiplier.
This connects the low graph realization to the same annular envelope operator
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem graphTestModulation_toLp (lam : ℝ) (φ : E → ℝ) (hcφ : Continuous φ)
    {S : Set E} (hS : IsOpen S) (hφ : ContDiffOn ℝ ∞ φ S)
    (u : graphTestSpace n r) (hs : tsupport u.val ⊆ S) :
    graphTestToLp (graphTestModulation lam φ hS hφ u hs) =
      carrierMultiplication lam φ hcφ (graphTestToLp u) := by
  apply Lp.ext
  filter_upwards [(graphTest_memLp (graphTestModulation lam φ hS hφ u hs)).coeFn_toLp,
    carrierMultiplication_ae lam φ hcφ (graphTestToLp u),
    (graphTest_memLp u).coeFn_toLp] with x hx hy hu
  change (graphTestToLp u : H) x = u.val x at hu
  exact hx.trans (by rw [hy, hu]; rfl)

/-- An explicit physical test realization gives the literal demodulated
kernel on the SAME L² space. It applies to both original and reversed graph
kernels, with the latter's exchanged conjugate-transposed amplitude.
Source: restoring the carrier following `new:eq:carrier-ibp`. -/
theorem demodulatedL2Operator_ae_kernel
    (T : H →L[ℂ] H) (K : (E → Fin r → ℂ) → E → Fin r → ℂ)
    (hT : ∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
      fun x => WithLp.toLp 2 (K (fun y => (u.val y).ofLp) x))
    (lam : ℝ) (φ : E → ℝ) (hcφ : Continuous φ)
    {S : Set E} (hS : IsOpen S) (hφ : ContDiffOn ℝ ∞ φ S)
    (u : graphTestSpace n r) (hs : tsupport u.val ⊆ S) :
    demodulatedL2Operator lam φ hcφ T (graphTestToLp u) =ᵐ[volume]
      fun x => WithLp.toLp 2 (carrier (-lam) φ x •
        K (fun y => carrier lam φ y • (u.val y).ofLp) x) := by
  have hi := hT (graphTestModulation lam φ hS hφ u hs)
  rw [graphTestModulation_toLp lam φ hcφ hS hφ u hs] at hi
  filter_upwards [carrierMultiplication_ae (-lam) φ hcφ
    (T (carrierMultiplication lam φ hcφ (graphTestToLp u))), hi] with x hx hy
  change carrierMultiplication (-lam) φ hcφ
    (T (carrierMultiplication lam φ hcφ (graphTestToLp u))) x = _
  rw [hx, hy]
  rfl

variable {d : ℕ} {P ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]
local notation "X" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The actual forward annular branch has the normalized joint kernel on
its original output domain. The only operator input is its physical compact
smooth test realization, supplied by
`exists_annularBranchElapsedGraph_of_primitive_jets`. Joint integrability is
proved from the primitive data by `integrable_jointBranch_of_primitive_geometry`.
No transfer identity or output regularity is an assumption (`new:eq:carrier-ibp`). -/
theorem annularBranchOperator_ae_jointIntegral
    (b : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (elapsed : ℝ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (φ : X → P → ℝ) (w₀ : X × P → CarrierVariables (d + 1))
    (α : (X × P) → CarrierVariables (d + 1) → Mat) (a : X × P → Fin r → ℂ)
    (t : JointTransferTerm (d + 1) P Mat ι) (c : P)
    (hcφ : Continuous (fun x => φ x c))
    {S W : Set X} (hS : IsOpen S) (hφ : ContDiffOn ℝ ∞ (fun x => φ x c) S)
    (u : graphTestSpace (d + 1) r) (hs : tsupport u.val ⊆ S)
    (hu : ∀ z, (u.val z).ofLp = originalDatumDerivative t.datumWord a (z, c))
    (hreal : ∀ u : graphTestSpace (d + 1) r,
      fullGraphOperator (elapsedPhase Ψ elapsed) (modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c))
        (graphTestToLp u) =ᵐ[volume]
      graphTestOutput (elapsedPhase Ψ elapsed) (modifiedAmplitude lam p
        (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c)) u)
    (hΘ : ∀ x ∈ W, ∀ z θ, modifiedAmplitude lam p
      (normalizedTermAmplitude b (elapsedCarrierPhase Ψ elapsed φ) w₀ α t c) x z (lam • θ) ≠ 0 →
      elapsedPhase Ψ elapsed x (lam • θ) = lam * elapsedPhase Ψ elapsed x θ)
    (hi : ∀ x ∈ W, Integrable (fun w => oscillation (elapsedCarrierPhase Ψ elapsed φ) lam (x, c) w •
      jointTransferTermValue b ReverseDerivative.matrixAction
        (elapsedCarrierPhase Ψ elapsed φ) w₀ α a t (x, c) w))
    (hW : MeasurableSet W) :
    annularBranchOperator b Ψ elapsed lam p φ w₀ α t c hcφ (graphTestToLp u)
      =ᵐ[volume.restrict W] fun x => WithLp.toLp 2
        (normalizedBranchIntegral b (elapsedCarrierPhase Ψ elapsed φ) w₀ α a t lam p (x, c)) := by
  have hk := demodulatedL2Operator_ae_kernel _ _ hreal lam (fun x => φ x c) hcφ hS hφ u hs
  filter_upwards [ae_restrict_of_ae hk, ae_restrict_mem hW] with x hx hxW
  change demodulatedL2Operator _ _ _ _ _ x = _
  rw [hx]
  simp_rw [hu]
  exact congrArg (WithLp.toLp 2)
    (demodulated_branchGraphOperator_eq_jointIntegral b (elapsedPhase Ψ elapsed) φ w₀ α a
      t hlam p (x, c) (hΘ x hxW) (hi x hxW))

/-- The same identification for the reversed phase uses the Hilbert adjoint
of the forward graph with amplitude `fun x z ξ => (A z x ξ).conjTranspose`.
The independent reverse-branch producer supplies precisely this physical test
realization. It is not necessary to wait for that producer to prove this
implication (`new:eq:carrier-ibp`). -/
theorem reverseAnnularBranchOperator_ae_jointIntegral
    (b : OrthonormalBasis ι ℝ (CarrierVariables (d + 1)))
    (Ψ : TwoTimePhase d) (elapsed : ℝ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ)
    (φ : X → P → ℝ) (w₀ : X × P → CarrierVariables (d + 1))
    (α : (X × P) → CarrierVariables (d + 1) → Mat) (a : X × P → Fin r → ℂ)
    (t : JointTransferTerm (d + 1) P Mat ι) (c : P)
    (hcφ : Continuous (fun x => φ x c))
    {S W : Set X} (hS : IsOpen S) (hφ : ContDiffOn ℝ ∞ (fun x => φ x c) S)
    (u : graphTestSpace (d + 1) r) (hs : tsupport u.val ⊆ S)
    (hu : ∀ z, (u.val z).ofLp = originalDatumDerivative t.datumWord a (z, c))
    (hreal : ∀ u : graphTestSpace (d + 1) r,
      (fullGraphOperator (elapsedPhase Ψ elapsed) (fun x z ξ =>
        (modifiedAmplitude lam p (normalizedTermAmplitude b
          (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c) z x ξ).conjTranspose)).adjoint
        (graphTestToLp u) =ᵐ[volume] fun x => WithLp.toLp 2
      (reverseGraphOperator (elapsedPhase Ψ elapsed) (fun y z ξ =>
        modifiedAmplitude lam p (normalizedTermAmplitude b
          (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c) z y ξ)
        (fun y => (u.val y).ofLp) x))
    (hΘ : ∀ x ∈ W, ∀ z θ, modifiedAmplitude lam p
      (normalizedTermAmplitude b (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α t c)
        x z (lam • θ) ≠ 0 →
      elapsedPhase Ψ elapsed z (lam • θ) = lam * elapsedPhase Ψ elapsed z θ)
    (hi : ∀ x ∈ W, Integrable (fun w =>
      oscillation (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) lam (x, c) w •
      jointTransferTermValue b ReverseDerivative.matrixAction
        (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ) w₀ α a t (x, c) w))
    (hW : MeasurableSet W) :
    reverseAnnularBranchOperator b Ψ elapsed lam p φ w₀ α t c hcφ (graphTestToLp u)
      =ᵐ[volume.restrict W] fun x => WithLp.toLp 2
        (normalizedBranchIntegral b (adjointCarrierPhase (elapsedPhase Ψ elapsed) φ)
          w₀ α a t lam p (x, c)) := by
  have hk := demodulatedL2Operator_ae_kernel _ _ hreal lam (fun x => φ x c) hcφ hS hφ u hs
  filter_upwards [ae_restrict_of_ae hk, ae_restrict_mem hW] with x hx hxW
  change demodulatedL2Operator _ _ _ _ _ x = _
  rw [hx]
  simp_rw [hu]
  exact congrArg (WithLp.toLp 2)
    (demodulated_reverseBranchGraphOperator_eq_jointIntegral b (elapsedPhase Ψ elapsed) φ w₀ α a
      t hlam p (x, c) (hΘ x hxW) (hi x hxW))

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
