module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Operators
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Distributional

/-!
# Literal demodulated reverse kernels and their distributional limits

The regularized Hilbert adjoints supplied by the primitive graph constructor
act on the same carrier-modulated compact tests. Strong convergence then gives
the distributional realization of the literal reversed carrier kernel.
Consumer: the annular weak-transfer proof of
`app:ch_response:eq:direct-envelope-profile` following `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open FourierIntegral FullLowBounds CompactTransfer BranchAmplitudes ModifiedLow
open JanetCartan.ResponseTransfer.Complement
variable {n r : ℕ}
local notation "En" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure En)

/-- The literal reverse kernel in the branch's own output/source order,
with the original physical normalization and both carrier multipliers.
Source: the adjoint case of `new:eq:carrier-ibp`. -/
def reverseAnnularKernel (S : En → En → ℝ) (φ : En → ℝ) (lam : ℝ)
    (A : FullAmplitude n r) (u : En → Fin r → ℂ) (x : En) : Fin r → ℂ :=
  carrier (-lam) φ x • reverseGraphOperator S (fun z y ξ => A y z ξ)
    (fun z => carrier lam φ z • u z) x

/-- Multiplying a compact smooth graph test by a smooth carrier gives the
actual modulated graph test. No cutoff is added to the datum.
Source: the test realization of `new:eq:carrier-ibp`. -/
def annularCarrierGraphTest (lam : ℝ) (φ : En → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (u : graphTestSpace n r) : graphTestSpace n r :=
  ⟨fun x => carrier lam φ x • u.val x,
    (by
      have hc : ContDiff ℝ ∞ (carrier lam φ) := by
        unfold carrier
        exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hφ))).cexp
      exact hc.smul u.property.1),
    HasCompactSupport.smul_left (f := carrier lam φ) u.property.2⟩

/-- The compact-test modulation is exactly the published L² carrier
multiplication (`app:ch_response:eq:direct-envelope-profile`). -/
theorem graphTestToLp_annularCarrierGraphTest (lam : ℝ) (φ : En → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (u : graphTestSpace n r) :
    graphTestToLp (annularCarrierGraphTest lam φ hφ u) =
      carrierMultiplication lam φ hφ.continuous (graphTestToLp u) := by
  apply Lp.ext
  filter_upwards [(graphTest_memLp (annularCarrierGraphTest lam φ hφ u)).coeFn_toLp,
    carrierMultiplication_ae lam φ hφ.continuous (graphTestToLp u),
    (graphTest_memLp u).coeFn_toLp] with x hx hm hu
  change (graphTestToLp u : H) x = u.val x at hu
  exact hx.trans (by rw [hm, hu]; rfl)

/-- A proved physical reverse test identity gives the literal demodulated
identity on the SAME test datum. `Construction` supplies `hreal` from primitive
jets; this lemma only performs carrier conjugation (`new:eq:carrier-ibp`). -/
theorem demodulated_reverseGraph_test_ae
    (S : En → En → ℝ) (φ : En → ℝ) (lam : ℝ) (hφ : ContDiff ℝ ∞ φ)
    (A : FullAmplitude n r) (T : H →L[ℂ] H)
    (hreal : ∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
      fun x => WithLp.toLp 2
        (reverseGraphOperator S (fun z y ξ => A y z ξ) (fun z => (u.val z).ofLp) x))
    (u : graphTestSpace n r) :
    demodulatedL2Operator lam φ hφ.continuous T (graphTestToLp u) =ᵐ[volume]
      fun x => WithLp.toLp 2 (reverseAnnularKernel S φ lam A (fun z => (u.val z).ofLp) x) := by
  have ht := hreal (annularCarrierGraphTest lam φ hφ u)
  rw [graphTestToLp_annularCarrierGraphTest] at ht
  have hm := carrierMultiplication_ae (-lam) φ hφ.continuous
    (T (carrierMultiplication lam φ hφ.continuous (graphTestToLp u)))
  filter_upwards [hm, ht] with x hx ht
  change carrierMultiplication (-lam) φ hφ.continuous
    (T (carrierMultiplication lam φ hφ.continuous (graphTestToLp u))) x = _
  rw [hx, ht]
  rfl

/-- Strong limits of the actual reverse regularizations realize the literal
carrier kernel distributionally. The producer of the two inputs is
`exists_reverseAnnularBranchElapsedGraph_of_primitive_jets`; no additional
operator estimate is needed. Source: `app:ch_response:eq:direct-envelope-profile`.
-/
theorem reverseAnnularKernel_distributional_of_strong_limit
    (S : En → En → ℝ) (φ : En → ℝ) (lam : ℝ) (hφ : ContDiff ℝ ∞ φ)
    (χ : ℕ → En → ℂ) (A : FullAmplitude n r)
    (T : H →L[ℂ] H) (Treg : ℕ → H →L[ℂ] H)
    (hreal : ∀ j (u : graphTestSpace n r), Treg j (graphTestToLp u) =ᵐ[volume]
      fun x => WithLp.toLp 2 (reverseGraphOperator S
        (frequencyCutFullAmplitude (χ j) (fun z y ξ => A y z ξ))
        (fun z => (u.val z).ofLp) x))
    (hlim : ∀ u, Tendsto (fun j => Treg j u) atTop (𝓝 (T u))) :
    GraphDistributionalRealization (reverseAnnularKernel S φ lam) χ A
      (demodulatedL2Operator lam φ hφ.continuous T) := by
  apply graphDistributionalRealization_of_strong_limit _ χ A _
    (fun j => demodulatedL2Operator lam φ hφ.continuous (Treg j))
  · intro j u
    exact demodulated_reverseGraph_test_ae S φ lam hφ
      (frequencyCutFullAmplitude (χ j) A) (Treg j) (hreal j) u
  · exact demodulatedL2Operator_strongLimit lam φ hφ.continuous Treg T hlim

variable {P ι : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι]
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The realized reverse branch kernel has literally `adjointCarrierPhase`,
including the physical Fourier normalization, `lam^n` frequency Jacobian and
`lam^p` amplitude order. This reuses the exact kernel calculation from
`BranchAmplitudes.Kernel`, rather than an adjoint transport identity.
Source: `new:eq:carrier-ibp`. -/
theorem reverseAnnularKernel_branch_eq_normalized
    (basis : OrthonormalBasis ι ℝ (CarrierVariables n))
    (S : En → En → ℝ) (φ : En → P → ℝ)
    (w₀ : En × P → CarrierVariables n)
    (α : (En × P) → CarrierVariables n → Mat)
    (branch : JointTransferTerm n P Mat ι) (param : P)
    (u : En → Fin r → ℂ) {lam : ℝ} (hlam : 0 < lam) (p : ℤ) (x : En)
    (hS : ∀ z θ, modifiedAmplitude lam p
      (normalizedTermAmplitude basis (adjointCarrierPhase S φ) w₀ α branch param)
        x z (lam • θ) ≠ 0 → S z (lam • θ) = lam * S z θ) :
    reverseAnnularKernel S (fun y => φ y param) lam
      (modifiedAmplitude lam p
        (normalizedTermAmplitude basis (adjointCarrierPhase S φ) w₀ α branch param)) u x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • (lam ^ n •
        ∫ θ : En, ∫ z : En,
          oscillation (adjointCarrierPhase S φ) lam (x, param) (WithLp.toLp 2 (z, θ)) •
            ((lam ^ p) • (branch.amplitude.evaluate
              (jointAmplitudeFields basis (adjointCarrierPhase S φ) w₀ α)
                ((x, param), WithLp.toLp 2 (z, θ))).1).mulVec (u z)) :=
  demodulated_reverseBranchGraphOperator_eq_normalized basis S φ w₀ α branch param u hlam p x hS

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
