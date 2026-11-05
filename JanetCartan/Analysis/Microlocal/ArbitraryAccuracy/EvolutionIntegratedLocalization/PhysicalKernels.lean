module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CompactKernels
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Identities
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Phase

/-!
# Identification with physical compact-frequency kernels

The half-space estimate concerns exactly the normalized version of Graph's
physical regularized kernel, with three frequency Jacobians. The original
phase need not be globally homogeneous: use the existing degree-one
normalization of its two-time phase. This is the physical-kernel bridge for
`app:ch_regular:eq:chain-tail` and
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FourierIntegral FiniteChain.Graph
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ}

/-- Exact physical-to-normalized kernel identification commutes with the
bounded elapsed integral. The finite graph's primitive carrier and continuity
inputs are the ones used in the existing physical kernel-identification API;
no estimate or uncut identification is a premise. The adjoint uses the SAME
original masks and conjugate multiplier in the original amplitude positions
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem integral_physicalElapsedKernel_eq_normalized
    (backward : Bool) {ρ : ℝ} (hρ : 0 < ρ) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (hΨ : ∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r)))
    (hb : ∀ r ∈ Icc 0 Δ, Continuous
      (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) × Euclidean (d + 1) ↦
        orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (c : ∀ r ∈ Icc 0 Δ,
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi χA χo) :
    (∫ r in Icc 0 Δ, KernelLimits.regularizedJointKernel backward
      (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y) =
    ∫ r in Icc 0 Δ, KernelEstimates.regularizedJointKernel backward ρ
      (elapsedPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) r)
      (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo x y := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  apply PhysicalShells.regularizedJointKernel_eq_normalized backward _ _ _ mi mo χA χo x y
    hρ ?_ (hΨ r hr) (hb r hr) hi ho hg hc (c r hr)
  intro u ξ
  rw [← SymbolBudgets.normalizedPhase_elapsedPhase hρ.ne' Ψ r]
  simp only [WholeImageGeometry.normalizedPhase, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]

/-- The differentiated bounded physical kernel is exactly the differentiated
normalized kernel estimated in `OutputDecay`. This uses equality of the
actual functions, retaining all Fourier normalizations, masks and the literal
adjoint order; no derivative-interchange premise is added
(`app:ch_regular:eq:chain-tail`, `app:ch_regular_base:eq:fixed-time-representation`). -/
theorem iteratedFDeriv_integral_physicalElapsedKernel_eq_normalized
    (backward : Bool) {ρ : ℝ} (hρ : 0 < ρ) (Δ : ℝ)
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1))
    (hΨ : ∀ r ∈ Icc 0 Δ, Continuous (Function.uncurry (elapsedPhase Ψ r)))
    (hb : ∀ r ∈ Icc 0 Δ, Continuous
      (fun p : (Euclidean (d + 1) × Euclidean (d + 1)) × Euclidean (d + 1) ↦
        orientedElapsedAmplitude backward b χout χsource β r p.1.1 p.1.2 p.2))
    (hi : Continuous mi) (ho : Continuous mo) (hg : Continuous χA) (hc : Continuous χo)
    (c : ∀ r ∈ Icc 0 Δ,
      KernelLimits.RegularizedCarriers (orientedElapsedAmplitude backward b χout χsource β r)
        mi χA χo) (m : ℕ) (v : Fin m → Euclidean (d + 1)) :
    iteratedFDeriv ℝ m (fun t ↦ ∫ r in Icc 0 Δ, KernelLimits.regularizedJointKernel backward
      (elapsedPhase Ψ r) (orientedElapsedAmplitude backward b χout χsource β r)
      (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo t y) x v =
    iteratedFDeriv ℝ m (fun t ↦ ∫ r in Icc 0 Δ, KernelEstimates.regularizedJointKernel backward ρ
      (elapsedPhase (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) r)
      (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo t y) x v := by
  have he := funext (fun t ↦ integral_physicalElapsedKernel_eq_normalized backward hρ Δ Ψ b
    χout χsource β mi mo χA χo t y hΨ hb hi ho hg hc c)
  exact congrArg (fun f ↦ iteratedFDeriv ℝ m f x v) he

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
