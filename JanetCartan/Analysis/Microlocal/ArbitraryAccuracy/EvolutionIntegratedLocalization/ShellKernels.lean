module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.PhysicalKernels

/-!
# Shared literal elapsed shell kernels

The shell summation and strong-limit identification for
`app:ch_regular:eq:chain-tail` concern the same bounded elapsed integral of
Graph's physical regularized kernel. This definition fixes that common input
before the independent deductions. The graph and output cutoffs are independent;
using `PhysicalShells.graphCutoff` and `PhysicalShells.outputCutoff` retains
the contracting low graph shells and the zeroth output-frequency piece.

Unfolding `elapsedPhysicalShellKernel` gives exactly the left-hand side of
`integral_physicalElapsedKernel_eq_normalized`. Its differentiated version is
identified by `iteratedFDeriv_integral_physicalElapsedKernel_eq_normalized`.
Neither definition nor identity asserts an unregularized estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization

open FiniteChain.Graph RegularSector.Characteristic.EvolutionIntegral

/-- The literal bounded physical elapsed shell kernel, with the source and
output localizers at physical frequency scale `ρ`. Both Fourier cutoffs
remain visible. `backward = true` uses the literal adjoint amplitude with
the original masks in reversed order. Consumers: independent shell summation
and identification of the actual strong-integral limit
(`app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:fixed-time-representation`). -/
def elapsedPhysicalShellKernel {d q : ℕ}
    (backward : Bool) (ρ Δ : ℝ) (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q)
    (χout χsource β : Euclidean (d + 1) → ℂ) (mi mo : LocalizerSymbol (d + 1))
    (χA χo : Euclidean (d + 1) → ℝ) (x y : Euclidean (d + 1)) :
    Matrix (Fin q) (Fin q) ℂ :=
  ∫ r in Icc 0 Δ, KernelLimits.regularizedJointKernel backward (elapsedPhase Ψ r)
    (orientedElapsedAmplitude backward b χout χsource β r)
    (fun p ↦ mi (p.1, ρ⁻¹ • p.2)) (fun p ↦ mo (p.1, ρ⁻¹ • p.2)) χA χo x y

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
