module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Bounds
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Regularity

/-!
# The smooth kernel-to-Sobolev bridge

For the common kernel estimate of `app:ch_regular:lem:finite-chain`, pointwise
bounds on the actual Cartesian output derivatives give the finite-support
Hilbert–Schmidt bound. Smoothness and differentiation under the integral follow
from the kernel itself. The extension uses the existing classical jet completion,
without any differentiation of the input datum.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.RetardedSobolev.Spaces

namespace JanetCartan.FiniteChain.Retarded.KernelSobolev

variable {d e m : ℕ} (K : SupportedSmoothKernel d e)
  (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- The actual differentiated output belongs to L²
(`app:ch_regular:lem:finite-chain`, common kernel estimate). -/
theorem kernelIntegral_jet_memLp (i : JetIndex e m) (f : Test d) :
    MemLp (jet i (kernelIntegral K μ f.val)) 2 ν :=
  jet_memLp ν i (kernelIntegralLinear K μ f)

/-- Pointwise output-derivative bounds give the precise classical Sobolev bound
with constant `C √μ(input) √ν(output)` (`app:ch_regular:eq:chain-tail`). -/
theorem kernelIntegral_jetMap_bound {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (i : JetIndex e m) p y, ‖kernelJet K i p y‖ ≤ C) (f : Test d) :
    ‖jetMap m ν (kernelIntegralLinear K μ f)‖ ≤
      (C * compactSupportFactor μ ν K.inputSupport (Prod.swap ⁻¹' K.outputSupport)) *
        ‖jetMap 0 μ f‖ :=
  jetMap_bound_of_kernelJet_formula K μ ν (kernelIntegralLinear K μ)
    (fun f i p ↦ kernelIntegral_jet K μ i f p)
    (kernelJet_aestronglyMeasurable K μ) hC hb f

/-- A smooth supported kernel with bounded output jets has a unique extension
from the L² test-field completion to the existing order-`m` Cartesian Sobolev
space (`app:ch_regular:eq:chain-tail`). No operator estimate or
integral-differentiation formula is assumed. -/
theorem exists_kernelSobolevExtension {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (i : JetIndex e m) p y, ‖kernelJet K i p y‖ ≤ C) :
    ∃ A : Sobolev 0 μ →L[ℂ] Sobolev m ν,
      ‖A‖ ≤ C * compactSupportFactor μ ν K.inputSupport (Prod.swap ⁻¹' K.outputSupport) ∧
      (∀ f, A (ofTest 0 μ f) = ofTest m ν (kernelIntegralLinear K μ f)) ∧
      ∀ B : Sobolev 0 μ →L[ℂ] Sobolev m ν,
        (∀ f, B (ofTest 0 μ f) = ofTest m ν (kernelIntegralLinear K μ f)) → B = A :=
  exists_extension_of_kernelJet_formula K μ ν (kernelIntegralLinear K μ)
    (fun f i p ↦ kernelIntegral_jet K μ i f p)
    (kernelJet_aestronglyMeasurable K μ) hC hb

end JanetCartan.FiniteChain.Retarded.KernelSobolev
