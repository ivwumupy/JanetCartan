module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Energy
public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Completion

/-!
# Compactly supported smooth kernels in Cartesian jet coordinates

Shared data for the common kernel estimate in `app:ch_regular:lem:finite-chain`.
Output coordinates have the order used by classical test fields; integration
coordinates have the order used by the L² jet measures. No Euclidean norm or
additional inner product on the coordinate space is introduced.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FiniteChain.Retarded.KernelSobolev

/-- A smooth kernel with explicit common compact base supports, as in the
common kernel estimate of `app:ch_regular:lem:finite-chain`. All fields describe
the kernel itself; none assume bounds or regularity of its integral operator. -/
structure SupportedSmoothKernel (d e : ℕ) where
  toFun : (ℝ × (Fin e → ℝ)) → ((Fin d → ℝ) × ℝ) → ℂ
  smooth : ContDiff ℝ ∞ (Function.uncurry toFun)
  inputSupport : Set ((Fin d → ℝ) × ℝ)
  outputSupport : Set (ℝ × (Fin e → ℝ))
  compact_inputSupport : IsCompact inputSupport
  compact_outputSupport : IsCompact outputSupport
  zero_off_input : ∀ x y, y ∉ inputSupport → toFun x y = 0
  zero_off_output : ∀ x y, x ∉ outputSupport → toFun x y = 0

/-- The actual kernel integral, with the coordinate swap required by the
Cartesian jet spaces (`app:ch_regular:eq:chain-tail`). -/
def kernelIntegral {d e : ℕ} (K : SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (f : (ℝ × (Fin d → ℝ)) → ℂ)
    (x : ℝ × (Fin e → ℝ)) : ℂ :=
  ∫ y, K.toFun x y * f (y.2, y.1) ∂μ

/-- The classical output jet of a kernel column
(`app:ch_regular:lem:finite-chain`). This is an actual iterated derivative. -/
def kernelJet {d e m : ℕ} (K : SupportedSmoothKernel d e)
    (i : RetardedSobolev.Spaces.JetIndex e m)
    (p : (Fin e → ℝ) × ℝ) (y : (Fin d → ℝ) × ℝ) : ℂ :=
  RetardedSobolev.Spaces.jet i (fun x ↦ K.toFun x y) p

/-- Each kernel column is smooth in the original Cartesian coordinates
(`app:ch_regular:lem:finite-chain`). -/
theorem kernelColumn_contDiff {d e : ℕ} (K : SupportedSmoothKernel d e)
    (y : (Fin d → ℝ) × ℝ) : ContDiff ℝ ∞ (fun x ↦ K.toFun x y) :=
  K.smooth.comp (contDiff_id.prodMk contDiff_const)

/-- Kernel jets preserve the common input support
(`app:ch_regular:lem:finite-chain`). -/
theorem kernelJet_zero_off_input {d e m : ℕ} (K : SupportedSmoothKernel d e)
    (i : RetardedSobolev.Spaces.JetIndex e m) (p : (Fin e → ℝ) × ℝ)
    (y : (Fin d → ℝ) × ℝ) (hy : y ∉ K.inputSupport) : kernelJet K i p y = 0 := by
  have he : (fun x ↦ K.toFun x y) = 0 := funext fun x ↦ K.zero_off_input x y hy
  unfold kernelJet
  rw [he]
  exact congrFun ((RetardedSobolev.Spaces.jetLinear i).map_zero) p

/-- Kernel jets preserve the common output support
(`app:ch_regular:lem:finite-chain`). -/
theorem kernelJet_zero_off_output {d e m : ℕ} (K : SupportedSmoothKernel d e)
    (i : RetardedSobolev.Spaces.JetIndex e m) (p : (Fin e → ℝ) × ℝ)
    (y : (Fin d → ℝ) × ℝ) (hp : (p.2, p.1) ∉ K.outputSupport) :
    kernelJet K i p y = 0 := by
  apply RetardedSobolev.Spaces.jet_eq_zero_off_tsupport i (kernelColumn_contDiff K y)
  have hs : tsupport (fun x ↦ K.toFun x y) ⊆ K.outputSupport := by
    apply closure_minimal _ K.compact_outputSupport.isClosed
    intro x hx
    by_contra h
    exact hx (K.zero_off_output x y h)
  exact fun h ↦ hp (hs h)

/-- The finite-support Hilbert–Schmidt factor in the common kernel estimate
of `app:ch_regular:lem:finite-chain`. -/
def compactSupportFactor {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (s : Set X) (t : Set Y) : ℝ :=
  Real.sqrt (μ.real s) * Real.sqrt (ν.real t)

/-- Nonnegativity of the support factor (`app:ch_regular:eq:chain-tail`). -/
theorem compactSupportFactor_nonneg {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (s : Set X) (t : Set Y) :
    0 ≤ compactSupportFactor μ ν s t := by
  unfold compactSupportFactor
  positivity

end JanetCartan.FiniteChain.Retarded.KernelSobolev
