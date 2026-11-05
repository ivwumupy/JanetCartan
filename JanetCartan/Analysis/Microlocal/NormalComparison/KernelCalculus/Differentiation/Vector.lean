module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Differentiation.Scalar
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Vector
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Parameter differentiation with finite vector output

The actual operator into `NormalOutputL2` in `app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Topology ContDiff

namespace JanetCartan.NormalComparison

variable {d m r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The finite vector compact kernel operator is differentiable in operator norm
for a jointly C¹ family on a fixed compact support. Its derivative has the actual
parameter derivative entries (`app:ch_osc:prop:osc-normal`). -/
theorem hasDerivAt_compactVectorKernelOperator (D : Set U)
    {t : Fin r → ℝ → E × U → ℂ}
    (ht : ∀ i, ContDiff ℝ 1 (Function.uncurry (t i)))
    {K : Set (E × U)} (hK : IsCompact K)
    (hs : ∀ i s z, z ∉ K → t i s z = 0) (s₀ : ℝ) :
    HasDerivAt
      (fun s ↦ compactVectorKernelOperator D (t := fun i x u ↦ t i s (x, u))
        (fun i ↦ continuous_kernelSlice (ht i) s)
        (fun i ↦ hasCompactSupport_kernelSlice hK (hs i) s))
      (compactVectorKernelOperator D
        (t := fun i x u ↦ kernelParameterDeriv (t i) s₀ (x, u))
        (fun i ↦ continuous_kernelParameterDeriv_slice (ht i) s₀)
        (fun i ↦ hasCompactSupport_kernelParameterDeriv (ht i) hK (hs i) s₀)) s₀ := by
  let I := Lp ℂ 2 (volume.restrict D)
  let O := Lp (α := E) ℂ 2 volume
  let P := ContinuousLinearMap.piEquivL ℂ I (fun _ : Fin r ↦ O)
  let Q := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ O)).symm.toContinuousLinearMap
  let L := ((ContinuousLinearMap.compL ℂ I (Fin r → O) (NormalOutputL2 d r)) Q).comp
    P.toContinuousLinearMap
  have hh := hasDerivAt_pi.mpr fun i ↦
    hasDerivAt_compactKernelOperator (μ := volume.restrict D) (ν := volume)
      (ht i) hK (hs i) s₀
  exact (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s₀ hh

end JanetCartan.NormalComparison
