module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Differentiation.Vector
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiation of the actual masked normal composition

The product rule for the genuine Hilbert adjoint and a fixed bounded mask in
`app:ch_osc:prop:osc-normal`. No derivative of the mask is involved.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Topology ContDiff

namespace JanetCartan.NormalComparison

section Hilbert
variable {I O : Type*} [NormedAddCommGroup I] [InnerProductSpace ℂ I] [CompleteSpace I]
  [NormedAddCommGroup O] [InnerProductSpace ℂ O] [CompleteSpace O]

private def adjointRealCLM : (I →L[ℂ] O) →L[ℝ] (O →L[ℂ] I) where
  toFun := ContinuousLinearMap.adjoint
  map_add' := map_add ContinuousLinearMap.adjoint
  map_smul' c T := by
    have hc : starRingEnd ℂ (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
    have hh := map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℂ)) (c : ℂ) T
    rw [hc] at hh
    simpa only [RingHom.id_apply, Complex.coe_smul] using hh
  cont := ContinuousLinearMap.adjoint.continuous

/-- Product rule for a fixed bounded mask and the actual complex Hilbert
adjoint, with a real parameter (`app:ch_osc:prop:osc-normal`). -/
theorem hasDerivAt_maskedNormal_of_hasDerivAt {T : ℝ → I →L[ℂ] O}
    {T' : I →L[ℂ] O} {s : ℝ} (hT : HasDerivAt T T' s) (M : I →L[ℂ] I) :
    HasDerivAt (fun v ↦ (T v).comp (M.comp (T v).adjoint))
      (T'.comp (M.comp (T s).adjoint) + (T s).comp (M.comp T'.adjoint)) s := by
  have ha := (adjointRealCLM (I := I) (O := O)).hasFDerivAt.comp_hasDerivAt s hT
  have hm := (((ContinuousLinearMap.compL ℂ O I I) M).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt s ha
  have hh := ((ContinuousLinearMap.compL ℂ O I O).bilinearRestrictScalars ℝ).hasDerivAt_of_bilinear
    (fun _ ↦ hT) (fun _ ↦ hm)
  convert hh using 1 <;> first | rfl | exact add_comm _ _

end Hilbert

variable {d m r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

/-- Differentiation of the actual compact masked normal operator on
`NormalOutputL2`, derived solely from C¹ kernels with fixed compact spatial
support and a fixed L∞ mask (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem hasDerivAt_compactVectorKernel_maskedNormal (D : Set U)
    {t : Fin r → ℝ → E × U → ℂ}
    (ht : ∀ i, ContDiff ℝ 1 (Function.uncurry (t i)))
    {K : Set (E × U)} (hK : IsCompact K)
    (hs : ∀ i s z, z ∉ K → t i s z = 0)
    (g : Lp ℂ ∞ (volume.restrict D)) (s₀ : ℝ) :
    let T := fun s ↦ compactVectorKernelOperator D (t := fun i x u ↦ t i s (x, u))
      (fun i ↦ continuous_kernelSlice (ht i) s)
      (fun i ↦ hasCompactSupport_kernelSlice hK (hs i) s)
    let T' := compactVectorKernelOperator D
      (t := fun i x u ↦ kernelParameterDeriv (t i) s₀ (x, u))
      (fun i ↦ continuous_kernelParameterDeriv_slice (ht i) s₀)
      (fun i ↦ hasCompactSupport_kernelParameterDeriv (ht i) hK (hs i) s₀)
    let M := AmplitudeBound.multiplicationOperator g
    HasDerivAt (fun s ↦ (T s).comp (M.comp (T s).adjoint))
      (T'.comp (M.comp (T s₀).adjoint) + (T s₀).comp (M.comp T'.adjoint)) s₀ := by
  exact hasDerivAt_maskedNormal_of_hasDerivAt
    (hasDerivAt_compactVectorKernelOperator D ht hK hs s₀)
    (AmplitudeBound.multiplicationOperator g)

end JanetCartan.NormalComparison
