module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.FullKernel
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Finite Hilbert blocks for the pure graph normal

The matrix channels in `app:ch_regular_base:eq:actual-normal-kernel` act on the
shared Euclidean Lebesgue L² direct sum `NormalOutputL2`. These finite block
identities are used by the compact-frequency graph construction.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ComplexInnerProductSpace

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n r : ℕ}

/-- Assemble the finite matrix of scalar L² maps required by
`app:ch_regular_base:eq:actual-normal-kernel`. -/
def blocks (L : Fin r → Fin r → Lp (α := Euclidean n) ℂ 2 →L[ℂ]
    Lp (α := Euclidean n) ℂ 2) : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r :=
  (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ ∑ j, (L i j).comp (PiLp.proj 2 _ j))

/-- The actual channel sum in the graph construction
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem blocks_apply (L : Fin r → Fin r → Lp (α := Euclidean n) ℂ 2 →L[ℂ]
    Lp (α := Euclidean n) ℂ 2) (f : NormalOutputL2 n r) (i : Fin r) :
    blocks L f i = ∑ j, L i j (f j) := by
  change (∑ j, (L i j).comp (PiLp.proj 2 _ j)) f = _
  rw [sum_apply]
  rfl

/-- Taking the Hilbert adjoint transposes the channel indices and takes each
scalar Hilbert adjoint (`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem blocks_adjoint (L : Fin r → Fin r → Lp (α := Euclidean n) ℂ 2 →L[ℂ]
    Lp (α := Euclidean n) ℂ 2) :
    (blocks L).adjoint = blocks (fun j i ↦ (L i j).adjoint) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [blocks_apply, sum_inner, inner_sum, ContinuousLinearMap.adjoint_inner_right]
  exact Finset.sum_comm

/-- The two finite sums in a cross normal, before scalar kernel Fubini
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem blocks_cross_apply
    (L M : Fin r → Fin r → Lp (α := Euclidean n) ℂ 2 →L[ℂ]
      Lp (α := Euclidean n) ℂ 2) (f : NormalOutputL2 n r) (i : Fin r) :
    (blocks L ((blocks M).adjoint f)) i =
      ∑ j, ∑ k, L i k ((M j k).adjoint (f j)) := by
  rw [blocks_adjoint, blocks_apply]
  simp_rw [blocks_apply, map_sum]
  exact Finset.sum_comm

/-- The scalar Plancherel factor in the pure graph construction. Its measure
is Euclidean Lebesgue measure (`app:ch_regular_base:eq:actual-normal-kernel`). -/
def fourierL2 (n : ℕ) : Lp (α := Euclidean n) ℂ 2 ≃ₗᵢ[ℂ]
    Lp (α := Euclidean n) ℂ 2 := Lp.fourierTransformₗᵢ _ _

/-- Plancherel cancels the common source Fourier transform in the pure cross
normal, before any spatial source cutoff is introduced
(`app:ch_regular_base:eq:actual-normal-kernel`). -/
theorem fourier_comp_cross (K L : Lp (α := Euclidean n) ℂ 2 →L[ℂ]
    Lp (α := Euclidean n) ℂ 2) :
    (K.comp (fourierL2 n).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (L.comp (fourierL2 n).toContinuousLinearEquiv.toContinuousLinearMap).adjoint =
      K.comp L.adjoint := by
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  change K (fourierL2 n ((fourierL2 n).symm (L.adjoint f))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

end JanetCartan.FourierIntegral.NormalKernel
