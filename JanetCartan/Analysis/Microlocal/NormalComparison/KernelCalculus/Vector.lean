module

public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Scalar
public import JanetCartan.Analysis.Microlocal.NormalComparison.ChannelBounds

/-!
# Compact kernels with finite vector output

Construction and actual Hilbert adjoint on `NormalOutputL2` for
`app:ch_osc:prop:osc-normal`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.NormalComparison

variable {d m r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The finite vector integral operator of `app:ch_osc:prop:osc-normal`,
constructed entrywise from its compact scalar kernels. -/
def compactVectorKernelOperator (D : Set U) {t : Fin r → E → U → ℂ}
    (ht : ∀ i, Continuous (Function.uncurry (t i)))
    (hs : ∀ i, HasCompactSupport (Function.uncurry (t i))) :
    Lp ℂ 2 (volume.restrict D) →L[ℂ] NormalOutputL2 d r :=
  (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i ↦ compactKernelOperator (ht i) (hs i)))

/-- The vector operator's actual input integral, coordinate by coordinate,
for `app:ch_osc:prop:osc-normal`. -/
theorem compactVectorKernelOperator_ae_integral (D : Set U) {t : Fin r → E → U → ℂ}
    (ht : ∀ i, Continuous (Function.uncurry (t i)))
    (hs : ∀ i, HasCompactSupport (Function.uncurry (t i)))
    (h : Lp ℂ 2 (volume.restrict D)) (i : Fin r) :
    (compactVectorKernelOperator D ht hs h) i =ᵐ[volume]
      fun x ↦ ∫ u, t i x u * h u ∂volume.restrict D :=
  compactKernelOperator_ae_integral (ht i) (hs i) h

/-- The Hilbert adjoint is the sum of the scalar adjoints, for the genuine
finite vector operator in `app:ch_osc:prop:osc-normal`. -/
theorem compactVectorKernelOperator_adjoint_apply (D : Set U) {t : Fin r → E → U → ℂ}
    (ht : ∀ i, Continuous (Function.uncurry (t i)))
    (hs : ∀ i, HasCompactSupport (Function.uncurry (t i)))
    (f : NormalOutputL2 d r) :
    (compactVectorKernelOperator D ht hs).adjoint f =
      ∑ i, (compactKernelOperator (μ := volume.restrict D) (ht i) (hs i)).adjoint (f i) := by
  apply ext_inner_left ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_right, inner_sum, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (ContinuousLinearMap.adjoint_inner_right
    (compactKernelOperator (μ := volume.restrict D) (ν := volume) (ht i) (hs i)) h (f i)).symm

/-- The actual vector adjoint integral in
`app:ch_osc:eq:osc-exact-normal-kernel`. -/
theorem compactVectorKernelOperator_adjoint_ae_integral (D : Set U)
    {t : Fin r → E → U → ℂ}
    (ht : ∀ i, Continuous (Function.uncurry (t i)))
    (hs : ∀ i, HasCompactSupport (Function.uncurry (t i)))
    (f : NormalOutputL2 d r) :
    (compactVectorKernelOperator D ht hs).adjoint f =ᵐ[volume.restrict D]
      fun u ↦ ∑ i, ∫ x, star (t i x u) * f i x := by
  rw [compactVectorKernelOperator_adjoint_apply]
  have hall := ae_all_iff.mpr (fun i ↦
    compactKernelOperator_adjoint_ae_integral (μ := volume.restrict D) (ht i) (hs i) (f i))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ (compactKernelOperator (μ := volume.restrict D) (ht i) (hs i)).adjoint (f i)),
    hall] with u hu hi
  exact hu.trans (Finset.sum_congr rfl (fun i _ ↦ hi i))

end JanetCartan.NormalComparison
