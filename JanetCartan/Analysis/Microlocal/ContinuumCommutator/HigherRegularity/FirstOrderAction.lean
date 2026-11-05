module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.WeakDerivatives
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The forward H¹ action from the first differential commutator

The H⁻¹ duality argument needs the bounded H¹ action of both `E` and its
original inverse. Construct the forward action from the order-one member of
the actual differential commutators, so the final assembly takes only the
inverse H¹ action from the first-order regularity producer.

This closes the forward-action premise for `Assembly` in
`app:ch_background:prop:bg-inverse`; density supplies the weak derivatives
before the closed graph theorem supplies continuity.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.HigherRegularity

open PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

variable (E : PeriodicL2 n F →L[ℝ] PeriodicL2 n F)
  (K : (is : List (Fin n)) → is.length = 0 + 1 →
    PeriodicSobolevSpace n F 0 →L[ℝ] PeriodicL2 n F)
  (hK : ∀ (is : List (Fin n)) (hlen : is.length = 0 + 1)
    (f : Torus n → F) (hf : IsSmoothPeriodic f),
    HasPeriodicWeakDerivativeList is (E (toL2 0 (ofSmooth 0 f hf)))
      (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
        (hf.coordinateDerivList is))) + K is hlen (ofSmooth 0 f hf)))

include hK

/-- Extend the first smooth commutator by H¹ density to prove that the forward
operator preserves H¹ (`app:ch_background:eq:bg-commutator`). This argument
requires neither self-adjointness nor any inverse regularity. -/
theorem mem_one_apply_of_commutators (u : PeriodicSobolevSpace n F 1) :
    E (toL2 1 u) ∈ periodicSobolevLevel n F 1 := by
  apply (mem_periodicSobolevLevel_one_iff_weakDerivatives _).mpr
  intro i
  let T : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicL2 n F :=
    E.comp (Exterior.derivativeToL2 1 [i] (by simp)) +
      (K [i] rfl).comp (inclusion (Nat.zero_le 1))
  refine ⟨T u, (hasPeriodicWeakDerivativeList_singleton i _ _).mp ?_⟩
  intro φ hφ
  have he :
      (fun v : PeriodicSobolevSpace n F 1 ↦ ⟪T v, toL2 0 (ofSmooth 0 φ hφ)⟫) =
      (fun v ↦ (-1 : ℝ) ^ ([i] : List (Fin n)).length *
        ⟪E (toL2 1 v), toL2 0 (ofSmooth 0 (periodicCoordinateDerivList [i].reverse φ)
          (hφ.coordinateDerivList _))⟫) := by
    apply (denseRange_ofSmooth 1).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, T, add_apply,
      ContinuousLinearMap.comp_apply, Exterior.derivativeToL2_ofSmooth,
      inner_periodicL2_ofSmooth]
    exact hK [i] rfl f.val f.property φ hφ
  simpa only [inner_periodicL2_ofSmooth] using congrFun he u

/-- Construct the bounded forward H¹ restriction used to define the dual H⁻¹
action in `Assembly` (`app:ch_background:prop:bg-inverse`). Its continuity follows
from the closed graph theorem and the existing injective inclusion into L². -/
theorem exists_firstOrderRestriction_of_commutators :
    ∃ E₁ : PeriodicSobolevSpace n F 1 →L[ℝ] PeriodicSobolevSpace n F 1,
      ∀ u, toL2 1 (E₁ u) = E (toL2 1 u) := by
  let L : PeriodicSobolevSpace n F 1 →ₗ[ℝ] PeriodicSobolevSpace n F 1 :=
    { toFun := fun u ↦ ofL2 1 (E (toL2 1 u)) (mem_one_apply_of_commutators E K hK u)
      map_add' := by
        intro u v
        apply toL2_injective 1
        simp
      map_smul' := by
        intro r u
        apply toL2_injective 1
        simp }
  have hcont : Continuous L := by
    apply L.continuous_of_seq_closed_graph
    intro u x y hx hy
    apply toL2_injective 1
    exact tendsto_nhds_unique (((toL2 1).continuous.tendsto y).comp hy)
      ((E.continuous.comp (toL2 1).continuous).tendsto x |>.comp hx)
  exact ⟨⟨L, hcont⟩, fun _ ↦ rfl⟩

end JanetCartan.ContinuumCommutator.HigherRegularity
