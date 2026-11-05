module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior.Operators
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completion of a smooth periodic commutator

The density step for `app:ch_background:eq:bg-commutator`. The smooth estimate
is an explicit input here, supplied by `Differential.Chart.Bounds` in the
concrete amplitude construction. The domain carries the actual Sobolev norm.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace JanetCartan.Pseudodifferential.PeriodicExtension
open PeriodicSobolevSpace
variable {d : ℕ}

/-- Smooth scalar periodic fields, used only as the dense domain of the
commutator in `app:ch_background:eq:bg-commutator`. -/
def smoothFields (d : ℕ) : Submodule ℝ (Torus d → ℂ) where
  carrier := {f | IsSmoothPeriodic f}
  zero_mem' := ⟨continuous_const, contDiff_const⟩
  add_mem' := fun hf hg ↦ ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c _ hf ↦ ⟨hf.1.const_smul c, hf.2.const_smul c⟩

/-- The actual Sobolev realization of the dense smooth domain
(`app:ch_background:eq:bg-commutator`). -/
def smoothRealization (n : ℕ) : smoothFields d →ₗ[ℝ] PeriodicSobolevSpace d ℂ n where
  toFun f := ofSmooth n f.val f.property
  map_add' f g := by
    apply toL2_injective n
    rw [map_add]
    apply Lp.ext
    exact (toL2_ofSmooth_ae n _ _).trans
      (((toL2_ofSmooth_ae n _ f.property).add (toL2_ofSmooth_ae n _ g.property)).symm.trans
        (Lp.coeFn_add _ _).symm)
  map_smul' c f := by
    apply toL2_injective n
    rw [map_smul]
    apply Lp.ext
    exact (toL2_ofSmooth_ae n _ _).trans
      (((toL2_ofSmooth_ae n _ f.property).const_smul c).symm.trans
        (Lp.coeFn_smul c _).symm)

/-- Density is in the Sobolev topology (`app:ch_background:eq:bg-commutator`). -/
theorem denseRange_smoothRealization (n : ℕ) :
    DenseRange (smoothRealization (d := d) n) := denseRange_ofSmooth n

/-- L² realization of a smooth derivative word, expressed through the shared
actual weak derivatives (`app:ch_background:eq:bg-commutator`). -/
def smoothDerivative (is : List (Fin d)) : smoothFields d →ₗ[ℝ] PeriodicL2 d ℂ :=
  (ContinuumCommutator.Exterior.derivativeToL2 is.length is le_rfl).toLinearMap.comp
    (smoothRealization is.length)

/-- The dense-domain derivative is the literal classical derivative
(`app:ch_background:eq:bg-commutator`). -/
theorem smoothDerivative_apply (is : List (Fin d)) (f : smoothFields d) :
    smoothDerivative is f = toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f.val)
      (f.property.coordinateDerivList is)) :=
  ContinuumCommutator.Exterior.derivativeToL2_ofSmooth _ _ _ f.val f.property

/-- The iterated weak identity in L² inner-product notation. This keeps the
normalized measure and reversed test derivative (`app:ch_background:eq:bg-commutator`). -/
theorem weakDerivativeList_iff_inner (is : List (Fin d)) (u v : PeriodicL2 d ℂ) :
    HasPeriodicWeakDerivativeList is u v ↔ ∀ φ : smoothFields d,
      ⟪v, toL2 0 (smoothRealization 0 φ)⟫ =
        (-1 : ℝ) ^ is.length * ⟪u, smoothDerivative is.reverse φ⟫ := by
  have he (φ : smoothFields d) :
      ⟪v, toL2 0 (smoothRealization 0 φ)⟫ = ∫ x, ⟪v x, φ.val x⟫ :=
    inner_periodicL2_ofSmooth v 0 φ.val φ.property
  simp only [he, smoothDerivative_apply, inner_periodicL2_ofSmooth]
  exact ⟨fun h φ ↦ h φ.val φ.property, fun h φ hφ ↦ h ⟨φ, hφ⟩⟩

private theorem weak_add {is : List (Fin d)} {u v u' v' : PeriodicL2 d ℂ}
    (h : HasPeriodicWeakDerivativeList is u v)
    (h' : HasPeriodicWeakDerivativeList is u' v') :
    HasPeriodicWeakDerivativeList is (u + u') (v + v') := by
  rw [weakDerivativeList_iff_inner] at h h' ⊢
  intro φ
  simp only [inner_add_left, h φ, h' φ, mul_add]

private theorem weak_smul {is : List (Fin d)} {u v : PeriodicL2 d ℂ}
    (h : HasPeriodicWeakDerivativeList is u v) (c : ℝ) :
    HasPeriodicWeakDerivativeList is (c • u) (c • v) := by
  rw [weakDerivativeList_iff_inner] at h ⊢
  intro φ
  simp only [real_inner_smul_left, h φ]
  ring

variable (n : ℕ) (is : List (Fin d)) (T : PeriodicL2 d ℂ →L[ℝ] PeriodicL2 d ℂ)

/-- The actual smooth weak commutator relation for the completion step of
`app:ch_background:eq:bg-commutator`. No estimate is part of this relation. -/
def SmoothCommutator (f : smoothFields d) (w : PeriodicL2 d ℂ) : Prop :=
  HasPeriodicWeakDerivativeList is (T (toL2 n (smoothRealization n f)))
    (T (smoothDerivative is f) + w)

/-- The smooth commutator has a unique L² representative
(`app:ch_background:eq:bg-commutator`). -/
theorem SmoothCommutator.unique {f : smoothFields d} {w v : PeriodicL2 d ℂ}
    (hw : SmoothCommutator n is T f w) (hv : SmoothCommutator n is T f v) : w = v :=
  add_left_cancel (HasPeriodicWeakDerivativeList.unique hw hv)

private theorem commutator_add {f g : smoothFields d} {v w : PeriodicL2 d ℂ}
    (hf : SmoothCommutator n is T f v) (hg : SmoothCommutator n is T g w) :
    SmoothCommutator n is T (f + g) (v + w) := by
  unfold SmoothCommutator at *
  simp only [map_add]
  convert weak_add hf hg using 1
  abel

private theorem commutator_smul {f : smoothFields d} {v : PeriodicL2 d ℂ}
    (hf : SmoothCommutator n is T f v) (c : ℝ) :
    SmoothCommutator n is T (c • f) (c • v) := by
  unfold SmoothCommutator at *
  simpa only [map_smul, smul_add] using weak_smul hf c

/-- Completion of the smooth estimate, retaining its additive Hⁿ/L² form.
The concrete producer is `exists_torusL2Operator_periodic_commutator_bound`;
this lemma alone does not assert an amplitude estimate
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_commutator_extension (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (h : ∀ f : smoothFields d, ∃ w : PeriodicL2 d ℂ,
      SmoothCommutator n is T f w ∧
      ‖w‖ ≤ C * (‖smoothRealization n f‖ + B * ‖toL2 n (smoothRealization n f)‖)) :
    ∃ S : PeriodicSobolevSpace d ℂ n →L[ℝ] PeriodicL2 d ℂ,
      (∀ f : smoothFields d, SmoothCommutator n is T f (S (smoothRealization n f))) ∧
      ∀ u, ‖S u‖ ≤ C * (‖u‖ + B * ‖toL2 n u‖) := by
  let L : smoothFields d →ₗ[ℝ] PeriodicL2 d ℂ :=
    { toFun := fun f ↦ (h f).choose
      map_add' := fun f g ↦ (h (f + g)).choose_spec.1.unique n is T
        (commutator_add n is T (h f).choose_spec.1 (h g).choose_spec.1)
      map_smul' := fun c f ↦ (h (c • f)).choose_spec.1.unique n is T
        (commutator_smul n is T (h f).choose_spec.1 c) }
  have hbound (f : smoothFields d) : ‖L f‖ ≤ (C * (1 + B)) * ‖smoothRealization n f‖ := by
    calc
      _ ≤ C * (‖smoothRealization n f‖ + B * ‖toL2 n (smoothRealization n f)‖) :=
        (h f).choose_spec.2
      _ ≤ C * (‖smoothRealization n f‖ + B * ‖smoothRealization n f‖) := by
        gcongr
        exact norm_toL2_le _ _
      _ = _ := by ring
  let S := L.extendOfNorm (smoothRealization n)
  have heq (f : smoothFields d) : S (smoothRealization n f) = L f :=
    LinearMap.extendOfNorm_eq (denseRange_smoothRealization n) ⟨C * (1 + B), hbound⟩ f
  refine ⟨S, fun f ↦ ?_, fun u ↦ ?_⟩
  · rw [heq]
    exact (h f).choose_spec.1
  · refine (denseRange_smoothRealization n).induction
      (P := fun u ↦ ‖S u‖ ≤ C * (‖u‖ + B * ‖toL2 n u‖)) ?_ ?_ u
    · intro v hv
      obtain ⟨f, rfl⟩ := hv
      rw [heq]
      exact (h f).choose_spec.2
    · exact isClosed_le (by fun_prop) (by fun_prop)

/-- Agreement on the smooth weak commutator determines the extension uniquely
(`app:ch_background:eq:bg-commutator`). -/
theorem commutator_extension_unique
    (S R : PeriodicSobolevSpace d ℂ n →L[ℝ] PeriodicL2 d ℂ)
    (hS : ∀ f, SmoothCommutator n is T f (S (smoothRealization n f)))
    (hR : ∀ f, SmoothCommutator n is T f (R (smoothRealization n f))) : S = R := by
  apply DFunLike.coe_injective
  apply (denseRange_smoothRealization n).equalizer S.continuous R.continuous
  funext f
  exact (hS f).unique n is T (hR f)

end JanetCartan.Pseudodifferential.PeriodicExtension
