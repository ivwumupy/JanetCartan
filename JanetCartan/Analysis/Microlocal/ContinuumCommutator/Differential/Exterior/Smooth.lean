module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Terms
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Iterated

/-!
# Ordered Leibniz expansion for the exterior normal

The fixed multiplication contribution to `app:ch_background:eq:bg-commutator`.
The consumer is the bounded exterior commutator on the periodic Sobolev scale.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.Exterior

open Pseudodifferential

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smooth scalar multiplication on the shared torus, for
`app:ch_background:eq:bg-commutator`. -/
theorem smooth_smul {q : Torus n → ℝ} {f : Torus n → F}
    (hq : IsSmoothPeriodic q) (hf : IsSmoothPeriodic f) :
    IsSmoothPeriodic (fun x ↦ q x • f x) :=
  ⟨hq.1.smul hf.1, hq.2.smul hf.2⟩

/-- The coordinate product rule used by the exterior normal in
`app:ch_background:eq:bg-commutator`. -/
theorem coordinateDeriv_smul {q : Torus n → ℝ} {f : Torus n → F}
    (hq : IsSmoothPeriodic q) (hf : IsSmoothPeriodic f) (i : Fin n) :
    periodicCoordinateDeriv i (fun x ↦ q x • f x) =
      fun x ↦ periodicCoordinateDeriv i q x • f x +
        q x • periodicCoordinateDeriv i f x := by
  funext x
  simpa only [periodicCoordinateDeriv, Pi.smul_def', AddCircle.coe_zero, Pi.single_zero, add_zero, add_comm]
    using ((hq.hasDerivAt_coordinate i x 0).smul (hf.hasDerivAt_coordinate i x 0)).deriv

private theorem smooth_sum {α : Type*} (l : List α) (f : α → Torus n → F)
    (hf : ∀ a ∈ l, IsSmoothPeriodic (f a)) : IsSmoothPeriodic ((l.map f).sum) := by
  induction l with
  | nil => exact ⟨continuous_const, contDiff_const⟩
  | cons a l ih =>
    exact ⟨(hf a (by simp)).1.add (ih (fun b hb ↦ hf b (by simp [hb]))).1,
      (hf a (by simp)).2.add (ih (fun b hb ↦ hf b (by simp [hb]))).2⟩

private theorem coordinateDeriv_sum {α : Type*} (l : List α) (f : α → Torus n → F)
    (hf : ∀ a ∈ l, IsSmoothPeriodic (f a)) (i : Fin n) :
    periodicCoordinateDeriv i ((l.map f).sum) =
      (l.map (fun a ↦ periodicCoordinateDeriv i (f a))).sum := by
  induction l with
  | nil => funext x; simp [periodicCoordinateDeriv]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := hf a (by simp)
    have hl := smooth_sum l f (fun b hb ↦ hf b (by simp [hb]))
    have hadd : periodicCoordinateDeriv i (f a + (l.map f).sum) =
        periodicCoordinateDeriv i (f a) + periodicCoordinateDeriv i (l.map f).sum := by
      funext x
      simpa only [periodicCoordinateDeriv, Pi.add_apply, Pi.add_def, AddCircle.coe_zero,
        Pi.single_zero, add_zero] using
        ((ha.hasDerivAt_coordinate i x 0).add (hl.hasDerivAt_coordinate i x 0)).deriv
    rw [hadd, ih (fun b hb ↦ hf b (by simp [hb]))]

/-- Exact ordered Leibniz formula, retaining repeated-coordinate multiplicities
(`app:ch_background:eq:bg-commutator`). -/
theorem coordinateDerivList_smul {q : Torus n → ℝ} {f : Torus n → F}
    (hq : IsSmoothPeriodic q) (hf : IsSmoothPeriodic f) (is : List (Fin n)) :
    periodicCoordinateDerivList is (fun x ↦ q x • f x) =
      ((orderedTransferTerms is).map (fun p ↦ fun x ↦
        periodicCoordinateDerivList p.1 q x • periodicCoordinateDerivList p.2 f x)).sum := by
  induction is with
  | nil => simp [periodicCoordinateDerivList, orderedTransferTerms]
  | cons i is ih =>
    rw [periodicCoordinateDerivList, ih, coordinateDeriv_sum]
    · simp only [coordinateDeriv_smul (hq.coordinateDerivList _) (hf.coordinateDerivList _),
        orderedTransferTerms, List.map_append, List.map_map, List.sum_append,
        Function.comp_def, periodicCoordinateDerivList]
      exact List.sum_map_add
    · intro p _
      exact smooth_smul (hq.coordinateDerivList _) (hf.coordinateDerivList _)

/-- The smooth exterior commutator is exactly the surviving Leibniz expression;
the all-datum branch is removed (`app:ch_background:eq:bg-commutator`). -/
theorem coordinateDerivList_commutator {q : Torus n → ℝ} {f : Torus n → F}
    (hq : IsSmoothPeriodic q) (hf : IsSmoothPeriodic f) (is : List (Fin n)) :
    periodicCoordinateDerivList is (fun x ↦ q x • f x) -
        (fun x ↦ q x • periodicCoordinateDerivList is f x) =
      ((differentialCommutatorTerms is).map (fun p ↦ fun x ↦
        periodicCoordinateDerivList p.1 q x • periodicCoordinateDerivList p.2 f x)).sum := by
  rw [coordinateDerivList_smul hq hf, orderedTransferTerms_sum_eq_commutator_add]
  simp only [periodicCoordinateDerivList, add_sub_cancel_right]

/-- The actual exterior coefficient `(1-χ)^2` is smooth
(`app:ch_background:prop:bg-inverse`). -/
theorem smooth_exteriorCoefficient {χ : Torus n → ℝ} (hχ : IsSmoothPeriodic χ) :
    IsSmoothPeriodic (fun x ↦ (1 - χ x) ^ 2) :=
  ⟨(continuous_const.sub hχ.1).pow 2, (contDiff_const.sub hχ.2).pow 2⟩

end JanetCartan.ContinuumCommutator.Exterior
