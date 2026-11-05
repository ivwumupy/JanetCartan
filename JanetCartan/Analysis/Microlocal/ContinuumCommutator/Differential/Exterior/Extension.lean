module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Exterior.Operators

/-!
# The exterior commutator on every Sobolev datum

The finite surviving Leibniz expression constructs the exterior contribution to
`app:ch_background:eq:bg-commutator`; no operator bound is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.Exterior

open Pseudodifferential PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The surviving ordered Leibniz expression on every `H^(|is|-1)` datum,
with literal multiplication by derivatives of `q`
(`app:ch_background:eq:bg-commutator`). -/
def commutator (q : Torus n → ℝ) (hq : IsSmoothPeriodic q) (is : List (Fin n)) :
    PeriodicSobolevSpace n F (is.length - 1) →L[ℝ] PeriodicL2 n F :=
  ((differentialCommutatorTerms is).attach.map (fun p ↦
    (multiplication (periodicCoordinateDerivList p.val.1 q)
      (hq.coordinateDerivList p.val.1).1).comp
      (derivativeToL2 (is.length - 1) p.val.2
        (differentialCommutatorTerms_spec is p.val p.property).2.2))).sum

omit [FiniteDimensional ℝ F] in
private theorem list_sum_apply {α : Type*} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (l : List α) (T : α → E →L[ℝ] PeriodicL2 n F) (v : E) :
    (l.map T).sum v = (l.map (fun a ↦ T a v)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, add_apply, ih]

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem list_sum_ae {α : Type*} (l : List α) (u : α → PeriodicL2 n F)
    (f : α → Torus n → F) (hu : ∀ a ∈ l, u a =ᵐ[volume] f a) :
    ((l.map u).sum : PeriodicL2 n F) =ᵐ[volume] (l.map f).sum := by
  induction l with
  | nil => simpa using (Lp.coeFn_zero F 2 volume)
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (Lp.coeFn_add _ _).trans
      ((hu a (by simp)).add (ih (fun b hb ↦ hu b (by simp [hb]))))

/-- Literal surviving expression on smooth fields. Together with
`coordinateDerivList_commutator`, this identifies the bounded construction with
`[D^is,M_q]` (`app:ch_background:eq:bg-commutator`). -/
theorem commutator_ofSmooth_ae (q : Torus n → ℝ) (hq : IsSmoothPeriodic q)
    (is : List (Fin n)) (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    commutator q hq is (ofSmooth (is.length - 1) f hf) =ᵐ[volume]
      periodicCoordinateDerivList is (fun x ↦ q x • f x) -
        (fun x ↦ q x • periodicCoordinateDerivList is f x) := by
  rw [coordinateDerivList_commutator hq hf]
  simp only [commutator, list_sum_apply]
  have h := list_sum_ae (differentialCommutatorTerms is).attach
    (fun p ↦ (multiplication (periodicCoordinateDerivList p.val.1 q)
      (hq.coordinateDerivList p.val.1).1).comp
      (derivativeToL2 (is.length - 1) p.val.2
        (differentialCommutatorTerms_spec is p.val p.property).2.2)
        (ofSmooth (is.length - 1) f hf))
    (fun p ↦ fun x ↦ periodicCoordinateDerivList p.val.1 q x •
      periodicCoordinateDerivList p.val.2 f x) (by
        intro p _
        simp only [ContinuousLinearMap.comp_apply, derivativeToL2_ofSmooth,
          multiplication_ofSmooth (hq.coordinateDerivList _) (hf.coordinateDerivList _) 0 0]
        exact toL2_ofSmooth_ae 0 _ _)
  rw [List.attach_map_val (f := fun p : List (Fin n) × List (Fin n) ↦ fun x ↦
    periodicCoordinateDerivList p.1 q x • periodicCoordinateDerivList p.2 f x)] at h
  exact h

/-- Equality with the classical L² commutator on smooth fields
(`app:ch_background:eq:bg-commutator`). -/
theorem commutator_ofSmooth (q : Torus n → ℝ) (hq : IsSmoothPeriodic q)
    (is : List (Fin n)) (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    commutator q hq is (ofSmooth (is.length - 1) f hf) =
      toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is (fun x ↦ q x • f x))
        ((smooth_smul hq hf).coordinateDerivList is)) -
      multiplication q hq.1 (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
        (hf.coordinateDerivList is))) := by
  apply Lp.ext
  filter_upwards [commutator_ofSmooth_ae q hq is f hf,
    Lp.coeFn_sub (toL2 0 (ofSmooth 0 _ ((smooth_smul hq hf).coordinateDerivList is)))
      (multiplication q hq.1 (toL2 0 (ofSmooth 0 _ (hf.coordinateDerivList is)))),
    toL2_ofSmooth_ae 0 _ ((smooth_smul hq hf).coordinateDerivList is),
    multiplication_ae q hq.1 (toL2 0 (ofSmooth 0 _ (hf.coordinateDerivList is))),
    toL2_ofSmooth_ae 0 _ (hf.coordinateDerivList is)] with x h₁ h₂ h₃ h₄ h₅
  rw [h₂]
  simpa only [Pi.sub_apply, h₃, h₄, h₅] using h₁

/-- A finite constant for each derivative order, uniform over all ordered words
of that length. This is constructed from bounded literal branch operators
(`app:ch_background:eq:bg-commutator`). -/
def commutatorConstant (q : Torus n → ℝ) (hq : IsSmoothPeriodic q) (s : ℕ) : ℝ :=
  1 + ∑ w : Fin s → Fin n, ‖commutator (F := F) q hq (List.ofFn w)‖

/-- The fixed exterior constant is positive
(`app:ch_background:eq:bg-commutator`). -/
theorem commutatorConstant_pos (q : Torus n → ℝ) (hq : IsSmoothPeriodic q) (s : ℕ) :
    0 < commutatorConstant (F := F) q hq s := by
  unfold commutatorConstant
  positivity

/-- The required derivative-losing bound on every Sobolev datum. In particular,
for every word of length `s ≥ 1`, its domain is `H^(s-1)`
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_commutator_le (q : Torus n → ℝ) (hq : IsSmoothPeriodic q)
    (is : List (Fin n)) (u : PeriodicSobolevSpace n F (is.length - 1)) :
    ‖commutator q hq is u‖ ≤ commutatorConstant (F := F) q hq is.length * ‖u‖ := by
  apply (commutator q hq is).le_opNorm u |>.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  have h := Finset.single_le_sum (fun w (_ : w ∈ Finset.univ) ↦
    norm_nonneg (commutator (F := F) q hq (List.ofFn w))) (Finset.mem_univ is.get)
  have he := congrArg (fun js : List (Fin n) ↦ ‖commutator (F := F) q hq js‖)
    (List.ofFn_get is)
  rw [he] at h
  unfold commutatorConstant
  linarith

end JanetCartan.ContinuumCommutator.Exterior
