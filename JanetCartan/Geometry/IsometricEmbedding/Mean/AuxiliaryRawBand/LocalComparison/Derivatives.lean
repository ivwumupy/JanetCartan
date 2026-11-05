module

public import JanetCartan.Analysis.Fourier.Periodic.Sobolev
public import JanetCartan.Analysis.Sobolev.Local.Comparison.Cartesian

/-!
# Cartesian derivatives on the physical chart

The field and strain consumers in `app:ch_background:prop:bg-mixed-physical`
need equality of actual Euclidean derivatives on their open immersion chart.
No regularity outside that chart is needed for the physical representative.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.AuxiliaryRawBand

/-- Ordered periodic derivatives are the actual Cartesian evaluations of the
Fréchet jet (`app:not:fourier`, `app:ch_background:prop:bg-mixed-physical`). -/
theorem periodicLift_coordinateDerivList_eq_iteratedFDeriv {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Torus n → F} (hf : IsSmoothPeriodic f) (is : List (Fin n)) :
    periodicLift (periodicCoordinateDerivList is f) = fun x ↦
      iteratedFDeriv ℝ is.length (periodicLift f) x
        (fun j ↦ EuclideanSpace.basisFun (Fin n) ℝ (is.get j)) := by
  induction is with
  | nil => simp [periodicCoordinateDerivList]
  | cons i is ih =>
    rw [periodicCoordinateDerivList, periodicLift_coordinateDeriv (hf.coordinateDerivList is).2,
      ih]
    funext x
    simpa [Fin.tail_def, EuclideanSpace.basisFun_apply] using
      (hf.2.contDiffAt.differentiableAt_iteratedFDeriv (m := is.length) (x := x) (by exact_mod_cast (ENat.natCast_lt_top is.length))).iteratedFDeriv_succ_apply_left'
        (m := fun j ↦ EuclideanSpace.basisFun (Fin n) ℝ ((i :: is).get j)) |>.symm


variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The project's existing Cartesian jet derivative agrees with the lift of
its periodic multiindex derivative (`app:not:fourier`). -/
theorem cartesianJetDerivative_periodicLift {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (α : Fin n → ℕ) :
    LocalSobolev.cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j (periodicLift f)) α =
      periodicLift (periodicMultiindexDeriv α f) :=
  (periodicLift_coordinateDerivList_eq_iteratedFDeriv hf (sobolevDerivativeList α)).symm

/-- Equality on an OPEN physical chart propagates to every actual Fréchet jet
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem iteratedFDeriv_eqOn_of_eqOn_periodicLift
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (heq : EqOn g (periodicLift f) W) (j : ℕ) :
    EqOn (iteratedFDeriv ℝ j g) (iteratedFDeriv ℝ j (periodicLift f)) W := by
  intro x hx
  rw [← iteratedFDerivWithin_of_isOpen j hW hx,
    ← iteratedFDerivWithin_of_isOpen j hW hx]
  exact heq.iteratedFDerivWithin j hx

/-- Cartesian derivatives of the physical field and full strain can be
replaced by the parent's periodic representatives on the open chart
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem cartesianJetDerivative_eqOn_of_eqOn_periodicLift
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (heq : EqOn g (periodicLift f) W) (α : Fin n → ℕ) :
    EqOn (LocalSobolev.cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j g) α)
      (periodicLift (periodicMultiindexDeriv α f)) W := by
  intro x hx
  rw [← cartesianJetDerivative_periodicLift hf α]
  unfold LocalSobolev.cartesianJetDerivative
  dsimp only
  rw [iteratedFDeriv_eqOn_of_eqOn_periodicLift hW heq _ hx]

end JanetCartan.AuxiliaryRawBand
