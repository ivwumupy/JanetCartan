module
public import JanetCartan.Analysis.Fourier.Periodic
/-!
# Coordinate derivatives of periodic fields

Cartesian derivatives for the Fourier convention of paper.tex, `app:not:fourier`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coordinate derivative on the unit torus (paper.tex, `app:not:fourier`). -/
def periodicCoordinateDeriv (i : Fin n) (f : Torus n → F) (x : Torus n) : F :=
  deriv (fun t : ℝ ↦ f (x + Pi.single i (t : AddCircle (1 : ℝ)))) 0

private lemma coordinateQuotientMap : IsOpenQuotientMap (@torusQuotient n) := by
  exact (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
    QuotientAddGroup.isOpenQuotientMap_mk)).comp (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap

private lemma torusQuotient_coordinateLine (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    torusQuotient (x + t • EuclideanSpace.single i 1) =
      torusQuotient x + Pi.single i (t : AddCircle (1 : ℝ)) := by
  classical
  ext j
  by_cases h : j = i
  · subst j
    simp [torusQuotient]
  · simp [torusQuotient, h]

/-- The torus derivative lifts to the Cartesian derivative (`app:not:fourier`). -/
theorem periodicLift_coordinateDeriv {f : Torus n → F} (hf : ContDiff ℝ ∞ (periodicLift f)) (i : Fin n) :
    periodicLift (periodicCoordinateDeriv i f) =
      fun x ↦ fderiv ℝ (periodicLift f) x (EuclideanSpace.single i 1) := by
  funext x
  have hd := ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ)) |>.const_add x)
  have heq (t : ℝ) : periodicLift f (x + t • EuclideanSpace.single i 1) =
      f (torusQuotient x + Pi.single i (t : AddCircle (1 : ℝ))) := by
    rw [periodicLift, Function.comp_apply, torusQuotient_coordinateLine]
  change deriv (fun t : ℝ ↦ f (torusQuotient x + Pi.single i (t : AddCircle (1 : ℝ)))) 0 = _
  simpa only [Function.comp_def, id_eq, zero_smul, add_zero, one_smul, heq] using hd.deriv

/-- Smooth periodic fields remain smooth after a coordinate derivative (`app:not:fourier`). -/
theorem IsSmoothPeriodic.coordinateDeriv {f : Torus n → F} (hf : IsSmoothPeriodic f) (i : Fin n) :
    IsSmoothPeriodic (periodicCoordinateDeriv i f) := by
  have hd : ContDiff ℝ ∞ (periodicLift (periodicCoordinateDeriv i f)) := by
    rw [periodicLift_coordinateDeriv hf.2]
    exact (hf.2.fderiv_right (by simp)).clm_apply contDiff_const
  exact ⟨coordinateQuotientMap.isQuotientMap.continuous_iff.mpr hd.continuous, hd⟩

/-- Coordinate translations differentiate to the torus derivative (`app:not:fourier`). -/
theorem IsSmoothPeriodic.hasDerivAt_coordinate {f : Torus n → F} (hf : IsSmoothPeriodic f) (i : Fin n)
    (x : Torus n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (x + Pi.single i (s : AddCircle (1 : ℝ))))
      (periodicCoordinateDeriv i f (x + Pi.single i (t : AddCircle (1 : ℝ)))) t := by
  classical
  obtain ⟨y, rfl⟩ := coordinateQuotientMap.surjective x
  have hd := ((hf.2.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ)) |>.const_add y)
  have heq (s : ℝ) : periodicLift f (y + s • EuclideanSpace.single i 1) =
      f (torusQuotient y + Pi.single i (s : AddCircle (1 : ℝ))) := by
    rw [periodicLift, Function.comp_apply, torusQuotient_coordinateLine]
  have hder := congr_fun (periodicLift_coordinateDeriv hf.2 i) (y + t • EuclideanSpace.single i 1)
  change periodicCoordinateDeriv i f (torusQuotient (y + t • EuclideanSpace.single i 1)) = _ at hder
  rw [torusQuotient_coordinateLine] at hder
  rw [hder]
  simpa only [Function.comp_def, id_eq, one_smul, heq] using hd
variable {n : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- Real continuous linear maps commute with coordinate differentiation (`app:not:fourier`). -/
theorem periodicCoordinateDeriv_comp_clm {f : Torus n → F} (hf : IsSmoothPeriodic f) (L : F →L[ℝ] G) (i : Fin n) :
    periodicCoordinateDeriv i (fun x ↦ L (f x)) = fun x ↦ L (periodicCoordinateDeriv i f x) := by
  funext x
  have hd := L.hasFDerivAt.comp_hasDerivAt 0 (hf.hasDerivAt_coordinate i x 0)
  simpa only [periodicCoordinateDeriv, Function.comp_def, AddCircle.coe_zero,
    Pi.single_zero, add_zero] using hd.deriv
/-- Applying a real continuous linear map preserves smooth periodicity (`app:not:fourier`). -/
theorem IsSmoothPeriodic.comp_clm {f : Torus n → F} (hf : IsSmoothPeriodic f) (L : F →L[ℝ] G) :
    IsSmoothPeriodic (fun x ↦ L (f x)) :=
  ⟨L.continuous.comp hf.1, L.contDiff.comp hf.2⟩

end JanetCartan
