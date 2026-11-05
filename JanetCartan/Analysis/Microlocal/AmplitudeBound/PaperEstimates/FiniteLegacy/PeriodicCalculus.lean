module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoxScaling

/-!
# Finite periodic derivatives for the amplitude estimate

The integration-by-parts step of `app:ch_osc:lem:osc-amplitude` needs only
the finite derivative order appearing in its estimate. These lemmas retain
that order instead of imposing qualitative smoothness of every order.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.AmplitudeBound.FiniteLegacy

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem quotientMap : IsOpenQuotientMap (@torusQuotient n) :=
  (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
    QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap

private theorem quotient_coordinateLine (i : Fin n) (x : E) (t : ℝ) :
    torusQuotient (x + t • EuclideanSpace.single i 1) =
      torusQuotient x + Pi.single i (t : AddCircle (1 : ℝ)) := by
  classical
  ext j
  by_cases h : j = i
  · subst j
    simp [torusQuotient]
  · simp [torusQuotient,h]

/-- The torus derivative is the Cartesian derivative under mere differentiability
(`app:ch_osc:lem:osc-amplitude`). -/
theorem periodicLift_coordinateDeriv_of_differentiable {f : Torus n → ℂ}
    (hf : Differentiable ℝ (periodicLift f)) (i : Fin n) :
    periodicLift (periodicCoordinateDeriv i f) =
      fun x ↦ fderiv ℝ (periodicLift f) x (EuclideanSpace.single i 1) := by
  funext x
  have hd := (hf (x + id (0 : ℝ) • EuclideanSpace.single i 1)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ)) |>.const_add x)
  have heq (t : ℝ) : periodicLift f (x + t • EuclideanSpace.single i 1) =
      f (torusQuotient x + Pi.single i (t : AddCircle (1 : ℝ))) := by
    rw [periodicLift,Function.comp_apply,quotient_coordinateLine]
  change deriv (fun t : ℝ ↦ f (torusQuotient x + Pi.single i (t : AddCircle (1 : ℝ)))) 0 = _
  simpa only [Function.comp_def,id_eq,zero_smul,add_zero,one_smul,heq] using hd.deriv

/-- A coordinate derivative loses exactly one finite derivative
(`app:ch_osc:lem:osc-amplitude`). -/
theorem contDiff_periodicLift_coordinateDeriv {f : Torus n → ℂ} {m : ℕ}
    (hf : ContDiff ℝ (m+1) (periodicLift f)) (i : Fin n) :
    ContDiff ℝ m (periodicLift (periodicCoordinateDeriv i f)) := by
  rw [periodicLift_coordinateDeriv_of_differentiable (hf.differentiable (by simp))]
  exact (hf.fderiv_right (by norm_cast)).clm_apply contDiff_const

/-- Ordered Euclidean derivatives retain the unused finite regularity
(`app:ch_osc:lem:osc-amplitude`). -/
theorem contDiff_euclideanCoordinateDerivList {f : E → ℂ} (is : List (Fin n))
    {m : ℕ} (hf : ContDiff ℝ (m+is.length) f) :
    ContDiff ℝ m (euclideanCoordinateDerivList is f) := by
  induction is generalizing m with
  | nil => simpa [euclideanCoordinateDerivList] using hf
  | cons i is ih =>
    have hg : ContDiff ℝ (m+1) (euclideanCoordinateDerivList is f) :=
      ih (by simpa [List.length_cons,add_assoc,add_left_comm,add_comm] using hf)
    exact (hg.fderiv_right (by norm_cast)).clm_apply contDiff_const

/-- Ordered periodic derivatives retain the unused finite regularity
(`app:ch_osc:lem:osc-amplitude`). -/
theorem contDiff_periodicLift_coordinateDerivList {f : Torus n → ℂ}
    (is : List (Fin n)) {m : ℕ} (hf : ContDiff ℝ (m+is.length) (periodicLift f)) :
    ContDiff ℝ m (periodicLift (periodicCoordinateDerivList is f)) := by
  induction is generalizing m with
  | nil => simpa [periodicCoordinateDerivList] using hf
  | cons i is ih =>
    apply contDiff_periodicLift_coordinateDeriv
    exact ih (by simpa [List.length_cons,add_assoc,add_left_comm,add_comm] using hf)

/-- The ordered periodic derivatives are continuous with only the indicated
finite regularity (`app:ch_osc:lem:osc-amplitude`). -/
theorem continuous_periodicCoordinateDerivList {f : Torus n → ℂ}
    (is : List (Fin n)) (hf : ContDiff ℝ is.length (periodicLift f)) :
    Continuous (periodicCoordinateDerivList is f) :=
  quotientMap.isQuotientMap.continuous_iff.mpr
    (contDiff_periodicLift_coordinateDerivList is (m := 0) (by simpa using hf)).continuous

/-- Coordinate translations have the usual derivative for a differentiable
periodic lift (`app:ch_osc:lem:osc-amplitude`). -/
theorem hasDerivAt_coordinate_of_differentiable {f : Torus n → ℂ}
    (hf : Differentiable ℝ (periodicLift f)) (i : Fin n) (x : Torus n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (x + Pi.single i (s : AddCircle (1 : ℝ))))
      (periodicCoordinateDeriv i f (x + Pi.single i (t : AddCircle (1 : ℝ)))) t := by
  classical
  obtain ⟨y,rfl⟩ := quotientMap.surjective x
  have hd := (hf (y + t • EuclideanSpace.single i 1)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ)) |>.const_add y)
  have heq (s : ℝ) : periodicLift f (y + s • EuclideanSpace.single i 1) =
      f (torusQuotient y + Pi.single i (s : AddCircle (1 : ℝ))) := by
    rw [periodicLift,Function.comp_apply,quotient_coordinateLine]
  have hder := congr_fun (periodicLift_coordinateDeriv_of_differentiable hf i)
    (y + t • EuclideanSpace.single i 1)
  change periodicCoordinateDeriv i f (torusQuotient (y + t • EuclideanSpace.single i 1)) = _ at hder
  rw [quotient_coordinateLine] at hder
  rw [hder]
  simpa only [Function.comp_def,id_eq,one_smul,heq] using hd

/-- Finite-order integration by parts for the actual complex Fourier coefficient.
This is shared by the summable-coefficient fallback and the sharp energy proof
of `app:ch_osc:lem:osc-amplitude`. -/
theorem mFourierCoeff_coordinateDerivList_of_finite {f : Torus n → ℂ}
    (is : List (Fin n)) (hf : ContDiff ℝ is.length (periodicLift f)) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (periodicCoordinateDerivList is f) k =
      (is.map (fun i ↦ 2 * Real.pi * Complex.I * (k i : ℂ))).prod *
        UnitAddTorus.mFourierCoeff f k := by
  induction is with
  | nil => simp [periodicCoordinateDerivList]
  | cons i is ih =>
    have hs : ContDiff ℝ 1 (periodicLift (periodicCoordinateDerivList is f)) :=
      contDiff_periodicLift_coordinateDerivList is
        (by simpa [List.length_cons,add_comm] using hf)
    have hcoeff := mFourierCoeff_of_hasDerivAt_coordinate
      (g := periodicCoordinateDeriv i (periodicCoordinateDerivList is f))
      (continuous_periodicCoordinateDerivList is (hf.of_le (by simp)))
      (by simpa only [periodicCoordinateDerivList] using
        continuous_periodicCoordinateDerivList (i :: is) hf) i
      (hasDerivAt_coordinate_of_differentiable (hs.differentiable (by norm_num)) i) k
    rw [periodicCoordinateDerivList,hcoeff,ih (hf.of_le (by simp))]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

/-- Ordered derivatives of a finitely differentiable periodic lift agree with
its ordinary Cartesian derivatives (`app:ch_osc:lem:osc-amplitude`). -/
theorem periodicLift_coordinateDerivList_eq_of_finite {f : Torus n → ℂ}
    (is : List (Fin n)) (hf : ContDiff ℝ is.length (periodicLift f)) :
    periodicLift (periodicCoordinateDerivList is f) =
      euclideanCoordinateDerivList is (periodicLift f) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have hs : ContDiff ℝ 1 (periodicLift (periodicCoordinateDerivList is f)) :=
      contDiff_periodicLift_coordinateDerivList is
        (by simpa [List.length_cons,add_comm] using hf)
    rw [periodicCoordinateDerivList,
      periodicLift_coordinateDeriv_of_differentiable (hs.differentiable (by norm_num)),
      ih (hf.of_le (by simp))]
    rfl

end JanetCartan.AmplitudeBound.FiniteLegacy
