module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers.SmoothBounds

/-!
# Jets of differentiated image coefficients

The coefficient derivatives in `app:ch_background:eq:bg-commutator` are the
actual coordinate derivatives. Their jet budgets cost exactly the word length,
for the parent's single-high estimate.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

variable {n : ℕ}

/-- The actual derivative coefficient, bundled only with its proved continuity
(`app:ch_background:eq:bg-commutator`). -/
def coordinateCoefficient (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q) (i : Fin n) :
    C(Torus n, ℝ) := ⟨periodicCoordinateDeriv i q, (hq.coordinateDeriv i).1⟩

/-- A coordinate derivative of a smooth coefficient is smooth
(`app:ch_background:eq:bg-commutator`). -/
theorem smooth_coordinateCoefficient (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (i : Fin n) : IsSmoothPeriodic (coordinateCoefficient q hq i) := hq.coordinateDeriv i

/-- Differentiated coefficients retain their literal ordered representatives
(`app:ch_background:eq:bg-commutator`). -/
def orderedCoefficient (q : C(Torus n, ℝ)) (hq : IsSmoothPeriodic q)
    (js : List (Fin n)) : C(Torus n, ℝ) :=
  ⟨periodicCoordinateDerivList js q, (hq.coordinateDerivList js).1⟩

/-- Each additional coordinate derivative costs one additional jet order
with constant one (`app:ch_background:eq:bg-commutator`). -/
theorem norm_iteratedFDeriv_coordinate_le (q : Torus n → ℝ) (hq : IsSmoothPeriodic q)
    (i : Fin n) (j : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ j (periodicLift (periodicCoordinateDeriv i q)) x‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) (periodicLift q) x‖ := by
  rw [periodicLift_coordinateDeriv hq.2]
  have hd : ContDiff ℝ ∞ (fderiv ℝ (periodicLift q)) := hq.2.fderiv_right (by simp)
  have h := norm_iteratedFDeriv_clm_apply_const hd.contDiffAt (n := j) (x := x)
    (c := EuclideanSpace.single i 1) (by simp)
  simpa only [norm_iteratedFDeriv_fderiv, EuclideanSpace.single, PiLp.norm_single,
    norm_one, one_mul] using h

/-- Ordered differentiation costs precisely the total number of derivatives;
this controls the jets of every coefficient in the normal's Leibniz branches
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_iteratedFDeriv_orderedCoefficient_le (q : Torus n → ℝ)
    (hq : IsSmoothPeriodic q) (js : List (Fin n)) (j : ℕ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ j (periodicLift (periodicCoordinateDerivList js q)) x‖ ≤
      ‖iteratedFDeriv ℝ (j + js.length) (periodicLift q) x‖ := by
  induction js generalizing j with
  | nil => simp [periodicCoordinateDerivList]
  | cons i js ih =>
    apply (norm_iteratedFDeriv_coordinate_le _ (hq.coordinateDerivList js) i j x).trans
    have he : j + (i :: js).length = (j + 1) + js.length := by
      simp only [List.length_cons]
      omega
    rw [he]
    exact ih (j + 1)

/-- Usable coefficient-jet bound for every ordered derivative: the constant
is independent of the coefficient and no additional analytic premise occurs
(`app:ch_background:eq:bg-commutator`). -/
theorem cNorm_periodicCoordinateDerivList_le (q : Torus n → ℝ)
    (hq : IsSmoothPeriodic q) (js : List (Fin n)) (j : ℕ) :
    cNorm (fundamentalCell n) j (periodicLift (periodicCoordinateDerivList js q)) ≤
      (j + 1) * cNorm (fundamentalCell n) (j + js.length) (periodicLift q) := by
  calc
    _ ≤ ∑ _k ∈ Finset.range (j + 1),
        cNorm (fundamentalCell n) (j + js.length) (periodicLift q) := by
      apply cNorm_le_sum_of_bounds (fun _ _ ↦ cNorm_nonneg _ _ _)
      intro k hk x hx
      exact (norm_iteratedFDeriv_orderedCoefficient_le q hq js k x).trans
        (norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
          (hq.2.of_le (by simp)) hx (Nat.add_le_add_right hk _))
    _ = _ := by simp

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
