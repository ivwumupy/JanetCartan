module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealVector.Coordinates
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Identities

/-!
# Real coordinate compatibility of the actual cell maps

The lift and restriction in `app:ch_background:defn:bg-row` commute with
complexification of coordinates. Torus volume and Euclidean Lebesgue measure
remain distinct, connected by the existing measure-preserving cell maps.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open JanetCartan.PeriodicLocalL2 JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

variable {n : ℕ} {I : Type*} [Fintype I]

/-- Restriction of real vector data commutes with taking complex coordinates
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexifiedL2Coordinate_toTorus
    (u : EuclideanL2 n (EuclideanSpace ℝ I)) (i : I) :
    complexifiedL2Coordinate volume i (toTorus (𝕜 := ℝ) u) =
      toTorus (𝕜 := ℂ) (complexifiedL2Coordinate volume i u) := by
  apply Lp.ext
  filter_upwards [complexifiedL2Coordinate_coe volume i (toTorus (𝕜 := ℝ) u),
    toTorus_coe (𝕜 := ℝ) u,
    toTorus_coe (𝕜 := ℂ) (complexifiedL2Coordinate volume i u),
    measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
      (complexifiedL2Coordinate_coe volume i u).restrict] with z h₁ h₂ h₃ h₄
  exact h₁.trans ((congrArg (fun v : EuclideanSpace ℝ I ↦ (v i : ℂ)) h₂).trans
    (h₃.trans h₄).symm)

/-- Zero extension of real torus data commutes with complex coordinates;
the asserted equality is on Euclidean Lebesgue L²
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexifiedL2Coordinate_toEuclidean
    (u : PeriodicL2 n (EuclideanSpace ℝ I)) (i : I) :
    complexifiedL2Coordinate volume i (toEuclidean (𝕜 := ℝ) u) =
      toEuclidean (𝕜 := ℂ) (complexifiedL2Coordinate volume i u) := by
  apply Lp.ext
  have hu := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp
      (complexifiedL2Coordinate_coe volume i u))
  filter_upwards [complexifiedL2Coordinate_coe volume i (toEuclidean (𝕜 := ℝ) u),
    toEuclidean_coe (𝕜 := ℝ) u,
    toEuclidean_coe (𝕜 := ℂ) (complexifiedL2Coordinate volume i u), hu]
    with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃]
  by_cases hx : x ∈ halfOpenCell n
  · simpa only [indicator_of_mem hx, periodicLift, Function.comp_apply] using (h₄ hx).symm
  · simp only [indicator_of_notMem hx, PiLp.zero_apply, Complex.ofReal_zero]

end JanetCartan.ContinuumNormalReduction.ImageNormal
