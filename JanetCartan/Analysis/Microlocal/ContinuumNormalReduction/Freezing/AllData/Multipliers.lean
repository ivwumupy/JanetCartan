module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.Realization

/-!
# Physical localization multipliers for freezing

Actual bounded multiplication by a compactly supported physical cutoff and by
its coordinate products, consumed by the L² identity in
`app:ch_background:prop:bg-frame`, Step 3.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff NNReal
open JanetCartan.AmplitudeBound
namespace JanetCartan.ContinuumNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp (α := E) ℂ 2

/-- The bounded physical multiplier by a real compact cutoff in
`app:ch_background:prop:bg-frame`, Step 3. -/
def freezingPhysicalMultiplier (χ : E → ℝ) (hχ : Continuous χ)
    (hχs : HasCompactSupport χ) : L² →L[ℂ] L² :=
  multiplicationOperator
    (((hχ.smul continuous_const).memLp_of_hasCompactSupport
      (hχs.smul_right (f' := fun _ ↦ (1 : ℂ))) :
        MemLp (fun x ↦ χ x • (1 : ℂ)) ⊤).toLp _)

/-- The physical multiplier has its literal representative
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem freezingPhysicalMultiplier_coeFn (χ : E → ℝ) (hχ : Continuous χ)
    (hχs : HasCompactSupport χ) (f : L²) :
    freezingPhysicalMultiplier χ hχ hχs f =ᵐ[volume] fun x ↦ χ x • f x := by
  unfold freezingPhysicalMultiplier
  filter_upwards [multiplicationOperator_coeFn _ f, MemLp.coeFn_toLp
    (((hχ.smul continuous_const).memLp_of_hasCompactSupport
      (hχs.smul_right (f' := fun _ ↦ (1 : ℂ)))) :
        MemLp (fun x ↦ χ x • (1 : ℂ)) ⊤)] with x hx hχx
  rw [hx, hχx]
  change (χ x • (1 : ℂ)) * f x = χ x • f x
  rw [smul_mul_assoc, one_mul]

/-- Multiplication by `χ(x) xᵢ`, constructed from the fixed compact cutoff for
`app:ch_background:prop:bg-frame`, Step 3. -/
def freezingCoordinateMultiplier (χ : E → ℝ) (hχ : Continuous χ)
    (hχs : HasCompactSupport χ) (i : Fin d) : L² →L[ℂ] L² :=
  freezingPhysicalMultiplier (fun x ↦ χ x * x i)
    (hχ.mul (by fun_prop)) hχs.mul_right

/-- The coordinate multiplier has its literal representative
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem freezingCoordinateMultiplier_coeFn (χ : E → ℝ) (hχ : Continuous χ)
    (hχs : HasCompactSupport χ) (i : Fin d) (f : L²) :
    freezingCoordinateMultiplier χ hχ hχs i f =ᵐ[volume]
      fun x ↦ (χ x * x i) • f x :=
  freezingPhysicalMultiplier_coeFn ..

end JanetCartan.ContinuumNormal
