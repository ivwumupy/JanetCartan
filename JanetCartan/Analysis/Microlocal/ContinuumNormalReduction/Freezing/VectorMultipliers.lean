module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.AllData.Multipliers
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector

/-!
# Physical multipliers on vector L²

Literal multiplication by the fixed physical cutoffs used in the matrix freezing
identity of `app:ch_background:prop:bg-frame`, Step 3. The measure is Euclidean
Lebesgue measure throughout.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
namespace JanetCartan.ContinuumNormal
variable {d : ℕ} {I : Type} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "H" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)

/-- Multiplication by a fixed compact cutoff on actual vector L², for
`app:ch_background:prop:bg-frame`, Step 3. -/
def freezingVectorPhysicalMultiplier (χ : E → ℝ) (hχ : Continuous χ)
    (hχs : HasCompactSupport χ) : H →L[ℂ] H := by
  classical
  exact vectorMatrixL2Operator (fun j k ↦ if j = k then
    freezingPhysicalMultiplier χ hχ hχs else 0)

/-- Exact coordinate formula for the localization in
`app:ch_background:prop:bg-frame`, Step 3. -/
theorem finiteL2CoordinateIsometry_freezingVectorPhysicalMultiplier
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) (f : H) (j : I) :
    finiteL2CoordinateIsometry volume (freezingVectorPhysicalMultiplier χ hχ hχs f) j =
      freezingPhysicalMultiplier χ hχ hχs (finiteL2CoordinateIsometry volume f j) := by
  classical
  simp only [freezingVectorPhysicalMultiplier,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

/-- The localization is literal multiplication, as required by
`app:ch_background:prop:bg-frame`, Step 3. -/
theorem freezingVectorPhysicalMultiplier_coeFn
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) (f : H) :
    freezingVectorPhysicalMultiplier χ hχ hχs f =ᵐ[volume] fun x ↦ χ x • f x := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro j
  rw [finiteL2CoordinateIsometry_freezingVectorPhysicalMultiplier]
  filter_upwards [freezingPhysicalMultiplier_coeFn χ hχ hχs
    (finiteL2CoordinateIsometry volume f j), finiteL2Coordinates_apply_ae volume f j]
    with x hx hj
  change finiteL2CoordinateIsometry volume f j x = f x j at hj
  simpa only [PiLp.smul_apply, hj] using hx

/-- The fixed bounded coordinate localization in
`app:ch_background:prop:bg-frame`, Step 3. -/
def freezingVectorCoordinateMultiplier (χ : E → ℝ) (hχ : Continuous χ)
    (hχs : HasCompactSupport χ) (i : Fin d) : H →L[ℂ] H :=
  freezingVectorPhysicalMultiplier (fun x ↦ χ x * x i)
    (hχ.mul (by fun_prop)) hχs.mul_right

/-- Coordinate formula for the bounded coordinate localization in
`app:ch_background:prop:bg-frame`, Step 3. -/
theorem finiteL2CoordinateIsometry_freezingVectorCoordinateMultiplier
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) (i : Fin d)
    (f : H) (j : I) :
    finiteL2CoordinateIsometry volume (freezingVectorCoordinateMultiplier χ hχ hχs i f) j =
      freezingCoordinateMultiplier χ hχ hχs i (finiteL2CoordinateIsometry volume f j) :=
  finiteL2CoordinateIsometry_freezingVectorPhysicalMultiplier ..

/-- Literal representative of the coordinate localization in
`app:ch_background:prop:bg-frame`, Step 3. -/
theorem freezingVectorCoordinateMultiplier_coeFn
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) (i : Fin d) (f : H) :
    freezingVectorCoordinateMultiplier χ hχ hχs i f =ᵐ[volume]
      fun x ↦ (χ x * x i) • f x :=
  freezingVectorPhysicalMultiplier_coeFn ..

/-- Real physical multiplication is self-adjoint on the underlying real
Hilbert space used by `ContinuumNormal.LocalEstimate`
(`app:ch_background:prop:bg-frame`, Step 3). -/
theorem isSelfAdjoint_freezingVectorPhysicalMultiplier_real
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) :
    IsSelfAdjoint ((freezingVectorPhysicalMultiplier (I := I) χ hχ hχs).restrictScalars ℝ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℝ (freezingVectorPhysicalMultiplier χ hχ hχs f) g =
    inner ℝ f (freezingVectorPhysicalMultiplier χ hχ hχs g)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [freezingVectorPhysicalMultiplier_coeFn χ hχ hχs f,
    freezingVectorPhysicalMultiplier_coeFn χ hχ hχs g] with x hf hg
  rw [hf, hg, real_inner_smul_left, real_inner_smul_right]

/-- Self-adjointness of the bounded coordinate localization, for the existing
error absorption lemma (`app:ch_background:prop:bg-frame`, Step 3). -/
theorem isSelfAdjoint_freezingVectorCoordinateMultiplier_real
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) (i : Fin d) :
    IsSelfAdjoint ((freezingVectorCoordinateMultiplier (I := I) χ hχ hχs i).restrictScalars ℝ) :=
  isSelfAdjoint_freezingVectorPhysicalMultiplier_real ..

/-- A fixed plateau acts as the identity on supported data, for
`app:ch_background:prop:bg-frame`, Step 3. -/
theorem freezingVectorPhysicalMultiplier_eq_self_of_support
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (s : Set E) (hplateau : ∀ x ∈ s, χ x = 1) (f : H)
    (hf : ∀ᵐ x ∂volume, x ∉ s → f x = 0) :
    freezingVectorPhysicalMultiplier χ hχ hχs f = f := by
  apply Lp.ext
  filter_upwards [freezingVectorPhysicalMultiplier_coeFn χ hχ hχs f, hf] with x hx hf
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [hplateau x hxs, one_smul]
  · rw [hf hxs, smul_zero]

/-- The physical small-support coordinate estimate consumed by
`ContinuumNormal.LocalEstimate` (`app:ch_background:prop:bg-frame`, Step 3).
The cutoff is fixed; only the support of the datum depends on `r`. -/
theorem norm_freezingVectorCoordinateMultiplier_apply_le
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    {r : ℝ} (hplateau : ∀ x ∈ Metric.closedBall (0 : E) r, χ x = 1)
    (f : H) (hf : ∀ᵐ x ∂volume, x ∉ Metric.closedBall (0 : E) r → f x = 0)
    (i : Fin d) :
    ‖freezingVectorCoordinateMultiplier χ hχ hχs i f‖ ≤ r * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [freezingVectorCoordinateMultiplier_coeFn χ hχ hχs i f, hf]
    with x hx hf
  rw [hx]
  by_cases hxs : x ∈ Metric.closedBall (0 : E) r
  · rw [hplateau x hxs, one_mul, norm_smul]
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le x i).trans
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxs)) (norm_nonneg _)
  · simp [hf hxs]

end JanetCartan.ContinuumNormal
