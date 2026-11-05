module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.PeriodicAlgebra
public import JanetCartan.Analysis.Operator.RealQuadratures
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces

/-!
# Real compression of periodic translation commutators

For `app:ch_background:prop:bg-inverse`, positive translations on normalized
torus volume commute with the real-part and inclusion maps on the actual
`ContinuumRow.OutputL2` space. Consequently real output compression does not
increase the norm of the divided conjugation difference of an arbitrary bounded
complex-linear output operator; no reality-preservation hypothesis is needed.

The consumer is the parent's matrix-plus-exterior estimate for `E δₕ v`, obtained
from `norm_periodic_operator_differenceQuotient_le`. The algebra below combines
its finite matrix summands and retains the real carrier normal's factor four
from `app:ch_background:eq:bg-realification`. The complex PDO bound is supplied
separately by chart transfer, and the exterior bound by `Translation.Exterior`.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumCommutator

variable {n : ℕ}

/-- Positive translation commutes with real part on normalized torus L²
(`app:ch_background:prop:bg-inverse`, `app:ch_background:eq:bg-realification`). -/
@[simp] theorem periodicL2Translation_l2RealPart (a : Torus n) (v : ComplexOutputL2 n) :
    periodicL2Translation a (l2RealPart volume v) =
      l2RealPart volume (periodicL2Translation a v) := by
  apply Lp.ext
  filter_upwards [periodicL2Translation_coe a (l2RealPart volume v),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
      ((euclideanRealPart (ι := Fin n)).coeFn_compLpL v),
    (euclideanRealPart (ι := Fin n)).coeFn_compLpL (periodicL2Translation a v),
    periodicL2Translation_coe a v] with x ht hr hs hv
  change periodicL2Translation a (l2RealPart volume v) x =
    (euclideanRealPart.compLpL 2 volume) (periodicL2Translation a v) x
  rw [ht, l2RealPart, hr, hs, hv]

/-- Positive translation commutes with inclusion of the actual real output
(`app:ch_background:prop:bg-inverse`, `app:ch_background:eq:bg-realification`). -/
@[simp] theorem periodicL2Translation_l2ComplexInclusion (a : Torus n) (v : OutputL2 n) :
    periodicL2Translation a (l2ComplexInclusion volume v) =
      l2ComplexInclusion volume (periodicL2Translation a v) := by
  apply Lp.ext
  filter_upwards [periodicL2Translation_coe a (l2ComplexInclusion volume v),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
      ((euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL v),
    (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL (periodicL2Translation a v),
    periodicL2Translation_coe a v] with x ht hr hs hv
  change periodicL2Translation a (l2ComplexInclusion volume v) x =
    (euclideanComplexInclusion.compLpL 2 volume) (periodicL2Translation a v) x
  rw [ht, l2ComplexInclusion, hr, hs, hv]

/-- The divided conjugation difference of real output compression is exactly
real part composed with the complex-output difference (regarded as real) and
real inclusion. This transfers the matrix summands in
`app:ch_background:prop:bg-inverse` without a reality-preservation assumption. -/
theorem periodicConjugationDifference_realOutputCompression
    (T : ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n) (i : Fin n) (h : ℝ) :
    periodicConjugationDifference (realOutputCompression T) i h =
      l2RealPart volume ∘L periodicConjugationDifference (T.restrictScalars ℝ) i h ∘L
        l2ComplexInclusion volume := by
  ext1 v
  simp only [periodicConjugationDifference, realOutputCompression,
    smul_apply, sub_apply,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    map_smul, map_sub, periodicL2Translation_l2RealPart,
    periodicL2Translation_l2ComplexInclusion]

/-- Real output compression loses no constant in the translation commutator
bound used in `app:ch_background:prop:bg-inverse`. This is a norm transfer, not
an assertion of a uniform complex PDO bound. -/
theorem norm_periodicConjugationDifference_realOutputCompression_le
    (T : ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n) (i : Fin n) (h : ℝ) :
    ‖periodicConjugationDifference (realOutputCompression T) i h‖ ≤
      ‖periodicConjugationDifference (T.restrictScalars ℝ) i h‖ := by
  rw [periodicConjugationDifference_realOutputCompression]
  calc
    _ ≤ ‖l2RealPart (ι := Fin n) (volume : Measure (Torus n))‖ *
        ‖periodicConjugationDifference (T.restrictScalars ℝ) i h ∘L
          l2ComplexInclusion volume‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖periodicConjugationDifference (T.restrictScalars ℝ) i h‖ *
        ‖l2ComplexInclusion (ι := Fin n) (volume : Measure (Torus n))‖) :=
      mul_le_mul (l2RealPart_norm_le volume) (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _) zero_le_one
    _ ≤ 1 * (‖periodicConjugationDifference (T.restrictScalars ℝ) i h‖ * 1) := by
      gcongr
      exact l2ComplexInclusion_norm_le volume
    _ = _ := by ring

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The zero summand contributes no translation commutator
(`app:ch_background:prop:bg-inverse`). -/
@[simp] theorem periodicConjugationDifference_zero (i : Fin n) (h : ℝ) :
    periodicConjugationDifference (0 : PeriodicL2 n F →L[ℝ] PeriodicL2 n F) i h = 0 := by
  simp [periodicConjugationDifference]

/-- Exact addition of the matrix and exterior translation commutators in
`app:ch_background:prop:bg-inverse`. -/
theorem periodicConjugationDifference_add
    (A B : PeriodicL2 n F →L[ℝ] PeriodicL2 n F) (i : Fin n) (h : ℝ) :
    periodicConjugationDifference (A + B) i h =
      periodicConjugationDifference A i h + periodicConjugationDifference B i h := by
  simp only [periodicConjugationDifference, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add]
  module

/-- Real scalar factors pass unchanged through the divided conjugation
difference, including the factor four in `app:ch_background:eq:bg-realification`.
This is used in the matrix-plus-exterior estimate of
`app:ch_background:prop:bg-inverse`. -/
theorem periodicConjugationDifference_smul
    (c : ℝ) (A : PeriodicL2 n F →L[ℝ] PeriodicL2 n F) (i : Fin n) (h : ℝ) :
    periodicConjugationDifference (c • A) i h = c • periodicConjugationDifference A i h := by
  ext1 v
  simp only [periodicConjugationDifference, smul_apply, sub_apply,
    ContinuousLinearMap.comp_apply, map_smul]
  module

/-- Finite sums of matrix summands commute with the divided conjugation
difference (`app:ch_background:prop:bg-inverse`). -/
theorem periodicConjugationDifference_sum {κ : Type*} (s : Finset κ)
    (A : κ → PeriodicL2 n F →L[ℝ] PeriodicL2 n F) (i : Fin n) (h : ℝ) :
    periodicConjugationDifference (∑ k ∈ s, A k) i h =
      ∑ k ∈ s, periodicConjugationDifference (A k) i h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [periodicConjugationDifference_zero]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk, periodicConjugationDifference_add, ih]

/-- The actual real carrier normal retains precisely the factor four from
`app:ch_background:eq:bg-realification` when transferring the complex-output
translation bound to `app:ch_background:prop:bg-inverse`. -/
theorem norm_periodicConjugationDifference_four_realOutputCompression_le
    (T : ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n) (i : Fin n) (h : ℝ) :
    ‖periodicConjugationDifference ((4 : ℝ) • realOutputCompression T) i h‖ ≤
      4 * ‖periodicConjugationDifference (T.restrictScalars ℝ) i h‖ := by
  rw [periodicConjugationDifference_smul, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 4 by positivity)]
  exact mul_le_mul_of_nonneg_left
    (norm_periodicConjugationDifference_realOutputCompression_le T i h) (by positivity)

end JanetCartan.ContinuumCommutator
