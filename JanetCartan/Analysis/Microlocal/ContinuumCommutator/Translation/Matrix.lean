module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.ScalarCommutator
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds

/-!
# Translation commutators on literal vector-valued Lebesgue L²

The matrix step of `app:ch_background:prop:bg-inverse`. Translation commutes
with the existing exact coordinate isometry. Thus the scalar full-amplitude
commutator supplies the vector bound, with no regularity premise on the input.
The remaining periodic chart transfer is a separate construction.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumCommutator

variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "P" => EuclideanSpace ℝ (Fin (2 * d))
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "VI" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)
local notation "VJ" => Lp (EuclideanSpace ℂ J) 2 (volume : Measure E)

/-- Positive translation on literal vector-valued Lebesgue L², used by the
matrix commutator in `app:ch_background:prop:bg-inverse`. -/
def euclideanVectorL2Translation (a : E) : VI →ₗᵢ[ℂ] VI :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x ↦ x + a) (measurePreserving_add_right volume a)

/-- Translation of actual vector representatives
(`app:ch_background:prop:bg-inverse`). -/
theorem euclideanVectorL2Translation_coe (a : E) (u : VI) :
    euclideanVectorL2Translation a u =ᵐ[volume] fun x ↦ u (x + a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume a)

/-- The shared coordinate isometry intertwines vector and scalar translation
(`app:ch_background:prop:bg-inverse`). -/
theorem finiteL2CoordinateIsometry_translation (a : E) (u : VI) (j : I) :
    finiteL2CoordinateIsometry volume (euclideanVectorL2Translation a u) j =
      euclideanL2Translation a (finiteL2CoordinateIsometry volume u j) := by
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae volume (euclideanVectorL2Translation a u) j,
    euclideanVectorL2Translation_coe a u,
    euclideanL2Translation_coe a (finiteL2CoordinateIsometry volume u j),
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae
      (finiteL2Coordinates_apply_ae volume u j)] with x hc ht hs hcs
  exact hc.trans ((congrArg (fun z : EuclideanSpace ℂ I ↦ z j) ht).trans
    (hs.trans hcs).symm)

/-- Inverse vector translation on all L² data
(`app:ch_background:prop:bg-inverse`). -/
theorem euclideanVectorL2Translation_neg_apply (a : E) (u : VI) :
    euclideanVectorL2Translation (-a) (euclideanVectorL2Translation a u) = u := by
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  intro j
  rw [finiteL2CoordinateIsometry_translation, finiteL2CoordinateIsometry_translation,
    euclideanL2Translation_neg_apply]

/-- Vector difference quotients are defined before any H¹ regularity is known
(`app:ch_background:prop:bg-inverse`). -/
def euclideanVectorL2DifferenceQuotient (i : Fin d) (h : ℝ) : VI →L[ℂ] VI :=
  h⁻¹ • ((euclideanVectorL2Translation (h • EuclideanSpace.single i 1)).toContinuousLinearMap -
    ContinuousLinearMap.id ℂ (VI))

/-- Divided vector conjugation, retaining both physical positions
(`app:ch_background:prop:bg-inverse`). -/
def euclideanVectorConjugationDifference (B : VJ →L[ℂ] VI) (i : Fin d) (h : ℝ) :
    VJ →L[ℂ] VI :=
  h⁻¹ • ((euclideanVectorL2Translation (h • EuclideanSpace.single i 1)).toContinuousLinearMap.comp
    (B.comp (euclideanVectorL2Translation (-(h • EuclideanSpace.single i 1))).toContinuousLinearMap) - B)

/-- Conjugation of a vector matrix acts entrywise on the actual scalar
operators (`app:ch_background:prop:bg-inverse`). -/
theorem euclideanVectorL2Translation_vectorMatrixL2Operator
    (B : I → J → L² →L[ℂ] L²) (a : E) (u : VJ) :
    euclideanVectorL2Translation a (vectorMatrixL2Operator B
      (euclideanVectorL2Translation (-a) u)) =
      vectorMatrixL2Operator (fun r s ↦ (euclideanL2Translation a).toContinuousLinearMap.comp
        ((B r s).comp (euclideanL2Translation (-a)).toContinuousLinearMap)) u := by
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  intro r
  simp only [finiteL2CoordinateIsometry_translation,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply,
    map_sum, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]

/-- Matrix conjugation is exactly entrywise scalar conjugation. In particular,
source translation is included in every entry (`app:ch_background:prop:bg-inverse`). -/
theorem euclideanVectorConjugationDifference_vectorMatrixL2Operator
    (B : I → J → L² →L[ℂ] L²) (i : Fin d) (h : ℝ) :
    euclideanVectorConjugationDifference (vectorMatrixL2Operator B) i h =
      vectorMatrixL2Operator (fun r s ↦ euclideanConjugationDifference (B r s) i h) := by
  ext1 u
  apply (finiteL2CoordinateIsometry volume).injective
  apply PiLp.ext
  intro r
  change (finiteL2CoordinateIsometry volume
    (h⁻¹ • (euclideanVectorL2Translation (h • EuclideanSpace.single i 1)
      (vectorMatrixL2Operator B (euclideanVectorL2Translation
        (-(h • EuclideanSpace.single i 1)) u)) - vectorMatrixL2Operator B u))) r = _
  rw [LinearMapClass.map_smul_of_tower, map_sub]
  simp only [PiLp.smul_apply, PiLp.sub_apply, finiteL2CoordinateIsometry_translation,
    finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply,
    map_sum, euclideanConjugationDifference, smul_apply,
    sub_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]

/-- The existing Hilbert matrix estimate transfers without norm-equivalence
loss to literal vector L² (`app:ch_background:prop:bg-inverse`). -/
theorem norm_vectorMatrixL2Operator_le_of_entry_bound
    (B : I → J → L² →L[ℂ] L²) (C : ℝ) (hB : ∀ r s, ‖B r s‖ ≤ C) :
    ‖vectorMatrixL2Operator B‖ ≤ (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C := by
  have hb := norm_matrixOperator_le_of_entry_bound B C hB
  apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans hb)
  intro u
  rw [← (finiteL2CoordinateIsometry volume).norm_map (vectorMatrixL2Operator B u),
    finiteL2CoordinateIsometry_vectorMatrixL2Operator]
  exact ((matrixOperator B).le_opNorm _).trans (by
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg u))

/-- Factoring the vector commutator leaves an isometric input translation
(`app:ch_background:prop:bg-inverse`). -/
theorem euclideanVectorL2DifferenceQuotient_commutator
    (B : VJ →L[ℂ] VI) (i : Fin d) (h : ℝ) (u : VJ) :
    euclideanVectorL2DifferenceQuotient i h (B u) -
      B (euclideanVectorL2DifferenceQuotient i h u) =
      euclideanVectorConjugationDifference B i h
        (euclideanVectorL2Translation (h • EuclideanSpace.single i 1) u) := by
  change h⁻¹ • (euclideanVectorL2Translation (h • EuclideanSpace.single i 1) (B u) - B u) -
    B (h⁻¹ • (euclideanVectorL2Translation (h • EuclideanSpace.single i 1) u - u)) =
      h⁻¹ • (euclideanVectorL2Translation (h • EuclideanSpace.single i 1)
        (B (euclideanVectorL2Translation (-(h • EuclideanSpace.single i 1))
          (euclideanVectorL2Translation (h • EuclideanSpace.single i 1) u))) -
        B (euclideanVectorL2Translation (h • EuclideanSpace.single i 1) u))
  rw [euclideanVectorL2Translation_neg_apply, B.map_smul_of_tower, map_sub]
  module

/-- Exact vector PDO conjugation: both physical positions translate with
positive sign, as determined by the scalar Lebesgue kernel calculation
(`app:ch_background:prop:bg-inverse`). -/
theorem vectorTwoPositionL2Operator_conjugate
    (hd : 0 < d) (R h₀ : ℝ) (b : E → P → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
    (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s) (2 * (d + 1)) A)
    (i : Fin d) (h : ℝ) (hsmall : |h| ≤ h₀) (u : VJ) :
    euclideanVectorL2Translation (h • EuclideanSpace.single i 1)
      (vectorTwoPositionL2Operator hd R b hb hs A hA
        (euclideanVectorL2Translation (-(h • EuclideanSpace.single i 1)) u)) =
      vectorMatrixL2Operator (fun r s ↦ twoPositionL2Operator hd (R + h₀)
        (translatedAmplitude (fun ξ z ↦ b ξ z r s) i h)
        (contDiff_uncurry_translatedAmplitude (fun ξ z ↦ b ξ z r s) ((matrixEntryEvaluation r s).contDiff.comp hb) i h)
        (supportedInCenteredBox_translatedAmplitude (fun ξ z ↦ b ξ z r s) R h₀ (fun ξ ↦ hs ξ r s) i h hsmall)
        A (hasAmplitudeDerivativeBound_translatedAmplitude (fun ξ z ↦ b ξ z r s) i _ A (hA r s) h)) u := by
  rw [vectorTwoPositionL2Operator, euclideanVectorL2Translation_vectorMatrixL2Operator]
  congr 2
  funext r s
  apply ContinuousLinearMap.ext
  intro v
  exact twoPositionL2Operator_conjugate hd R h₀ (fun ξ z ↦ b ξ z r s)
    ((matrixEntryEvaluation r s).contDiff.comp hb) (fun ξ ↦ hs ξ r s) A (hA r s) i h hsmall v

/-- Exact divided full-amplitude representation of the vector PDO conjugation
(`app:ch_background:prop:bg-inverse`). The primitive budget on each entry is
obtained from a Frobenius budget by `matrixAmplitude_entry_bound`. -/
theorem euclideanVectorConjugationDifference_twoPosition_eq
  (hd : 0 < d) (R h₀ : ℝ) (b : E → P → Matrix I J ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
  (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s) (2 * (d + 1) + 1) A)
  (i : Fin d) (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) :
    euclideanVectorConjugationDifference
      (vectorTwoPositionL2Operator hd R b hb hs A
        (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his))) i h =
      vectorMatrixL2Operator (fun r s ↦ translationDifferenceL2Operator hd R h₀
        (fun ξ z ↦ b ξ z r s) ((matrixEntryEvaluation r s).contDiff.comp hb)
        (fun ξ ↦ hs ξ r s) A (hA r s) i h hh hsmall) := by
  unfold vectorTwoPositionL2Operator
  rw [euclideanVectorConjugationDifference_vectorMatrixL2Operator]
  congr 1
  funext r s
  exact (translationDifferenceL2Operator_eq_conjugationDifference hd R h₀
    (fun ξ z ↦ b ξ z r s) ((matrixEntryEvaluation r s).contDiff.comp hb)
    (fun ξ ↦ hs ξ r s) A (hA r s) i h hh hsmall).symm

/-- Uniform vector PDO conjugation bound from primitive first physical
derivatives and the fixed enlarged box (`app:ch_background:prop:bg-inverse`). -/
theorem norm_euclideanVectorConjugationDifference_twoPosition_le
  (hd : 0 < d) (R h₀ : ℝ) (b : E → P → Matrix I J ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
  (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s) (2 * (d + 1) + 1) A)
  (i : Fin d) (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) :
    ‖euclideanVectorConjugationDifference
      (vectorTwoPositionL2Operator hd R b hb hs A
        (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his))) i h‖ ≤
      (Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
        (fixedBoxAmplitudeConstant d (R + h₀) * (2 * A)) := by
  rw [euclideanVectorConjugationDifference_twoPosition_eq hd R h₀ b hb hs A hA i h hh hsmall]
  exact norm_vectorMatrixL2Operator_le_of_entry_bound _ _
    (fun r s ↦ norm_translationDifferenceL2Operator_le hd R h₀
      (fun ξ z ↦ b ξ z r s) ((matrixEntryEvaluation r s).contDiff.comp hb)
      (fun ξ ↦ hs ξ r s) A (hA r s) i h hh hsmall)

/-- The uniform difference-quotient commutator estimate on actual vector L²,
with all scalar analytic premises discharged (`app:ch_background:prop:bg-inverse`). -/
theorem norm_euclideanVectorL2DifferenceQuotient_twoPosition_commutator_le
  (hd : 0 < d) (R h₀ : ℝ) (b : E → P → Matrix I J ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
  (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s) (2 * (d + 1) + 1) A)
  (i : Fin d) (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) (u : VJ) :
    let B := vectorTwoPositionL2Operator hd R b hb hs A
      (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his))
    ‖euclideanVectorL2DifferenceQuotient i h (B u) -
      B (euclideanVectorL2DifferenceQuotient i h u)‖ ≤
      ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
        (fixedBoxAmplitudeConstant d (R + h₀) * (2 * A))) * ‖u‖ := by
  dsimp only
  rw [euclideanVectorL2DifferenceQuotient_commutator]
  exact ((euclideanVectorConjugationDifference _ i h).le_opNorm _).trans (by
    rw [LinearIsometry.norm_map]
    exact mul_le_mul_of_nonneg_right
      (norm_euclideanVectorConjugationDifference_twoPosition_le hd R h₀ b hb hs A hA
        i h hh hsmall) (norm_nonneg u))

/-- The form used before the coercive inverse estimate: the unknown datum
need only be in L² (`app:ch_background:prop:bg-inverse`). -/
theorem norm_euclideanVector_twoPosition_differenceQuotient_le
  (hd : 0 < d) (R h₀ : ℝ) (b : E → P → Matrix I J ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ r s, SupportedInCenteredBox R (fun z ↦ b ξ z r s)) (A : ℝ)
  (hA : ∀ r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z r s) (2 * (d + 1) + 1) A)
  (i : Fin d) (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) (u : VJ) :
    let B := vectorTwoPositionL2Operator hd R b hb hs A
      (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his))
    ‖B (euclideanVectorL2DifferenceQuotient i h u)‖ ≤
      ‖euclideanVectorL2DifferenceQuotient i h (B u)‖ +
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
          (fixedBoxAmplitudeConstant d (R + h₀) * (2 * A))) * ‖u‖ := by
  dsimp only
  have he := norm_euclideanVectorL2DifferenceQuotient_twoPosition_commutator_le
    hd R h₀ b hb hs A hA i h hh hsmall u
  let B := vectorTwoPositionL2Operator hd R b hb hs A
    (fun r s ξ is his ↦ hA r s ξ is (Nat.le_succ_of_le his))
  have hid : B (euclideanVectorL2DifferenceQuotient i h u) =
      euclideanVectorL2DifferenceQuotient i h (B u) -
        (euclideanVectorL2DifferenceQuotient i h (B u) -
          B (euclideanVectorL2DifferenceQuotient i h u)) := by abel
  change ‖B (euclideanVectorL2DifferenceQuotient i h u)‖ ≤ _
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _) he)

end JanetCartan.ContinuumCommutator
