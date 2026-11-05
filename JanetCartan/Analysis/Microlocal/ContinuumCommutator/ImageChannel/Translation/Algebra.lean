module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Exterior
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.RealCompression

/-!
# Translation algebra for the literal image normal

These product and adjoint identities are used for the finite factorization of
`ContinuumRow.imageChannel` in `app:ch_background:eq:bg-commutator`. In particular,
the normal is the original operator composed with its Hilbert adjoint.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannelTranslation

open ContinuumRow

variable {n : ℕ}

/-- Translation conjugation on the actual output Hilbert space, used for the
image factors in `app:ch_background:prop:bg-inverse`. -/
def conjugate (a : Torus n) (A : OutputL2 n →L[ℝ] OutputL2 n) :
    OutputL2 n →L[ℝ] OutputL2 n :=
  (periodicL2Translation a).toContinuousLinearMap ∘L A ∘L
    (periodicL2Translation (-a)).toContinuousLinearMap

/-- Conjugation preserves composition (`app:ch_background:eq:bg-commutator`). -/
theorem conjugate_comp (a : Torus n) (A B : OutputL2 n →L[ℝ] OutputL2 n) :
    conjugate a (A ∘L B) = conjugate a A ∘L conjugate a B := by
  ext1 u
  simp only [conjugate, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, ← periodicL2Translation_add,
    neg_add_cancel, periodicL2Translation_zero]

/-- Translation conjugation is contractive in operator norm
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_conjugate_le (a : Torus n) (A : OutputL2 n →L[ℝ] OutputL2 n) :
    ‖conjugate a A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖periodicL2Translation a (A (periodicL2Translation (-a) u))‖ ≤ _
  simpa only [norm_periodicL2Translation] using A.le_opNorm
    (periodicL2Translation (-a) u)

/-- The inverse translation is the literal Hilbert adjoint
(`app:ch_background:prop:bg-inverse`). -/
theorem translation_adjoint (a : Torus n) :
    (periodicL2Translation (F := Euclidean n) a).toContinuousLinearMap.adjoint =
      (periodicL2Translation (-a)).toContinuousLinearMap := by
  exact (periodicL2TranslationEquiv (F := Euclidean n) a).adjoint_eq_symm

/-- Conjugation commutes with the same Hilbert adjoint
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugate_adjoint (a : Torus n) (A : OutputL2 n →L[ℝ] OutputL2 n) :
    conjugate a A.adjoint = (conjugate a A).adjoint := by
  simp only [conjugate, ContinuousLinearMap.adjoint_comp, translation_adjoint,
    neg_neg, ContinuousLinearMap.comp_assoc]

/-- The divided product difference retains both literal factors
(`app:ch_background:eq:bg-commutator`). -/
theorem conjugationDifference_comp (A B : OutputL2 n →L[ℝ] OutputL2 n)
    (i : Fin n) (h : ℝ) :
    periodicConjugationDifference (A ∘L B) i h =
      periodicConjugationDifference A i h ∘L conjugate (periodicCoordinateShift i h) B +
        A ∘L periodicConjugationDifference B i h := by
  change h⁻¹ • (conjugate _ (A ∘L B) - A ∘L B) = _
  rw [conjugate_comp]
  change h⁻¹ • (conjugate _ A ∘L conjugate _ B - A ∘L B) =
    (h⁻¹ • (conjugate _ A - A)) ∘L conjugate _ B +
      A ∘L (h⁻¹ • (conjugate _ B - B))
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, smul_sub]
  abel

/-- The uniform product estimate used for cutoffs, coefficients and Bessel
factors (`app:ch_background:prop:bg-inverse`). -/
theorem norm_conjugationDifference_comp_le (A B : OutputL2 n →L[ℝ] OutputL2 n)
    (i : Fin n) (h : ℝ) :
    ‖periodicConjugationDifference (A ∘L B) i h‖ ≤
      ‖periodicConjugationDifference A i h‖ * ‖B‖ +
        ‖A‖ * ‖periodicConjugationDifference B i h‖ := by
  rw [conjugationDifference_comp]
  apply (norm_add_le _ _).trans
  exact add_le_add
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_conjugate_le _ _) (norm_nonneg _)))
    (ContinuousLinearMap.opNorm_comp_le _ _)

/-- Divided conjugation respects the literal adjoint, over the real Hilbert
space (`app:ch_background:eq:bg-commutator`). -/
theorem conjugationDifference_adjoint (A : OutputL2 n →L[ℝ] OutputL2 n)
    (i : Fin n) (h : ℝ) :
    periodicConjugationDifference A.adjoint i h =
      (periodicConjugationDifference A i h).adjoint := by
  change h⁻¹ • (conjugate _ A.adjoint - A.adjoint) =
    (h⁻¹ • (conjugate _ A - A)).adjoint
  rw [conjugate_adjoint]
  simp

/-- The normal commutator bound is deduced from the actual factor and its
adjoint, with no normal estimate assumed (`app:ch_background:eq:bg-commutator`). -/
theorem norm_conjugationDifference_normal_le (A : OutputL2 n →L[ℝ] OutputL2 n)
    (i : Fin n) (h : ℝ) :
    ‖periodicConjugationDifference (A ∘L A.adjoint) i h‖ ≤
      2 * ‖A‖ * ‖periodicConjugationDifference A i h‖ := by
  have hb := norm_conjugationDifference_comp_le A A.adjoint i h
  rw [conjugationDifference_adjoint, ContinuousLinearMap.adjoint.norm_map,
    ContinuousLinearMap.adjoint.norm_map] at hb
  convert hb using 1
  ring

end JanetCartan.ContinuumCommutator.ImageChannelTranslation
