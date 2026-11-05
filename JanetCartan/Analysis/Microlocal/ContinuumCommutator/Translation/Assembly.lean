module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Chart
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.RealCompression
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Translation.Exterior
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.DifferenceQuotient.Forward

/-!
# The real periodic matrix-plus-exterior translation estimate

For `app:ch_background:prop:bg-inverse`, assemble the full two-position PDOs on
the actual real `ContinuumRow.OutputL2` space. The coefficients allow the image
weight one and the carrier weight four from `app:ch_background:eq:bg-realification`.
The exterior normal is multiplication by `χ²` (take `χ = 1 - ψ`).

The normal-reduction producer must supply the literal operator representation,
joint smoothness, compact support in a buffered chart, and the primitive entry
budgets of order `2 * (d + 1) + 1`. The fixed cutoff supplies its value and first
derivative budgets. All commutator bounds are deduced here from those inputs;
none is an input. In particular no H¹ regularity of the unknown `v` is used.
The elliptic-bootstrap consumer retains coercivity and the difference-quotient
converse, as well as instantiation of the geometric normal representation.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
open JanetCartan.AmplitudeBound JanetCartan.Pseudodifferential
open JanetCartan.PeriodicLocalL2 JanetCartan.ContinuumRow

namespace JanetCartan.ContinuumCommutator

variable {d : ℕ} {κ : Type*} [Fintype κ]

variable (hd : 0 < d) (R h₀ : ℝ)
  (b : κ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) →
    Matrix (Fin d) (Fin d) ℂ)
  (hb : ∀ a, ContDiff ℝ ∞ (Function.uncurry (b a)))
  (hs : ∀ a ξ r s, SupportedInCenteredBox R (fun z ↦ b a ξ z r s))
  (A : κ → ℝ)
  (hA : ∀ a r s, HasAmplitudeDerivativeBound (fun ξ z ↦ b a ξ z r s)
    (2 * (d + 1) + 1) (A a))
  (hbuffer : R + h₀ < 1 / 2) (c : κ → ℝ) (χ : C(Torus d, ℝ))

local notation "B" => fun a : κ ↦ transferOperator
  (vectorTwoPositionL2Operator hd R (b a) (hb a) (hs a) (A a)
    (fun r s ξ is his ↦ hA a r s ξ is (Nat.le_succ_of_le his)))
local notation "N" => (∑ a, c a • realOutputCompression (B a)) + cutoffMultiplier (χ ^ 2)
local notation "Cpdo" => ∑ a, |c a| *
  ((d : ℝ) ^ 2 * (fixedBoxAmplitudeConstant d (R + h₀) * (2 * A a)))

include hbuffer

/-- Exact divided conjugation of the real finite matrix sum and exterior normal.
Each entry on the right is the PDO of `translationDifferenceAmplitude`, whose
FTC formula shifts both positions positively. The chart boundary and support
identities are discharged by `periodicConjugationDifference_transfer_twoPosition_eq`
(`app:ch_background:prop:bg-inverse`). -/
theorem periodicConjugationDifference_matrixSum_exterior_eq
    (i : Fin d) (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) :
    periodicConjugationDifference N i h =
      (∑ a, c a • (l2RealPart volume ∘L
        (transferOperator (vectorMatrixL2Operator (fun r s ↦
          translationDifferenceL2Operator hd R h₀ (fun ξ z ↦ b a ξ z r s)
            ((matrixEntryEvaluation r s).contDiff.comp (hb a)) (fun ξ ↦ hs a ξ r s)
            (A a) (hA a r s) i h hh hsmall))).restrictScalars ℝ ∘L
          l2ComplexInclusion volume)) +
        cutoffMultiplier (exteriorCutoffDifferenceQuotient (χ ^ 2) i h) := by
  rw [periodicConjugationDifference_add, periodicConjugationDifference_sum,
    periodicConjugationDifference_cutoffMultiplier]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [periodicConjugationDifference_smul,
    periodicConjugationDifference_realOutputCompression,
    periodicConjugationDifference_transfer_twoPosition_eq hd R h₀ (b a) (hb a)
      (hs a) (A a) (hA a) hbuffer i h hh hsmall]

variable (hχ : Differentiable ℝ (periodicLift χ)) (i : Fin d) (M K : ℝ)
  (hM0 : 0 ≤ M) (hK0 : 0 ≤ K) (hM : ∀ x, ‖χ x‖ ≤ M)
  (hK : ∀ x, ‖fderiv ℝ (periodicLift χ) x (EuclideanSpace.single i 1)‖ ≤ K)

include hχ hM0 hK0 hM hK

/-- Uniform L² operator bound for the real finite matrix sum plus the fixed
exterior normal. The constant depends only on the fixed enlarged box, primitive
entry budgets and cutoff budgets, and is independent of `h`. In particular a
carrier coefficient `c a = 4` contributes exactly four times its matrix bound
(`app:ch_background:prop:bg-inverse`, `app:ch_background:eq:bg-realification`). -/
theorem norm_periodicConjugationDifference_matrixSum_exterior_le
    (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) :
    ‖periodicConjugationDifference (F := EuclideanSpace ℝ (Fin d)) N i h‖ ≤ Cpdo + 2 * M * K := by
  rw [periodicConjugationDifference_add, periodicConjugationDifference_sum]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    rw [periodicConjugationDifference_smul, norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply (norm_periodicConjugationDifference_realOutputCompression_le (B a) i h).trans
    simpa only [Fintype.card_fin] using
      norm_periodicConjugationDifference_transfer_twoPosition_le hd R h₀ (b a) (hb a)
        (hs a) (A a) (hA a) hbuffer i h hh hsmall
  · exact norm_periodicConjugationDifference_cutoff_sq_le χ hχ i hM0 hK0 hM hK h

variable (E : OutputL2 d →L[ℝ] OutputL2 d)
  (hE : E = (∑ a, c a • realOutputCompression (transferOperator
    (vectorTwoPositionL2Operator hd R (b a) (hb a) (hs a) (A a)
      (fun r s ξ is his ↦ hA a r s ξ is (Nat.le_succ_of_le his))))) +
        cutoffMultiplier (χ ^ 2))

include hE

/-- The literal difference-quotient commutator of a represented continuum normal
is uniformly bounded on every L² input, before inverse regularity is known.
The sole operator hypothesis is its full-amplitude representation, supplied by
normal reduction (`app:ch_background:prop:bg-inverse`). -/
theorem norm_periodicL2DifferenceQuotient_commutator_of_matrix_representation_le
    (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) (v : OutputL2 d) :
    ‖periodicL2DifferenceQuotient i h (E v) - E (periodicL2DifferenceQuotient i h v)‖ ≤
      (Cpdo + 2 * M * K) * ‖v‖ := by
  rw [periodicL2DifferenceQuotient_commutator]
  apply ((periodicConjugationDifference E i h).le_opNorm _).trans
  rw [norm_periodicL2Translation]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  rw [hE]
  exact norm_periodicConjugationDifference_matrixSum_exterior_le hd R h₀ b hb hs A hA
    hbuffer c χ hχ i M K hM0 hK0 hM hK h hh hsmall

/-- The estimate fed to the coercive L² inverse in
`app:ch_background:prop:bg-inverse`. It differentiates `E v` by a bounded
difference quotient and requires only L² membership of `v`. -/
theorem norm_periodic_operator_differenceQuotient_of_matrix_representation_le
    (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) (v : OutputL2 d) :
    ‖E (periodicL2DifferenceQuotient i h v)‖ ≤
      ‖periodicL2DifferenceQuotient i h (E v)‖ + (Cpdo + 2 * M * K) * ‖v‖ := by
  apply (norm_periodic_operator_differenceQuotient_le E i h v).trans
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  rw [hE]
  exact norm_periodicConjugationDifference_matrixSum_exterior_le hd R h₀ b hb hs A hA
    hbuffer c χ hχ i M K hM0 hK0 hM hK h hh hsmall

/-- If `E v = e` with `e ∈ H¹`, the represented normal applied to every small
nonzero difference quotient of `v` has a uniform L² bound. This is the final
translation input to the parent's coercive inverse and difference-quotient
converse in `app:ch_background:prop:bg-inverse`; it asserts no regularity of `v`.
-/
theorem norm_periodic_operator_differenceQuotient_of_matrix_representation_h1_le
    (h : ℝ) (hh : h ≠ 0) (hsmall : |h| ≤ h₀) (v : OutputL2 d)
    (e : PeriodicSobolevSpace d (EuclideanSpace ℝ (Fin d)) 1)
    (he : E v = PeriodicSobolevSpace.toL2 1 e) :
    ‖E (periodicL2DifferenceQuotient i h v)‖ ≤ ‖e‖ + (Cpdo + 2 * M * K) * ‖v‖ := by
  apply (norm_periodic_operator_differenceQuotient_of_matrix_representation_le
    hd R h₀ b hb hs A hA hbuffer c χ hχ i M K hM0 hK0 hM hK E hE h hh hsmall v).trans
  rw [he]
  exact add_le_add (norm_periodicL2DifferenceQuotient_le_sobolev e i h hh) (le_refl _)

end JanetCartan.ContinuumCommutator
