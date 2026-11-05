module

public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.Compression
public import JanetCartan.Analysis.Microlocal.RegularSector.Adjoints

/-!
# Bounded realization of the real sector solver and residual

For supplied bounded factors this constructs the finite paired sum, then applies
the literal `-i` and output cutoff of
`app:ch_response:eq:response-actual-solver-formula`. The plus residual is exactly
`-E` (`app:ch_regular_base:eq:two-residual-conventions`). Analytic existence and
estimates for the supplied factors and complete error are separate inputs.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace JanetCartan.RegularSector.Realization

section Factors

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [StarAddMonoid X] [StarModule ℂ X] [NormedStarGroup X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
  [StarAddMonoid Y] [StarModule ℂ Y] [NormedStarGroup Y]

/-- Whole-factor conjugation as a bounded operator
(`app:ch_regular_base:eq:signed-graph-factor`). -/
def boundedConjugate (T : X →L[ℂ] Y) : X →L[ℂ] Y :=
  (conjugateOperator T.toLinearMap).mkContinuous ‖T‖ (by
    intro x
    simpa only [conjugateOperator_apply, ContinuousLinearMap.coe_coe, norm_star] using
      T.le_opNorm (star x))

/-- Bounded conjugation realizes the published algebraic conjugation
(`app:ch_regular_base:eq:signed-graph-factor`). -/
@[simp] theorem boundedConjugate_toLinearMap (T : X →L[ℂ] Y) :
    (boundedConjugate T).toLinearMap = conjugateOperator T.toLinearMap := rfl

variable {η : Type*} {C : η → Type*}
  [∀ j, NormedAddCommGroup (C j)] [∀ j, InnerProductSpace ℂ (C j)]
  [∀ j, StarAddMonoid (C j)] [∀ j, StarModule ℂ (C j)]

/-- The actual finite bounded sum of complete antipodal sectors, with the
minus sign in the conjugate characteristic integral
(`app:ch_regular_base:eq:QN-definition`). -/
def boundedPairedParametrix (s : Finset η) (T : ∀ j, C j →L[ℂ] Y)
    (J : ∀ j, C j →L[ℂ] C j) (V : ∀ j, X →L[ℂ] C j)
    (A : η → X →L[ℂ] X) : X →L[ℂ] Y :=
  let Q := boundedParametrix s T J V A
  Q - boundedConjugate Q

/-- The bounded construction is precisely `pairedParametrix`, retaining all
whole factors (`app:ch_regular_base:eq:QN-definition`). -/
theorem boundedPairedParametrix_toLinearMap (s : Finset η) (T : ∀ j, C j →L[ℂ] Y)
    (J : ∀ j, C j →L[ℂ] C j) (V : ∀ j, X →L[ℂ] C j)
    (A : η → X →L[ℂ] X) :
    (boundedPairedParametrix s T J V A).toLinearMap =
      pairedParametrix s (fun j ↦ (T j).toLinearMap) (fun j ↦ (J j).toLinearMap)
        (fun j ↦ (V j).toLinearMap) (fun j ↦ (A j).toLinearMap) := by
  change (boundedParametrix s T J V A).toLinearMap -
    conjugateOperator (boundedParametrix s T J V A).toLinearMap = _
  rw [boundedParametrix_toLinearMap, pairedParametrix, partner_parametrix, sub_eq_add_neg]

/-- Reality of the paired bounded construction follows from the published
whole-factor identities (`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem boundedPairedParametrix_conjugation (s : Finset η) (T : ∀ j, C j →L[ℂ] Y)
    (J : ∀ j, C j →L[ℂ] C j) (V : ∀ j, X →L[ℂ] C j)
    (A : η → X →L[ℂ] X) :
    conjugateOperator (boundedPairedParametrix s T J V A).toLinearMap =
      -(boundedPairedParametrix s T J V A).toLinearMap := by
  rw [boundedPairedParametrix_toLinearMap]
  exact conjugateOperator_pairedParametrix _ _ _ _ _

end Factors

variable {ι κ α β : Type*} [Fintype ι] [Fintype κ]
  [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- The bounded complex solver, with the original output localizer and literal
`-i` (`app:ch_response:eq:response-actual-solver-formula`). -/
def boundedSectorSolver
    (χ : Lp (EuclideanSpace ℂ κ) 2 ν →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (Q : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν) :=
  χ ∘L (-Complex.I • Q)

/-- The actual real solver is compression of the normalized bounded construction
(`app:ch_regular_base:eq:real-sector-normalization`). -/
def realSectorSolver
    (χ : Lp (EuclideanSpace ℂ κ) 2 ν →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (Q : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν) :=
  realCompression (boundedSectorSolver χ Q)

/-- The cutoff solver reuses `physicalNormalization` exactly
(`app:ch_regular_base:eq:real-sector-normalization`). -/
theorem boundedSectorSolver_toLinearMap
    (χ : Lp (EuclideanSpace ℂ κ) 2 ν →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (Q : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν) :
    (boundedSectorSolver χ Q).toLinearMap = χ.toLinearMap.comp (physicalNormalization Q.toLinearMap) := rfl

/-- A real output localizer and anti-real paired sum give a real solver
(`app:ch_regular_base:eq:real-sector-normalization`). -/
theorem boundedSectorSolver_conjugation
    (χ : Lp (EuclideanSpace ℂ κ) 2 ν →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (Q : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (hχ : conjugateOperator χ.toLinearMap = χ.toLinearMap)
    (hQ : conjugateOperator Q.toLinearMap = -Q.toLinearMap) :
    conjugateOperator (boundedSectorSolver χ Q).toLinearMap =
      (boundedSectorSolver χ Q).toLinearMap := by
  rw [boundedSectorSolver_toLinearMap, conjugateOperator_comp, hχ,
    conjugateOperator_physicalNormalization Q.toLinearMap hQ]

/-- Exact complex action of the real solver on embedded real inputs
(`app:ch_regular_base:eq:real-sector-normalization`). -/
theorem inclusion_realSectorSolver
    (χ : Lp (EuclideanSpace ℂ κ) 2 ν →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (Q : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (hχ : conjugateOperator χ.toLinearMap = χ.toLinearMap)
    (hQ : conjugateOperator Q.toLinearMap = -Q.toLinearMap)
    (f : Lp (EuclideanSpace ℝ ι) 2 μ) :
    l2ComplexInclusion ν (realSectorSolver χ Q f) =
      χ (-Complex.I • Q (l2ComplexInclusion μ f)) :=
  inclusion_realCompression _ (boundedSectorSolver_conjugation χ Q hχ hQ) f

/-- Both quadratures of the real solver agree with the actual complex construction
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem realSectorSolver_complex_extension
    (χ : Lp (EuclideanSpace ℂ κ) 2 ν →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (Q : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (hχ : conjugateOperator χ.toLinearMap = χ.toLinearMap)
    (hQ : conjugateOperator Q.toLinearMap = -Q.toLinearMap)
    (z : Lp (EuclideanSpace ℂ ι) 2 μ) :
    χ (-Complex.I • Q z) = l2ComplexInclusion ν (realSectorSolver χ Q (l2RealPart μ z)) +
      Complex.I • l2ComplexInclusion ν (realSectorSolver χ Q (l2RealPart μ (-Complex.I • z))) :=
  realCompression_complex_extension _ (boundedSectorSolver_conjugation χ Q hχ hQ) z

/-- Real compression retains the actual complex solver norm estimate
(`app:ch_regular_base:eq:sector-theorem-solution`). -/
theorem realSectorSolver_norm_le
    (χ : Lp (EuclideanSpace ℂ κ) 2 ν →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (Q : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν) :
    ‖realSectorSolver χ Q‖ ≤ ‖boundedSectorSolver χ Q‖ ∧
      ‖boundedSectorSolver χ Q‖ ≤ ‖χ‖ * ‖Q‖ := by
  refine ⟨realCompression_norm_le _, ?_⟩
  simpa only [boundedSectorSolver, norm_smul, norm_neg, Complex.norm_I, one_mul] using
    ContinuousLinearMap.opNorm_comp_le χ (-Complex.I • Q)

/-- The plus-residual convention is literally minus the supplied complete error
(`app:ch_regular_base:eq:two-residual-conventions`). -/
def realSectorResidual
    (E : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :=
  realOutputCompression (-E)

/-- A supplied bounded realization of the complete algebraic residual inherits
its reality from the whole factors. No reality or intertwining of the residual
is assumed (`app:ch_regular_base:eq:two-residual-conventions`). -/
theorem completeResidual_conjugation
    (E A : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (L : Lp (EuclideanSpace ℂ κ) 2 ν →ₗ[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (Q : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ κ) 2 ν)
    (hE : E.toLinearMap = SectorResidual.sectorResidual A.toLinearMap L Q.toLinearMap)
    (hA : conjugateOperator A.toLinearMap = A.toLinearMap)
    (hL : conjugateOperator L = -L)
    (hQ : conjugateOperator Q.toLinearMap = -Q.toLinearMap) :
    conjugateOperator E.toLinearMap = E.toLinearMap := by
  rw [hE]
  exact conjugateOperator_residual _ _ _ hA hL hQ

/-- Complex action of the plus residual on embedded real inputs
(`app:ch_regular_base:eq:two-residual-conventions`). -/
theorem inclusion_realSectorResidual
    (E : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hE : conjugateOperator E.toLinearMap = E.toLinearMap)
    (f : Lp (EuclideanSpace ℝ ι) 2 μ) :
    l2ComplexInclusion μ (realSectorResidual E f) = -E (l2ComplexInclusion μ f) := by
  apply inclusion_realCompression (-E)
  change conjugateOperator (-E.toLinearMap) = -E.toLinearMap
  rw [conjugateOperator_neg, hE]

/-- `R = -E` holds on both quadratures, hence on their entire complexification
(`app:ch_regular_base:eq:two-residual-conventions`). -/
theorem realSectorResidual_complex_extension
    (E : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ)
    (hE : conjugateOperator E.toLinearMap = E.toLinearMap)
    (z : Lp (EuclideanSpace ℂ ι) 2 μ) :
    -E z = l2ComplexInclusion μ (realSectorResidual E (l2RealPart μ z)) +
      Complex.I • l2ComplexInclusion μ (realSectorResidual E (l2RealPart μ (-Complex.I • z))) := by
  apply realCompression_complex_extension (-E)
  change conjugateOperator (-E.toLinearMap) = -E.toLinearMap
  rw [conjugateOperator_neg, hE]

/-- The sign change and real compression lose no residual norm bound
(`app:ch_regular_base:eq:sector-theorem-residual`). -/
theorem realSectorResidual_norm_le
    (E : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 μ) :
    ‖realSectorResidual E‖ ≤ ‖E‖ := by
  simpa only [realSectorResidual, norm_neg] using realOutputCompression_norm_le (-E)

end JanetCartan.RegularSector.Realization
