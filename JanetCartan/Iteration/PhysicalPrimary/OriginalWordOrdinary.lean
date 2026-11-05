module

public import JanetCartan.Iteration.PhysicalEllipticWords.OrdinaryGlobal
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPdoProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedSymbols
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.LocalComplex
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalWordOrdinaryTemplate

/-!
# Ordinary bounds and the exact sum of the original residual letters

The ordinary input of
`actual_finite_residual_word_reserved_bounds_of_one_step` is pointwise in the
current. A singleton family at scale one therefore uses the actual current's
coefficient seminorms; no bound uniform in the current or source contraction is
assumed. The same full Q/B, original W1, literal order-one retained operator,
physical conjugate pairs, and two measurement masks are retained.

The finite-sum identity is an equality of COMPLEX operators before any real
compression (`app:ch_regular:lem:finite-chain`, `energy-complete-residual`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalWordOrdinary
open LocalSobolev Pseudodifferential FourierIntegral
open ResponseTransfer ResponseTransfer.Complement
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.SelectedLocalization
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral RegularSector.FiniteAssembly

/-- The actual coefficient seminorm itself is a valid singleton-family
profile at scale one. No large-frequency or history-uniform premise is added. -/
theorem unit_coefficient_profile {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set E) (f : E → F) :
    (∀ m, 0 ≤ cNorm K m f) ∧
    ∀ (_ : Unit) (m : ℕ), cNorm K m f ≤ cNorm K m f * (1 : ℝ) ^ (m-1) := by
  refine ⟨fun m ↦ cNorm_nonneg K m f, ?_⟩
  intro i m
  simp only [one_pow, mul_one, le_refl]

/-- The two existing measurement bumps are used at their full smooth order,
not an unspecified finite regularity parameter. -/
theorem bump_smooth {n : ℕ} {x : Euclidean n} (χ : ContDiffBump x) :
    ContDiff ℝ ∞ (χ : Euclidean n → ℝ) := χ.contDiff

/-- The actual current's sector reserve dominates the native algebraic
low order; no additional coefficient bound is assumed. -/
theorem algebraic_low_bounds {d : ℕ} (KQ : Set (Euclidean (d+1)))
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (B : Euclidean (d+1) → MetricTensor (d+1)) {M : ℝ}
    (hQ : cNorm KQ (RegularSector.FiniteEvolution.sectorLowOrder d) Q ≤ M)
    (hB : cNorm KQ (RegularSector.FiniteEvolution.sectorLowOrder d) B ≤ M) :
    cNorm KQ (2*(d+2)+2) Q ≤ M ∧ cNorm KQ (2*(d+2)+2) B ≤ M := by
  have horder : 2*(d+2)+2 ≤ RegularSector.FiniteEvolution.sectorLowOrder d := by
    have h := (RegularSector.FiniteEvolution.sectorLowOrder_bounds d).2.2
    omega
  exact ⟨(cNorm_mono_order horder).trans hQ, (cNorm_mono_order horder).trans hB⟩

variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Whole-space polynomial restriction cost at the single scale one gives
exactly the pointwise ordinary Fourier-Sobolev input of the finite-word theorem. -/
theorem ordinary_from_unit_cost (T : H →L[ℂ] H)
    (hcost : HasPolynomialSobolevCost (restrictionSobolevScale univ F MeasurableSet.univ)
      (restrictionSobolevScale univ F MeasurableSet.univ) (fun _ : Unit ↦ (1 : ℝ))
      (fun _ : Unit ↦ (localRetardedOperator MeasurableSet.univ univ T).toLinearMap)) :
    ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : graphTestSpace (d+1) q,
      MemVectorFourierSobolev (s : ℝ) (T (graphTestToLp u)) ∧
      vectorFourierSobolevNorm (s : ℝ) (T (graphTestToLp u)) ≤
        C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u) :=
  PhysicalEllipticWords.ordinary_bounds_of_univ_polynomial_cost
    (fun _ : Unit ↦ (1 : ℝ)) (fun _ ↦ zero_le_one) (fun _ ↦ T) hcost ()

/-- Measurement distributes over the SAME finite sum as an equality of
complex operators, with the source mask kept on the right of every factor. -/
theorem measured_sum_of_eq {ι : Type*} [Fintype ι]
    (χout χin : E → ℝ) (ho : Continuous χout) (hi : Continuous χin)
    (hob : ∀ y, ‖χout y‖ ≤ 1) (hib : ∀ y, ‖χin y‖ ≤ 1)
    (raw : ι → H →L[ℂ] H) (P : H →L[ℂ] H) (hP : P = ∑ a, raw a) :
    measuredOperator χout χin ho hi hob hib P =
      ∑ a, measuredOperator χout χin ho hi hob hib (raw a) := by
  classical
  rw [hP]
  ext1 u
  simp only [measuredOperator, ContinuousLinearMap.comp_apply,
    sum_apply, map_sum]

/-- The optional local complex bundle is the very same measured sum, not a
real compression standing in for a complex identity. -/
theorem local_complex_sum_of_eq {ι : Type*} [Fintype ι]
    {U : Set E} (hU : MeasurableSet U) (V : Set E)
    (raw : ι → H →L[ℂ] H) (P : H →L[ℂ] H) (hP : P = ∑ a, raw a) :
    FixedDomainInverse.complexLocalRetardedOperator hU V P =
      ∑ a, FixedDomainInverse.complexLocalRetardedOperator hU V (raw a) := by
  classical
  rw [hP]
  ext1 u
  rw [sum_apply]
  change restrictL2 V ((∑ a, raw a) (SmallSupport.zeroExtend hU u)) =
    ∑ a, restrictL2 V (raw a (SmallSupport.zeroExtend hU u))
  simp only [sum_apply, map_sum]

end JanetCartan.PhysicalPrimary.OriginalWordOrdinary

apply_original_ordinary_residual_letters
