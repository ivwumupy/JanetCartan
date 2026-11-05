module

public import JanetCartan.Iteration.PhysicalEllipticWords.PairedOperations
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.WholeSpaceRestriction
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords.MeasuredCosts

/-!
# Whole-space ordinary regularity of the original residual factors

The ordinary input of `actual_finite_residual_word_reserved_bounds_of_one_step`
requires global Fourier Sobolev bounds on every compact smooth datum, separately
from the sharp oscillatory source bounds. The existing actual measured alphabet
has polynomial restriction costs on every measurement domain. On `univ`, every
extension is the very same original L² class, so those costs give this exact
ordinary input. There is no unsupported zero-extension claim at positive order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
open MeasureTheory Set
namespace JanetCartan.PhysicalEllipticWords
open LocalSobolev Pseudodifferential FourierIntegral
open ResponseTransfer ResponseTransfer.Complement
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.SelectedLocalization
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral

variable {d q : ℕ} {I : Type*}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The infimum restriction norm on the whole space bounds the Fourier norm
of the SAME class, with no derivative loss (`app:not:fourier`). -/
theorem exists_univ_restriction_fourier_bound (d q s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (Euclidean (d + 1))),
      MemRestrictionSobolev univ s (restrictL2 univ u) →
        MemVectorFourierSobolev (s : ℝ) u ∧
        vectorFourierSobolevNorm (s : ℝ) u ≤ C * restrictionSobolevNorm univ s (restrictL2 univ u) := by
  obtain ⟨C, hC, hb⟩ := exists_vector_extension_fourier_constant (d + 1) q s
  refine ⟨C, hC, ?_⟩
  intro u hu
  have he (e : SobolevExtension univ s (restrictL2 univ u)) : e.toL2 = u := by
    apply Lp.ext
    have hlocal : e.toFun =ᵐ[volume] restrictL2 univ u := by
      simpa only [Measure.restrict_univ] using e.restrict_eq
    have hrestrict : (restrictL2 univ u : Euclidean (d + 1) → EuclideanSpace ℂ (Fin q)) =ᵐ[volume] u := by
      simpa only [Measure.restrict_univ] using restrictL2_coeFn univ u
    exact e.toL2_coeFn.trans (hlocal.trans hrestrict)
  have hm := (hb univ _ hu.some).1
  rw [he] at hm
  refine ⟨hm, ?_⟩
  have hdiv : vectorFourierSobolevNorm (s : ℝ) u / C ≤
      restrictionSobolevNorm univ s (restrictL2 univ u) := by
    unfold restrictionSobolevNorm
    refine le_csInf ⟨hu.some.jetNorm, hu.some, rfl⟩ ?_
    rintro _ ⟨e, rfl⟩
    apply (div_le_iff₀ hC).2
    simpa only [he, mul_comm] using (hb univ _ e).2
  simpa only [mul_comm] using (div_le_iff₀ hC).1 hdiv

/-- Actual whole-space restriction costs supply the ordinary finite-word
input on all compact smooth tests. Constants may depend on the individual
family member, exactly as permitted by the smooth-representative constructor
(`app:ch_regular:lem:finite-chain`). -/
theorem ordinary_bounds_of_univ_polynomial_cost
    (ρ : I → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (T : I → H →L[ℂ] H)
    (hcost : HasPolynomialSobolevCost (restrictionSobolevScale univ F MeasurableSet.univ)
      (restrictionSobolevScale univ F MeasurableSet.univ) ρ
      (fun i ↦ (localRetardedOperator MeasurableSet.univ univ (T i)).toLinearMap)) :
    ∀ i (s : ℕ), ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : graphTestSpace (d + 1) q,
      MemVectorFourierSobolev (s : ℝ) (T i (graphTestToLp u)) ∧
      vectorFourierSobolevNorm (s : ℝ) (T i (graphTestToLp u)) ≤
        C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u) := by
  intro i s
  obtain ⟨t, power, D, hD, hbound⟩ := hcost s
  obtain ⟨Cin, hCin, hinput⟩ := vector_restrictionSobolev_nat_bounds (d + 1) q t
  obtain ⟨Cout, hCout, houtput⟩ := exists_univ_restriction_fourier_bound d q s
  refine ⟨t, Cout * (D * (ρ i) ^ power) * Cin,
    mul_nonneg (mul_nonneg hCout.le (mul_nonneg hD (Real.rpow_nonneg (hρ i) _))) hCin.le, ?_⟩
  intro u
  let v := graphTestToLp u
  have hv := hinput v (graphTest_memVectorFourierSobolev (t : ℝ) u)
    univ (restrictL2 univ v) (restrictL2_coeFn univ v).symm
  have hact : localRetardedOperator MeasurableSet.univ univ (T i) (restrictL2 univ v) =
      restrictL2 univ (T i v) := by
    change restrictL2 univ (T i (SmallSupport.zeroExtend MeasurableSet.univ (restrictL2 univ v))) = _
    rw [zeroExtend_restrictL2_univ]
  obtain ⟨hm, hb⟩ := hbound i (restrictL2 univ v) hv.1
  have hm' : MemRestrictionSobolev univ s (restrictL2 univ (T i v)) := by
    change MemRestrictionSobolev univ s
      (localRetardedOperator MeasurableSet.univ univ (T i) (restrictL2 univ v)) at hm
    simpa only [hact] using hm
  have hb' : restrictionSobolevNorm univ s (restrictL2 univ (T i v)) ≤
      D * (ρ i) ^ power * restrictionSobolevNorm univ t (restrictL2 univ v) := by
    change (restrictionSobolevScale univ F MeasurableSet.univ).gradeNorm s
      (localRetardedOperator MeasurableSet.univ univ (T i) (restrictL2 univ v)) ≤ _ at hb
    rw [hact, restrictionSobolevScale_gradeNorm MeasurableSet.univ hm',
      restrictionSobolevScale_gradeNorm MeasurableSet.univ hv.1] at hb
    exact hb
  obtain ⟨hmem, hout⟩ := houtput (T i v) hm'
  refine ⟨hmem, hout.trans ?_⟩
  calc
    _ ≤ Cout * (D * (ρ i) ^ power * (Cin * vectorFourierSobolevNorm (t : ℝ) v)) :=
      mul_le_mul_of_nonneg_left (hb'.trans (mul_le_mul_of_nonneg_left hv.2
        (mul_nonneg hD (Real.rpow_nonneg (hρ i) _)))) hCout.le
    _ = _ := by ring

end JanetCartan.PhysicalEllipticWords
