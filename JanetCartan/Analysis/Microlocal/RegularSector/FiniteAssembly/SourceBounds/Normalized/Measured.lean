module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.Normalized
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Positive

/-!
# Measured terminal costs for the same normalized source

Apply the actual normalized source's uniform Fourier estimate to the original
measurement masks. The identity remains between those masks. The literal local
adjoint exchanges their domains, and real compression retains the same measure.
Consumer: `finiteChain_observation_rapidDecayAt.hBcost` in
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open FiniteMasks.ActualFamily NormalizedSolver Characteristic.EvolutionIntegral
open FourierIntegral LowBounds Pseudodifferential LocalSobolev
open Characteristic.RetardedLocalization ArbitraryAccuracy ResponseTransfer Realization
open ArbitraryAccuracy.ResidualLocalization
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)

/-- The full normalized source discrepancy has order-zero measured
restriction bounds in both literal orientations. Constants precede the final
radial threshold and both domains; only the original measurement-mask supports
are required inside those domains (`measured-adjoint`, `resolved-angular-tail`). -/
theorem exists_normalizedSource_measured_discrepancy_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ L : ℝ, f.radialThreshold ≤ L →
      ∀ (U V : Set E) (hU : MeasurableSet U) (_hV : MeasurableSet V),
        tsupport ν ⊆ U → tsupport μ ⊆ V →
      let D := pairedSource f hK L output ho.continuous hob - 1
      let J := localRetardedOperator hU V
        (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb D)
      ∀ s,
        (∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
          MemRestrictionSobolev V s (J u) ∧
          restrictionSobolevNorm V s (J u) ≤ C s*restrictionSobolevNorm U s u) ∧
        (∀ u : LocalL2 V F, MemRestrictionSobolev V s u →
          MemRestrictionSobolev U s (J.adjoint u) ∧
          restrictionSobolevNorm U s (J.adjoint u) ≤ C s*restrictionSobolevNorm V s u) := by
  obtain ⟨A, hA, hbound⟩ := exists_normalizedSource_discrepancy_uniform_sobolev_constants
    f hK output ho hoc hob
  choose Cf hCf hf using fun s ↦ exists_measuredOperator_restriction_tame_constant
    (q := d+1) μ ν hμ hν hμc hνc hμb hνb s s
  choose Ca hCa ha using fun s ↦ exists_measuredOperator_restriction_tame_constant
    (q := d+1) ν μ hν hμ hνc hμc hνb hμb s s
  refine ⟨fun s ↦ (Cf s + Ca s)*A s,
    fun s ↦ mul_nonneg (add_nonneg (zero_le_one.trans (hCf s))
      (zero_le_one.trans (hCa s))) (hA s), ?_⟩
  intro L hL U V hU hV hνU hμV D J s
  constructor
  · intro u hu
    obtain ⟨hm, hn⟩ := hf s D (A s) 0 (hA s) le_rfl
      (by simpa only [zero_mul, add_zero] using hbound L hL s D (Or.inl rfl))
      U V hU hνU u hu
    simp only [zero_mul, add_zero] at hn
    refine ⟨hm, hn.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (zero_le_one.trans (hCa s))) (hA s)) restrictionSobolevNorm_nonneg
  · intro u hu
    rw [show J = localRetardedOperator hU V
      (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb D) from rfl,
      local_measuredOperator_adjoint hU hV]
    obtain ⟨hm, hn⟩ := ha s D.adjoint (A s) 0 (hA s) le_rfl
      (by simpa only [zero_mul, add_zero] using hbound L hL s D.adjoint (Or.inr rfl))
      V U hV hμV u hu
    simp only [zero_mul, add_zero] at hn
    refine ⟨hm, hn.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (zero_le_one.trans (hCf s))) (hA s)) restrictionSobolevNorm_nonneg

/-- The actual measured terminal discrepancy supplies the complex
`hBcost` input with zero frequency exponent and no derivative loss. The ONE
identity subtraction stays inside the physical masks
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem normalizedSource_measured_discrepancy_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {ι : Type*} (ρ L : ι → ℝ) (hL : ∀ i, f.radialThreshold ≤ L i)
    (U : Set E) (hU : MeasurableSet U)
    (hνU : tsupport ν ⊆ U) (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let T := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (pairedSource f hK (L i) output ho.continuous hob - 1)
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ
      (fun i ↦ (if backward then (localRetardedOperator hU U (T i)).adjoint
        else localRetardedOperator hU U (T i)).toLinearMap) := by
  intro T
  obtain ⟨C, hC, hbound⟩ := exists_normalizedSource_measured_discrepancy_constants
    f hK output ho hoc hob μ ν hμ hν hμc hνc hμb hνb
  intro s
  refine ⟨s, 0, C s, hC s, ?_⟩
  intro i u hu
  have hb : MemRestrictionSobolev U s
      ((if backward then (localRetardedOperator hU U (T i)).adjoint
        else localRetardedOperator hU U (T i)) u) ∧
      restrictionSobolevNorm U s
        ((if backward then (localRetardedOperator hU U (T i)).adjoint
          else localRetardedOperator hU U (T i)) u) ≤ C s * restrictionSobolevNorm U s u := by
    cases backward
    · exact (hbound (L i) (hL i) U U hU hU hνU hμU s).1 u hu
    · exact (hbound (L i) (hL i) U U hU hU hνU hμU s).2 u hu
  refine ⟨hb.1, ?_⟩
  change (restrictionSobolevScale U F hU).gradeNorm s
    ((if backward then (localRetardedOperator hU U (T i)).adjoint
      else localRetardedOperator hU U (T i)) u) ≤ _
  simpa only [Real.rpow_zero, mul_one, restrictionSobolevScale_gradeNorm hU hu,
    restrictionSobolevScale_gradeNorm hU hb.1] using hb.2

/-- Literal real compression and its Hilbert adjoint supply the terminal
cost on the same real restriction scale. Every threshold uses the same selected
family and measurement masks (`app:ch_regular:eq:chain-tail`, `negative-duality`). -/
theorem normalizedRealSource_measured_discrepancy_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {ι : Type*} (ρ L : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hL : ∀ i, f.radialThreshold ≤ L i)
    (U : Set E) (hU : MeasurableSet U)
    (hνU : tsupport ν ⊆ U) (hμU : tsupport μ ⊆ U) (backward : Bool) :
    let T := fun i ↦ measuredOperator μ ν hμ.continuous hν.continuous hμb hνb
      (pairedSource f hK (L i) output ho.continuous hob - 1)
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ
      (fun i ↦ (if backward then (localRealCompression hU U (T i)).adjoint
        else localRealCompression hU U (T i)).toLinearMap) := by
  intro T
  have hc := normalizedSource_measured_discrepancy_hasPolynomialRestrictionCost
    f hK output ho hoc hob μ ν hμ hν hμc hνc hμb hνb ρ L hL U hU hνU hμU backward
  have hr := realCompression_hasPolynomialRestrictionCost ρ hρ
    (fun i ↦ if backward then (T i).adjoint else T i) U U hU hU (by
      cases backward
      · exact hc
      · simpa only [Bool.true_eq, ite_true, localRetardedOperator_adjoint hU hU] using hc)
  cases backward
  · exact hr
  · simpa only [Bool.true_eq, ite_true, localRealCompression_adjoint hU hU] using hr

end JanetCartan.RegularSector.FiniteAssembly

