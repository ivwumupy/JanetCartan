module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds.Normalized
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Positive

/-!
# Restriction costs for the normalized terminal discrepancy

The actual input mask is applied before zero extension at positive Sobolev
orders. Its adjoint reverses the physical masks and uses the common output
support. Thus the complete source and its single identity subtraction feed
`finiteChain_observation_rapidDecayAt.hBcost` on the original restriction spaces
(`app:ch_regular:lem:finite-chain`, `resolved-angular-tail`).
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

/-- Order-zero bounds for the actual normalized complete source on the
original restriction spaces, together with its literal local adjoint. The
constants precede the threshold and domains. The source mask is applied before
zero extension; no positive-order regularity of bare zero extension is used
(`sector-theorem-identity`, `measured-adjoint`). -/
theorem exists_normalizedSource_uniform_restriction_constants
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
      ∀ L : ℝ, f.radialThreshold ≤ L →
      ∀ (U V : Set E) (hU : MeasurableSet U) (_hV : MeasurableSet V),
        tsupport f.inputMask ⊆ U → tsupport output ⊆ V →
      let J := localRetardedOperator hU V (pairedSource f hK L output ho.continuous hob)
      ∀ s,
        (∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
          MemRestrictionSobolev V s (J u) ∧
          restrictionSobolevNorm V s (J u) ≤ C s*restrictionSobolevNorm U s u) ∧
        (∀ u : LocalL2 V F, MemRestrictionSobolev V s u →
          MemRestrictionSobolev U s (J.adjoint u) ∧
          restrictionSobolevNorm U s (J.adjoint u) ≤ C s*restrictionSobolevNorm V s u) := by
  let hib := fun y ↦ (Real.norm_of_nonneg (f.inputMask_range y).1).trans_le (f.inputMask_range y).2
  let hfb := fun y ↦ (Real.norm_of_nonneg (f.outputMask_range y).1).trans_le (f.outputMask_range y).2
  choose Ki hKi hi using fun s ↦ exists_sourceCut_zeroExtension_fourier_bound
    (q := d+1) f.inputMask f.inputMask_smooth f.inputMask_compact hib s
  choose Kc hKc hc using fun s ↦ exists_sourceCut_zeroExtension_fourier_bound
    (q := d+1) output ho hoc hob s
  choose Ci hCi hmi using fun s ↦ exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) f.inputMask f.inputMask_smooth f.inputMask_compact hib s
  choose Co hCo hmo using fun s ↦ exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) f.outputMask f.outputMask_smooth f.outputMask_compact hfb s
  choose Cc hCc hmc using fun s ↦ exists_sourceCutMultiplier_fourierSobolev_bound
    (r := d+1) output ho hoc hob s
  choose Cr hCr hr using fun s ↦ vector_restrictionSobolev_nat_bounds (d+1) (d+1) s
  let Cf s := Cr s * Cc s * Co s * Ki s
  let Ca s := Cr s * Ci s * Co s * Kc s
  have hCf s : 0 ≤ Cf s := mul_nonneg
    (mul_nonneg (mul_nonneg (hCr s).le (hCc s)) (hCo s)) (zero_le_one.trans (hKi s))
  have hCa s : 0 ≤ Ca s := mul_nonneg
    (mul_nonneg (mul_nonneg (hCr s).le (hCi s)) (hCo s)) (zero_le_one.trans (hKc s))
  refine ⟨fun s ↦ Cf s + Ca s, fun s ↦ add_nonneg (hCf s) (hCa s), ?_⟩
  intro L hL U V hU hV hiU hoV J s
  have hfreq (v : H) (hv : MemVectorFourierSobolev (s : ℝ) v) :
      MemVectorFourierSobolev (s : ℝ) (sourceFourierOperator f hK L v) ∧
      vectorFourierSobolevNorm (s : ℝ) (sourceFourierOperator f hK L v) ≤
        vectorFourierSobolevNorm (s : ℝ) v :=
    scalarPhysicalFrequencyOperator_fourierSobolev_bound _ _ _ _ v hv
  constructor
  · intro u hu
    obtain ⟨hm₁, hn₁⟩ := hi s U hU hiU u hu
    obtain ⟨hm₂, hn₂⟩ := hfreq _ hm₁
    obtain ⟨hm₃, hn₃⟩ := hmo s _ hm₂
    obtain ⟨hm₄, hn₄⟩ := hmc s _ hm₃
    have hmem : MemVectorFourierSobolev (s : ℝ)
        (pairedSource f hK L output ho.continuous hob (SmallSupport.zeroExtend hU u)) := by
      rw [pairedSource_eq_fourier_composition f hK hL]
      exact hm₄
    obtain ⟨hm, hn⟩ := hr s _ hmem V (J u) (restrictL2_coeFn V _).symm
    refine ⟨hm, hn.trans ?_⟩
    have hb : vectorFourierSobolevNorm (s : ℝ)
        (pairedSource f hK L output ho.continuous hob (SmallSupport.zeroExtend hU u)) ≤
        Cc s * (Co s * (Ki s * restrictionSobolevNorm U s u)) := by
      rw [pairedSource_eq_fourier_composition f hK hL]
      exact hn₄.trans (mul_le_mul_of_nonneg_left
        (hn₃.trans (mul_le_mul_of_nonneg_left (hn₂.trans hn₁) (hCo s))) (hCc s))
    calc
      _ ≤ Cr s * (Cc s * (Co s * (Ki s * restrictionSobolevNorm U s u))) :=
        mul_le_mul_of_nonneg_left hb (hCr s).le
      _ = Cf s * restrictionSobolevNorm U s u := by dsimp [Cf]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hCa s))
        restrictionSobolevNorm_nonneg
  · intro u hu
    rw [show J = localRetardedOperator hU V (pairedSource f hK L output ho.continuous hob) from rfl,
      localRetardedOperator_adjoint hU hV]
    obtain ⟨hm₁, hn₁⟩ := hc s V hV hoV u hu
    obtain ⟨hm₂, hn₂⟩ := hmo s _ hm₁
    obtain ⟨hm₃, hn₃⟩ := hfreq _ hm₂
    obtain ⟨hm₄, hn₄⟩ := hmi s _ hm₃
    have hmem : MemVectorFourierSobolev (s : ℝ)
        ((pairedSource f hK L output ho.continuous hob).adjoint (SmallSupport.zeroExtend hV u)) := by
      rw [pairedSource_adjoint_eq_fourier_composition f hK hL]
      exact hm₄
    obtain ⟨hm, hn⟩ := hr s _ hmem U
      (localRetardedOperator hV U (pairedSource f hK L output ho.continuous hob).adjoint u)
      (restrictL2_coeFn U _).symm
    refine ⟨hm, hn.trans ?_⟩
    have hb : vectorFourierSobolevNorm (s : ℝ)
        ((pairedSource f hK L output ho.continuous hob).adjoint (SmallSupport.zeroExtend hV u)) ≤
        Ci s * (Co s * (Kc s * restrictionSobolevNorm V s u)) := by
      rw [pairedSource_adjoint_eq_fourier_composition f hK hL]
      exact hn₄.trans (mul_le_mul_of_nonneg_left
        (hn₃.trans (hn₂.trans (mul_le_mul_of_nonneg_left hn₁ (hCo s)))) (hCi s))
    calc
      _ ≤ Cr s * (Ci s * (Co s * (Kc s * restrictionSobolevNorm V s u))) :=
        mul_le_mul_of_nonneg_left hb (hCr s).le
      _ = Ca s * restrictionSobolevNorm V s u := by dsimp [Ca]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hCf s))
        restrictionSobolevNorm_nonneg

/-- The same complex source minus ONE local identity has terminal cost
with zero frequency exponent and no derivative loss, including the literal
adjoint. No terminal decay or source plateau is assumed
(`app:ch_regular:eq:chain-tail`, `resolved-angular-tail`). -/
theorem normalizedSource_discrepancy_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    {ι : Type*} (ρ L : ι → ℝ) (hL : ∀ i, f.radialThreshold ≤ L i)
    (U : Set E) (hU : MeasurableSet U)
    (hiU : tsupport f.inputMask ⊆ U) (hoU : tsupport output ⊆ U) (backward : Bool) :
    HasPolynomialSobolevCost (restrictionSobolevScale U F hU)
      (restrictionSobolevScale U F hU) ρ
      (fun i ↦ (if backward then
        (localRetardedOperator hU U (pairedSource f hK (L i) output ho.continuous hob)).adjoint
        else localRetardedOperator hU U (pairedSource f hK (L i) output ho.continuous hob)).toLinearMap -
          LinearMap.id) := by
  obtain ⟨C, hC, hbound⟩ := exists_normalizedSource_uniform_restriction_constants f hK output ho hoc hob
  intro s
  refine ⟨s, 0, C s + 1, add_nonneg (hC s) zero_le_one, ?_⟩
  intro i u hu
  let T := if backward then
    (localRetardedOperator hU U (pairedSource f hK (L i) output ho.continuous hob)).adjoint
    else localRetardedOperator hU U (pairedSource f hK (L i) output ho.continuous hob)
  have hb : MemRestrictionSobolev U s (T u) ∧
      restrictionSobolevNorm U s (T u) ≤ C s * restrictionSobolevNorm U s u := by
    cases backward
    · exact (hbound (L i) (hL i) U U hU hU hiU hoU s).1 u hu
    · exact (hbound (L i) (hL i) U U hU hU hiU hoU s).2 u hu
  let G := restrictionSobolevScale U F hU
  have hm : T u - u ∈ G.level s := (G.level s).sub_mem hb.1 hu
  refine ⟨hm, ?_⟩
  change G.gradeNorm s (T u - u) ≤ (C s + 1) * ρ i ^ (0 : ℝ) * G.gradeNorm s u
  rw [Real.rpow_zero, mul_one]
  calc
    _ ≤ G.gradeNorm s (T u) + G.gradeNorm s u := G.gradeNorm_sub_le hb.1 hu
    _ ≤ C s * G.gradeNorm s u + G.gradeNorm s u := by
      exact add_le_add (by simpa only [G, restrictionSobolevScale_gradeNorm hU hb.1,
        restrictionSobolevScale_gradeNorm hU hu] using hb.2) le_rfl
    _ = _ := by ring

/-- Real inclusion and real part transfer the actual normalized terminal
cost, retaining the one identity subtraction and literal real adjoint on the
same measure (`app:ch_regular:eq:chain-tail`, `negative-duality`). -/
theorem normalizedRealSource_discrepancy_hasPolynomialRestrictionCost
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    {ι : Type*} (ρ L : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hL : ∀ i, f.radialThreshold ≤ L i)
    (U : Set E) (hU : MeasurableSet U)
    (hiU : tsupport f.inputMask ⊆ U) (hoU : tsupport output ⊆ U) (backward : Bool) :
    HasPolynomialSobolevCost (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U RF hU) ρ
      (fun i ↦ (if backward then
        (localRealCompression hU U (pairedSource f hK (L i) output ho.continuous hob)).adjoint
        else localRealCompression hU U (pairedSource f hK (L i) output ho.continuous hob)).toLinearMap -
          LinearMap.id) := by
  have hc := normalizedSource_discrepancy_hasPolynomialRestrictionCost
    f hK output ho hoc hob ρ L hL U hU hiU hoU backward
  have hr := polynomialCost_comp (restrictionSobolevScale U RF hU)
    (restrictionSobolevScale U F hU) (restrictionSobolevScale U RF hU) hρ
    (compLp_hasPolynomialRestrictionCost ρ (euclideanRealPart (ι := Fin (d+1))) U hU)
    (polynomialCost_comp (restrictionSobolevScale U RF hU)
      (restrictionSobolevScale U F hU) (restrictionSobolevScale U F hU) hρ hc
      (compLp_hasPolynomialRestrictionCost ρ (euclideanComplexInclusion (ι := Fin (d+1))) U hU))
  convert hr using 1
  funext i
  apply LinearMap.ext
  intro u
  have he (T : H →L[ℂ] H) :
      localRealCompression hU U T u - u =
        l2RealPart (volume.restrict U)
          (localRetardedOperator hU U T (l2ComplexInclusion (volume.restrict U) u) -
            l2ComplexInclusion (volume.restrict U) u) := by
    rw [map_sub, realPart_inclusion]
    rfl
  cases backward
  · exact he _
  · simp only [ite_true, localRealCompression_adjoint hU hU,
      localRetardedOperator_adjoint hU hU]
    exact he (pairedSource f hK (L i) output ho.continuous hob).adjoint

end JanetCartan.RegularSector.FiniteAssembly

