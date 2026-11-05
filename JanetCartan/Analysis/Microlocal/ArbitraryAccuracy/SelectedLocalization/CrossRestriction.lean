module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.CrossQuantization
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.SobolevScale
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.OperatorUniqueness
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction

/-!
# Cross quantization on the actual restriction space

An intermediate restriction and zero extension cannot simply be erased from
the composition of local operators. Here it is erased using the actual compact
output support of the left proof localizer. The primitive cross-quantization
estimate then applies to the literal local product and its real Hilbert adjoint.
Consumer: consecutive right/left proof masks in the finite residual chain of
`app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.LowBounds FiniteChain.Graph Pseudodifferential LocalSobolev
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization EvolutionIntegratedLocalization
open ResidualLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- The literal left quantization is fixed by a physical plateau on its
output-base support. This is proved on representatives and extended by density,
without a Sobolev zero-extension assertion (`app:ch_regular:eq:chain-tail`). -/
theorem sourceCutMultiplier_leftLocalizer_eq
    (ρ : ℝ) (mi : LocalizerSymbol (d + 1)) (Li : H →L[ℂ] H)
    (hLi : ∀ u, (∀ a, Integrable (fun y ↦ u y a)) → Li u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (ψ : E → ℝ) (hψ : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1)
    (hplateau : ∀ x ∈ Prod.fst '' tsupport mi, ψ x = 1) :
    (sourceCutMultiplier ψ hψ hb).comp Li = Li := by
  apply eq_of_leftLocalizer_representatives ρ mi _ Li ?_ hLi
  intro u hu
  filter_upwards [sourceCutMultiplier_coeFn ψ hψ hb (Li u), hLi u hu] with x hx hy
  change (sourceCutMultiplier ψ hψ hb (Li u)) x = _
  rw [hx, hy]
  by_cases hxbase : x ∈ Prod.fst '' tsupport mi
  · rw [hplateau x hxbase]
    simp
  · have hm ξ : mi (x, ρ⁻¹ • ξ) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hxbase ⟨(x, ρ⁻¹ • ξ), h, rfl⟩)
    simp [leftLocalizer, graphOperator, hm]

/-- Exact identification of the local cross product. The intermediate left
output is supported in U, so restriction/zero extension introduces no boundary
error (`app:ch_regular:lem:finite-chain`). -/
theorem local_crossQuantization_eq
    (ρ : ℝ) (mi : LocalizerSymbol (d + 1)) (Li Ro : H →L[ℂ] H)
    (hLi : ∀ u, (∀ a, Integrable (fun y ↦ u y a)) → Li u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (U : Set E) (hU : MeasurableSet U)
    (ψ : E → ℝ) (hψ : Continuous ψ) (hb : ∀ x, ‖ψ x‖ ≤ 1)
    (hs : tsupport ψ ⊆ U) (hplateau : ∀ x ∈ Prod.fst '' tsupport mi, ψ x = 1) :
    (1 - localRetardedOperator hU U Ro).comp (localRetardedOperator hU U Li) =
      localRetardedOperator hU U ((1 - Ro).comp Li) := by
  have hsupport := sourceCutMultiplier_leftLocalizer_eq ρ mi Li hLi ψ hψ hb hplateau
  ext1 u
  change restrictL2 U (Li (SmallSupport.zeroExtend hU u)) -
      restrictL2 U (Ro (SmallSupport.zeroExtend hU
        (localRetardedOperator hU U Li u))) =
    restrictL2 U (Li (SmallSupport.zeroExtend hU u) - Ro (Li (SmallSupport.zeroExtend hU u)))
  rw [zeroExtend_localRetardedOperator_of_mask hU hU Li ψ hψ hb hs hsupport u, map_sub]

/-- Instantiate the primitive cross-quantization producer on the same local
operators. The support identity above supplies exact identification in both
orientations; the restriction norm is its genuine extension-infimum norm.
Constants precede masks, scales, domains and realizations, and losses are
independent of accuracy (`app:ch_regular:eq:chain-tail`). -/
theorem exists_local_crossQuantization_restriction_bounds
    (K : Set E) (hK : IsCompact K) (Di Do : ℕ → ℝ)
    (hDi : ∀ k, 0 ≤ Di k) (hDo : ∀ k, 0 ≤ Do k) (bi bo : ℕ)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) :
    ∃ C : ℕ → ℕ → ℝ, (∀ m N, 0 ≤ C m N) ∧
      ∀ (mi mo : LocalizerSymbol (d + 1)), ContDiff ℝ ∞ mi → HasCompactSupport mi →
      ContDiff ℝ ∞ mo → HasCompactSupport mo →
      Prod.fst '' tsupport mi ⊆ K →
      (∀ p ∈ tsupport mi, ‖p.2‖ ≤ R) →
      (∀ p ∈ tsupport mi, ∀ z : E × E, dist z p ≤ δ → mo z = 1) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      (∀ k p, ‖iteratedFDeriv ℝ k mi p‖ ≤ Di k * L ^ (k + bi)) →
      (∀ k p, ‖iteratedFDeriv ℝ k mo p‖ ≤ Do k * L ^ (k + bo)) →
      ∀ (Li Ro : H →L[ℂ] H),
      (∀ u, (∀ a, Integrable (fun y ↦ u y a)) → Li u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      (∀ u, Ro u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) →
      ∀ (U : Set E) (hU : MeasurableSet U) (ψ : E → ℝ)
        (_hψ : Continuous ψ) (_hb : ∀ x, ‖ψ x‖ ≤ 1),
      tsupport ψ ⊆ U → (∀ x ∈ Prod.fst '' tsupport mi, ψ x = 1) →
      let S := (1 - localRetardedOperator hU U Ro).comp (localRetardedOperator hU U Li)
      ∀ (m N : ℕ) (backward : Bool) (u : LocalL2 U F),
        (if backward then S.adjoint u else S u) ∈ (restrictionSobolevScale U F hU).level m ∧
        (restrictionSobolevScale U F hU).gradeNorm m (if backward then S.adjoint u else S u) ≤
          C m N * ρ ^ m * L ^ (m + (d + 1 + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖ := by
  obtain ⟨C, hC, hcross⟩ := FiniteChains.CrossQuantization.exists_crossQuantization_twoSided_sobolev_bounds
    (r := q) K hK Di Do hDi hDo bi bo hδ hR
  choose B hB hcompare using fun m ↦ exists_restrictionScale_fourier_comparison (d + 1) q m
  refine ⟨fun m N ↦ B m * C m N, fun m N ↦ mul_nonneg (hB m).le (hC m N), ?_⟩
  intro mi mo hi his ho hos hcarrier hann hbuffer ρ L hL hLρ hij hoj Li Ro hLi hRo
    U hU ψ hψ hb hs hplateau S m N backward u
  have he : S = localRetardedOperator hU U ((1 - Ro).comp Li) :=
    local_crossQuantization_eq ρ mi Li Ro hLi U hU ψ hψ hb hs hplateau
  have heo : (if backward then S.adjoint u else S u) =
      restrictL2 U ((if backward then ((1 - Ro).comp Li).adjoint
        else (1 - Ro).comp Li) (SmallSupport.zeroExtend hU u)) := by
    cases backward
    · exact congrArg (fun A ↦ A u) he
    · rw [he, localRetardedOperator_adjoint hU hU]
      rfl
  have hfull := hcross mi mo hi his ho hos hcarrier hann hbuffer ρ L hL hLρ hij hoj
    Li Ro hLi hRo m N (SmallSupport.zeroExtend hU u)
  have hout : MemVectorFourierSobolev (m : ℝ)
      ((if backward then ((1 - Ro).comp Li).adjoint else (1 - Ro).comp Li)
        (SmallSupport.zeroExtend hU u)) ∧
      vectorFourierSobolevNorm (m : ℝ)
        ((if backward then ((1 - Ro).comp Li).adjoint else (1 - Ro).comp Li)
          (SmallSupport.zeroExtend hU u)) ≤
      C m N * ρ ^ m * L ^ (m + (d + 1 + 1) + (bo + bi)) * (L / ρ) ^ N * ‖u‖ := by
    cases backward
    · simpa only [Bool.false_eq_true, ite_false, LinearIsometry.norm_map] using hfull.1
    · simpa only [ite_true, LinearIsometry.norm_map] using hfull.2
  rw [heo]
  obtain ⟨hm, hn⟩ := hcompare m U hU _ _ hout.1 (restrictL2_coeFn U _).symm
  refine ⟨hm, hn.trans ?_⟩
  convert mul_le_mul_of_nonneg_left hout.2 (hB m).le using 1
  ring

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
