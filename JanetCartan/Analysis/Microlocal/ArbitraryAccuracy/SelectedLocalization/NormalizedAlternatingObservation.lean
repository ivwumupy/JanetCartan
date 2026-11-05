module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.NormalizedObservation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.Alternating

/-!
# Observing the actual chain with both quantizations

The proved normalized terminal deduction is applied to the alternating chain.
Inserted identities preserve the original physical source plateau. The original
ordered product remains unchanged (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open ResponseTransfer FourierIntegral FourierIntegral.LowBounds FiniteChain.Graph LocalSobolev
open RegularSector.FiniteMasks.ActualFamily RegularSector.NormalizedSolver
open RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral
variable {d : ℕ} {ι : Type*}
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ C₀ : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)
local notation "Hu" => LocalL2 (univ : Set E) V
local notation "G" => restrictionSobolevScale (univ : Set E) V MeasurableSet.univ

/-- Apply the normalized supported terminal source to the ORIGINAL chain
using the two actual primitive leakage estimates: selected signed-letter
leakage and cross quantization. No left/right masks are identified, and the
terminal source estimate is used only on the supported full word. Consumers:
`NormalizedResidualWords.measured_realResidual_hchain_of_words` and the same
normalized inverse (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem normalizedSource_alternatingChain_observation_rapidDecayAt
    (f : ActualMaskFamily Ω x RQ A₀ K C₀) (hK : IsCompact K)
    (hsym : ∀ η ∈ K, -η ∈ K) (L₀ : ℝ) (hL₀ : f.radialThreshold ≤ L₀)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hor : ∀ y, output y ∈ Icc (0 : ℝ) 1)
    (χ₃ : ContDiffBump x) (U : Set E) (hU : IsOpen U)
    (hχ₃ : tsupport (χ₃ : E → ℝ) ⊆ U)
    (hcore : U ⊆ ball x f.physicalRadius) (houtput : ∀ y ∈ U, output y = 1)
    (mt : LocalizerSymbol (d+1)) (ht : ContDiff ℝ ∞ mt) (htc : HasCompactSupport mt)
    {lo : ℝ} (hlo : 0 < lo) (hann : ∀ p ∈ tsupport mt, lo ≤ ‖p.2‖)
    (hterminal : ∀ p ∈ tsupport mt, NormedSpace.normalize p.2 ∈ K)
    (n : ℕ) (T R Lout : ℕ → ι → Hu →ₗ[ℝ] Hu) (Mt : ι → H →L[ℂ] H)
    (u : ι → Hu) (ρ L A : ι → ℝ) (σ : ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (hσ : 0 < σ) (hscale : ∀ i, L i ≤ (ρ i)^(1-σ)) (hA : ∀ i, 0 ≤ A i)
    (hMt : ∀ i v, Mt i v =ᵐ[volume] fun y ↦ WithLp.toLp 2
      (rightLocalizer (ρ i) mt (fun z ↦ (v z).ofLp) y))
    (hu : ∃ D a : ℝ, 0 ≤ D ∧ ∀ i, ‖u i‖ ≤ D*A i*(ρ i)^a)
    (hsource : ∀ s, RapidDecayAt G s ρ A (fun i ↦ u i-R 0 i (u i)))
    (hsourceSupport : ∀ i,
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ (u i)) =
      SmallSupport.zeroExtend MeasurableSet.univ (u i))
    (hfactorSupport : ∀ j < n, ∀ i v,
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ v) =
      SmallSupport.zeroExtend MeasurableSet.univ v →
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ (T j i v)) =
      SmallSupport.zeroExtend MeasurableSet.univ (T j i v))
    (hfullLow : ∀ j < n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v, ‖T j i v‖ ≤ D*(ρ i)^c*‖v‖)
    (hlow : ∀ j < n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖T j i (R j i v)‖ ≤ D*(ρ i)^c*‖v‖)
    (hleft : ∀ j < n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖Lout j i v‖ ≤ D*(ρ i)^c*‖v‖)
    (hcost : ∀ j < n, HasPolynomialSobolevCost G G ρ (T j))
    (hfactor : ∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-Lout j i) (T j i (R j i v)) ∈ (G).level s ∧
        (G).gradeNorm s ((1-Lout j i) (T j i (R j i v))) ≤
          C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖)
    (hcross : ∀ j < n, ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-R (j+1) i) (Lout j i v) ∈ (G).level s ∧
        (G).gradeNorm s ((1-R (j+1) i) (Lout j i v)) ≤
          C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖)
    (htleak : ∀ s, ∃ (c : ℝ) (b : ℕ), ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i v,
        (1-(localRetardedOperator MeasurableSet.univ univ (Mt i)).toLinearMap)
          (R n i v) ∈ (G).level s ∧
        (G).gradeNorm s ((1-(localRetardedOperator MeasurableSet.univ univ (Mt i)).toLinearMap)
          (R n i v)) ≤ C*(ρ i)^c*L i^b*(L i/ρ i)^q*‖v‖) :
    ∀ backward : Bool, ∀ s,
      let S := pairedSource f hK L₀ output ho.continuous
        (fun y ↦ (Real.norm_of_nonneg (hor y).1).trans_le (hor y).2)
      let P := if backward then S.adjoint else S
      RapidDecayAt G s ρ A (fun i ↦ restrictL2 univ ((P-1)
        (SmallSupport.zeroExtend MeasurableSet.univ (factorChain T u n i)))) := by
  have halow : ∀ j < 2*n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖alternatingChainFactor T j i (alternatingChainLocalizer R Lout j i v)‖ ≤
        D*(ρ i)^c*‖v‖ := by
    intro j hj
    by_cases he : j%2 = 0
    · simpa only [alternatingChainFactor, alternatingChainLocalizer, he, ite_true]
        using hlow (j/2) (by omega)
    · simpa only [alternatingChainFactor, alternatingChainLocalizer, he, ite_false,
        LinearMap.id_apply] using hleft (j/2) (by omega)
  have hafull : ∀ j < 2*n, ∃ D c : ℝ, 0 ≤ D ∧ ∀ i v,
      ‖alternatingChainFactor T j i v‖ ≤ D*(ρ i)^c*‖v‖ := by
    intro j hj
    by_cases he : j%2 = 0
    · simpa only [alternatingChainFactor, he, ite_true] using hfullLow (j/2) (by omega)
    · exact ⟨1, 0, zero_le_one, fun i v ↦ by simp [alternatingChainFactor, he]⟩
  have hacost : ∀ j < 2*n,
      HasPolynomialSobolevCost G G ρ (alternatingChainFactor T j) := by
    intro j hj
    by_cases he : j%2 = 0
    · have heq : alternatingChainFactor T j = T (j/2) := funext fun _ ↦ ite_eq_left he
      rw [heq]
      exact hcost (j/2) (by omega)
    · have heq : alternatingChainFactor T j = fun _ ↦ LinearMap.id := funext fun _ ↦ ite_eq_right he
      rw [heq]
      exact ResidualLocalization.polynomialCost_identity G ρ
  have haplateau : ∀ j < 2*n, ∀ i v,
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ v) =
      SmallSupport.zeroExtend MeasurableSet.univ v →
      sourceCutMultiplier χ₃ χ₃.continuous (SmallSupport.bump_norm_le_one χ₃)
        (SmallSupport.zeroExtend MeasurableSet.univ (alternatingChainFactor T j i v)) =
      SmallSupport.zeroExtend MeasurableSet.univ (alternatingChainFactor T j i v) := by
    intro j hj i v hv
    by_cases he : j%2 = 0
    · simpa only [alternatingChainFactor, he, ite_true] using hfactorSupport (j/2) (by omega) i v hv
    · simpa only [alternatingChainFactor, he, ite_false, LinearMap.id_apply] using hv
  have h := normalizedSource_finiteChain_observation_rapidDecayAt
    f hK hsym L₀ hL₀ output ho hoc hor χ₃ U hU hχ₃ hcore houtput mt ht htc hlo hann hterminal
    (2*n) (alternatingChainFactor T) (alternatingChainLocalizer R Lout) Mt u ρ L A σ
    hρ hL hLρ hσ hscale hA hMt hu
    (by simpa [alternatingChainLocalizer] using hsource) hsourceSupport haplateau hafull halow hacost
    (alternatingChain_leakage_bounds G T R Lout ρ L n hfactor hcross)
    (by simpa [alternatingChainLocalizer] using htleak)
  simpa only [factorChain_alternatingChainFactor] using h

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
