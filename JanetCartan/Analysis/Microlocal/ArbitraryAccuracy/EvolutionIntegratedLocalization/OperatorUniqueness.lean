module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.IdentifiedSobolev

/-!
# Accuracy-independent realizations of the literal localizers

The physical representative identities determine the bounded localizers
uniquely, including the left identity that is stated only on integrable
inputs. This keeps the operators fixed when the integration-by-parts accuracy
changes in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph KernelLimits
open RegularSector.Characteristic.EvolutionIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "H" => SpacetimeL2 d q

/-- The literal right-localizer representative fixes its bounded realization
uniquely (`app:ch_regular:eq:chain-tail`). -/
theorem eq_of_rightLocalizer_representatives
    (ρ : ℝ) (mi : LocalizerSymbol (d + 1)) (T U : H →L[ℂ] H)
    (hT : ∀ u : H, T u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x))
    (hU : ∀ u : H, U u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) : T = U := by
  apply ContinuousLinearMap.ext
  intro u
  exact Lp.ext ((hT u).trans (hU u).symm)

/-- Integrable physical tests determine the literal left localizer. Its
bounded realization consequently cannot vary with requested accuracy
(`app:ch_regular:eq:chain-tail`). -/
theorem eq_of_leftLocalizer_representatives
    (ρ : ℝ) (mo : LocalizerSymbol (d + 1)) (T U : H →L[ℂ] H)
    (hT : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → T u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x))
    (hU : ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → U u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mo (fun y ↦ (u y).ofLp) x)) : T = U := by
  apply DFunLike.coe_injective
  apply denseRange_graphTestToLp.equalizer T.continuous U.continuous
  funext u
  have hint : ∀ i, Integrable (fun y ↦ graphTestToLp u y i) := by
    intro i
    have hval := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) i).integrable_comp
      (u.property.1.continuous.integrable_of_hasCompactSupport (μ := volume) u.property.2)
    apply hval.congr
    filter_upwards [(graphTest_memLp u).coeFn_toLp] with y hy
    exact congrArg (fun v : EuclideanSpace ℂ (Fin q) ↦ v i) hy.symm
  exact Lp.ext ((hT _ hint).trans (hU _ hint).symm)

end JanetCartan.ArbitraryAccuracy.EvolutionIntegratedLocalization
