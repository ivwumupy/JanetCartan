module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.SymbolCancellation
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ShellCover
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.UncutTestAction.MultiplierBudget

/-!
# Schwartz regularity of the original terminal symbol

The finite shell-cover and normalized-mask producers imply temperate growth
of the actual fixed conic masks, including their low-frequency collars.
Consumer: the bounded Fourier realization of the full terminal identity
defect in `app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral RegularSector.FiniteMasks
open RegularSector.Characteristic.EvolutionIntegral.UncutTestAction

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- The original collared conic symbol preserves Schwartz functions. All
derivative bounds come from the fixed angular mask and its constructed finite
shell cover, with no additional symbol-class assumption. Consumer: terminal
Fourier realization in `app:ch_regular:eq:resolved-angular-tail`. -/
theorem hasTemperateGrowth_complex_conicMask {a : E → ℝ}
    (ha : ContDiff ℝ ∞ a) :
    (fun ξ ↦ (conicMask a ξ : ℂ)).HasTemperateGrowth := by
  classical
  obtain ⟨s, δ, _, _, hbud, hcover⟩ := exists_finite_conicMask_shell_cover
    (X := {(0 : E × E)}) isCompact_singleton ha isOpen_univ (subset_univ _)
  apply hasTemperateGrowth_multiplier_of_normalized_budgets
    (fun p : s ↦ p.val.val) (fun p : s ↦ δ p.val)
    (fun ξ ↦ (conicMask a ξ : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_conicMask ha))
  · intro ξ hξ
    obtain ⟨p, hp, R, hR, v, hv, he, _⟩ := hcover ((0 : E × E), ξ)
      ⟨mem_singleton 0, hξ⟩
    exact ⟨⟨p, hp⟩, R, hR, v, hv, congrArg Prod.snd he⟩
  · intro k p
    exact hbud p.val p.property k

/-- The same fixed radial dilation has temperate growth at every derivative
order, including the original bounded-frequency modification. Consumer:
the actual finite angular multiplier in `app:ch_regular:eq:chain-tail`. -/
theorem hasTemperateGrowth_complex_dilatedConicMask {a : E → ℝ}
    (ha : ContDiff ℝ ∞ a) (R : ℝ) :
    (fun ξ ↦ (dilatedConicMask a R ξ : ℂ)).HasTemperateGrowth :=
  (hasTemperateGrowth_complex_conicMask ha).comp
    ((R⁻¹ • ContinuousLinearMap.id ℝ E).hasTemperateGrowth)

/-- The original finite angular symbol has the Schwartz regularity needed
to identify its bounded Fourier realization. Its producer is the actual
finite family's smooth masks, not a hypothesized localized estimate
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem actualFamily_angularSymbol_hasTemperateGrowth
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω x RQ A₀ K M) :
    (fun ξ ↦ ((∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ : ℝ) : ℂ)).HasTemperateGrowth := by
  simpa only [Complex.ofReal_sum] using Function.HasTemperateGrowth.sum
    (s := Finset.univ) (fun p _ ↦ hasTemperateGrowth_complex_dilatedConicMask
      (f.angularMask_smooth p) f.radialThreshold)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
