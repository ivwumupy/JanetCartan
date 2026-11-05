module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.SupportedMajorants
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.JetBounds.Normalized
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry.Mixed

/-!
# Transfer of the interior gap to the normalized supported phase

Positive normalization fixes the actual conic phase. Its joint germ on the
local overlap is supplied by `UniformGeometry.exists_uniform_fieldRoot_conicGeometry`,
or directly by `ConicPhase.phase_eventuallyEq_on_overlap`. Pullback preserves
the FULL elapsed derivative, not just the five fixed-time derivatives.

The final localization assembly must still put each supported point in that
overlap (or produce the same germ for its actual chart). The local chart gap
alone does not assert a gap everywhere on the unbounded conic continuation.
For a supported smooth replacement, the second theorem additionally uses its
actual two-time germ at the dilated point, as supplied by `SupportedPhase`.
Consumer: the normalized kernel estimate in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph JanetCartan.Localization

variable {d : ℕ}

/-- The actual normalized conic phase has the same full squared-gradient
as the original chart on their joint open overlap. The germ is the overlap
conclusion of `UniformGeometry`, not a presumed derivative gap
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:joint-stationary`). -/
theorem phaseGradientSquare_normalized_conic_eq_of_germ
    {κ : Type*} [Fintype κ] (eI : κ → ℝ × JointVariables (Euclidean (d + 1)))
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    {ρ : ℝ} (hρ : 0 < ρ) (backward : Bool) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hlocal : ConicPhase.phase ℓ C =ᶠ[𝓝 (elapsedChartPoint p.1 p.2.1.1 p.2.2.1)]
      twoTimePhase C) :
    phaseGradientSquare eI
      (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ
        (ConicPhase.curriedPhase ℓ C)) x y) p =
      phaseGradientSquare eI (jointElapsedPhase backward (chartPhase C) x y) p := by
  have hn : SymbolBudgets.normalizedTwoTimePhase ρ (ConicPhase.curriedPhase ℓ C) =
      ConicPhase.curriedPhase ℓ C :=
    ConicPhase.normalizedTwoTimePhase_curriedExtend ℓ (twoTimePhase C) hρ
  rw [hn]
  have hbudget : SymbolBudgets.jointPhase (ConicPhase.curriedPhase ℓ C) =ᶠ[
      𝓝 (elapsedJointCoordinates p)] SymbolBudgets.jointPhase (chartPhase C) :=
    hlocal.comp_tendsto (ConicPhase.budgetCoordinates.continuous.tendsto (elapsedJointCoordinates p))
  have he := jointElapsedPhase_eventuallyEq_of_twoTimePhase backward (chartPhase C)
    (ConicPhase.curriedPhase ℓ C) x y p hbudget
  simp only [phaseGradientSquare, he.fderiv_eq]

/-- A supported smooth replacement preserves the same normalized interior
gap. Its germ is required at the actual dilated frequency, while the conic
overlap germ is at the normalized integration point. These are distinct
obligations of the actual kernel assembly (`app:ch_regular:eq:chain-tail`). -/
theorem phaseGradientSquare_normalized_supported_eq_of_germs
    {κ : Type*} [Fintype κ] (eI : κ → ℝ × JointVariables (Euclidean (d + 1)))
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d)))
    (Ψ : TwoTimePhase d) {ρ : ℝ} (hρ : 0 < ρ)
    (backward : Bool) (x y : Euclidean (d + 1))
    (p : ℝ × JointVariables (Euclidean (d + 1)))
    (hlocal : ConicPhase.phase ℓ C =ᶠ[𝓝 (elapsedChartPoint p.1 p.2.1.1 p.2.2.1)]
      twoTimePhase C)
    (hext : SymbolBudgets.jointPhase Ψ =ᶠ[
      𝓝 ((elapsedJointCoordinates p).1, ρ • (elapsedJointCoordinates p).2)]
        SymbolBudgets.jointPhase (ConicPhase.curriedPhase ℓ C)) :
    phaseGradientSquare eI
      (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y) p =
      phaseGradientSquare eI (jointElapsedPhase backward (chartPhase C) x y) p := by
  have hn := normalizedTwoTimePhase_eventuallyEq_of_germ ρ
    (ConicPhase.curriedPhase ℓ C) Ψ (elapsedJointCoordinates p) hext
  have he := jointElapsedPhase_eventuallyEq_of_twoTimePhase backward
    (SymbolBudgets.normalizedTwoTimePhase ρ (ConicPhase.curriedPhase ℓ C))
    (SymbolBudgets.normalizedTwoTimePhase ρ Ψ) x y p hn
  calc
    _ = phaseGradientSquare eI
        (jointElapsedPhase backward (SymbolBudgets.normalizedTwoTimePhase ρ
          (ConicPhase.curriedPhase ℓ C)) x y) p := by
      simp only [phaseGradientSquare, he.fderiv_eq]
    _ = _ := phaseGradientSquare_normalized_conic_eq_of_germ eI ℓ C hρ backward x y p hlocal

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
