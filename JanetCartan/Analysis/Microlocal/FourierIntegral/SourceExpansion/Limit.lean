module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.Realization
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SourceExpansion.LiteralLimit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Identifying the source-series limit with the literal full graph

The final assembly for `app:ch_regular_base:thm:actual-calculus`, Step 1, needs
pointwise convergence of the full literal test integrals when the frequency
cutoff is removed. The source-series construction already supplies strong L²
convergence. This file proves their compatibility without assuming a full graph
bound, then discharges pointwise convergence using the fixed source derivative
reserve and a bounded exhausting frequency cutoff.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SourceExpansion
open AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Strong L² convergence of the constructed regularizations identifies their
limit with the original literal full-amplitude test action, once source
integration by parts supplies pointwise cutoff removal. Consumer: the final
literal realization of `exists_sourceFourierExpansion`, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem graphTestOutput_eq_of_strong_regularization_limit
    (S : E → E → ℝ) (A : FullAmplitude n r) (θ : ℕ → E → ℂ)
    (T : H →L[ℂ] H) (Treg : ℕ → H →L[ℂ] H) (u : graphTestSpace n r)
    (hreal : ∀ j, Treg j (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x y η ↦ θ j η • A x y η) u)
    (hstrong : Tendsto (fun j ↦ Treg j (graphTestToLp u)) atTop
      (𝓝 (T (graphTestToLp u))))
    (hliteral : ∀ᵐ x ∂volume,
      Tendsto (fun j ↦ graphTestOutput S (fun x y η ↦ θ j η • A x y η) u x)
        atTop (𝓝 (graphTestOutput S A u x))) :
    T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u := by
  obtain ⟨s, hs, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hstrong).exists_seq_tendsto_ae
  filter_upwards [hsub, hliteral, ae_all_iff.mpr hreal] with x hx hl he
  apply tendsto_nhds_unique hx
  apply (hl.comp hs.tendsto_atTop).congr
  intro j
  exact (he (s j)).symm

/-- The full literal test identification with pointwise cutoff removal proved
from primitive amplitude derivatives. No full graph estimate or full-amplitude
convergence is an analytic input. Consumer: `exists_literalSourceFourierExpansion`
in `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem graphTestOutput_eq_of_strong_source_regularization_limit
    (hn : 0 < n) {R : ℝ} (A : FullAmplitude n r)
    (hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (μ : ℕ) {B : ℝ} (hb : HasFullSourceSymbolBound A (μ + lowReserve n) B)
    (S : E → E → ℝ) (hS : ContDiff ℝ ∞ (Function.uncurry S))
    (θ : ℕ → E → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hθc : ∀ j, HasCompactSupport (θ j)) (hθb : ∀ j η, ‖θ j η‖ ≤ 1)
    (hθlim : ∀ η, Tendsto (fun j ↦ θ j η) atTop (𝓝 1))
    (T : H →L[ℂ] H) (Treg : ℕ → H →L[ℂ] H) (u : graphTestSpace n r)
    (hreal : ∀ j, Treg j (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S (fun x y η ↦ θ j η • A x y η) u)
    (hstrong : Tendsto (fun j ↦ Treg j (graphTestToLp u)) atTop
      (𝓝 (T (graphTestToLp u)))) :
    T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u :=
  graphTestOutput_eq_of_strong_regularization_limit S A θ T Treg u hreal hstrong
    (Eventually.of_forall (tendsto_graphTestOutput_frequency_cutoff hn A hs hA μ hb
      S hS θ hθ hθc hθb hθlim u))

end JanetCartan.FourierIntegral.SourceExpansion
