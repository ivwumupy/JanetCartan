module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Energy
public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces.Duality

/-!
# Integer Sobolev completions for retarded integration

Functional spaces for `app:ch_osc:setup:osc-retarded` and
`app:ch_osc:prop:osc-retarded-tube` of `paper.tex`.

The nonnegative spaces close the actual smooth compactly supported Cartesian
L² jet image. Tests embed densely and, for volume, injectively. The product norm
and classical derivative energy have explicit comparison constants. On strips,
that energy is exactly the coordinate specialization of `mixedSobolevEnergy`.
Classical linear operators with a derivative-energy estimate extend uniquely.

Supported spaces close tests supported inside an open set. Restriction spaces
quotient the ambient completion by the kernel of local L² restriction. Negative
spaces are the reversed continuous dual pairs. A transpose agrees with a literal
adjoint only under the exact smooth L² pairing identity given in `Duality`.

This construction does not assert an identification with distributions or Fourier
Sobolev spaces. Estimates for the concrete `Retarded.lower` and `Retarded.upper`
are supplied by the caller, not assumed as properties of these spaces.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RetardedSobolev.Spaces

/-- The ambient nonnegative integer Sobolev space on ℝ × ℝᵈ, constructed from
actual L² derivatives (`app:ch_osc:prop:osc-retarded-tube`). -/
abbrev Ambient (d m : ℕ) := Sobolev m (volume : Measure ((Fin d → ℝ) × ℝ))

/-- The ambient inclusion is injective (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem ambient_ofTest_injective (d m : ℕ) :
    Function.Injective (ofTest m (volume : Measure ((Fin d → ℝ) × ℝ))) :=
  ofTest_injective m volume

/-- A classical derivative-energy estimate yields a unique bounded operator on
the completions (`app:ch_osc:prop:osc-retarded-tube`). The explicit finite-index
factor only converts the sum norm to the finite product norm. -/
theorem exists_unique_extension_of_energy_bound {d e m n : ℕ}
    (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (T : Test d →ₗ[ℂ] Test e) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ f, jetEnergy n ν (T f) ≤ C * jetEnergy m μ f) :
    ∃ A : Sobolev m μ →L[ℂ] Sobolev n ν,
      ‖A‖ ≤ Real.sqrt (C * (Fintype.card (JetIndex d m) : ℝ)) ∧
      (∀ f, A (ofTest m μ f) = ofTest n ν (T f)) ∧
      ∀ B : Sobolev m μ →L[ℂ] Sobolev n ν,
        (∀ f, B (ofTest m μ f) = ofTest n ν (T f)) → B = A :=
  exists_unique_bounded_extension μ ν T (Real.sqrt_nonneg _)
    (jetMap_bound_of_energy_bound μ ν T hC hT)

end JanetCartan.RetardedSobolev.Spaces
