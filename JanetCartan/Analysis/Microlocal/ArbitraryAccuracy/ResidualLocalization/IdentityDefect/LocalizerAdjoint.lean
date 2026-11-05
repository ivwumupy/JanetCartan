module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.StrongIdentification.BoundedLocalizers

/-!
# Matching the principal input localizer to the terminal adjoint interface

The bounded right localizer chosen by the principal localization theorem is
the adjoint of the original bounded left quantization. This identifies the
SAME input operator for the principal `hleak` and terminal `hBnear` estimates
in `finiteChain_observation_rapidDecayAt`, without choosing new proof masks
(`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)
set_option backward.isDefEq.respectTransparency false

/-- The adjoint of any bounded realization of the original right localizer
has the literal left action. The existing bounded-localizer constructor is
the producer; its all-data right action proves uniqueness. This supplies the
terminal left-action premise with `M = Mi.adjoint`, so `M.adjoint = Mi` for
the SAME input localizer already used by the principal estimate
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem leftLocalizer_adjoint_ae_of_rightLocalizer
    {ρ : ℝ} (hρ : ρ ≠ 0) (mi : LocalizerSymbol n)
    (hi : Continuous mi) (his : HasCompactSupport mi) (Mi : H →L[ℂ] H)
    (hMi : ∀ u : H, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
      (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) :
    ∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → Mi.adjoint u =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x) := by
  obtain ⟨M, hleft, hright⟩ :=
    EvolutionIntegratedLocalization.exists_bounded_physicalLocalizers (q := r) hρ mi hi his
  have he : Mi = M.adjoint := by
    apply ContinuousLinearMap.ext
    intro u
    exact Lp.ext ((hMi u).trans (hright u).symm)
  simpa only [he, ContinuousLinearMap.adjoint_adjoint] using hleft

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
