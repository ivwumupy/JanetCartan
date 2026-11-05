module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.ShellCoverage

/-!
# The frequency inclusion retained by the physical construction

Consumer: the same-band amplitude input of
`EndpointPdoBounds.exists_supported_endpoint_pdo_budgets` for the literal
upper endpoint in `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.RegularSector.FinitePdo.RetainedConstruction
open Characteristic Characteristic.ConicPhase Characteristic.EvolutionIntegral
variable {d : ℕ}

/-- Normalize every frequency in the exact multiplier support into the
amplitude's radial band, retaining the norm comparison needed by the endpoint
PDO (`app:ch_regular_base:eq:fixed-time-representation`). -/
def DiagonalFrequencyCoverage (ℓ : Euclidean d →L[ℝ] ℝ)
    (η₀ : Euclidean d) (ε a b : ℝ) (β : Euclidean (d+1) → ℂ) : Prop :=
  ∀ ζ ∈ tsupport β, ∃ R : ℝ, 1 ≤ R ∧
    ∃ η ∈ radialSectionBand ℓ η₀ ε a b,
      spatialPart ζ = R • η ∧ ‖spatialPart ζ‖ ≤ R

/-- The primitive cover survives the precise radial and buffer enlargements
used by the physical retarded constructor (`fixed-time-representation`). -/
theorem DiagonalFrequencyCoverage.mono
    {ℓ : Euclidean d →L[ℝ] ℝ} {η₀ : Euclidean d}
    {ε ε' a a' b b' : ℝ} {β : Euclidean (d+1) → ℂ}
    (h : DiagonalFrequencyCoverage ℓ η₀ ε a b β)
    (hε : ε ≤ ε') (ha : a' ≤ a) (hb : b ≤ b') :
    DiagonalFrequencyCoverage ℓ η₀ ε' a' b' β := by
  intro ζ hζ
  obtain ⟨R, hR, η, ⟨v, ⟨hv, hθ, hℓ⟩, he⟩, hη, hnorm⟩ := h ζ hζ
  exact ⟨R, hR, η, ⟨v, ⟨⟨ha.trans hv.1, hv.2.trans hb⟩,
    closedBall_subset_closedBall hε hθ, hℓ⟩, he⟩, hη, hnorm⟩

end JanetCartan.RegularSector.FinitePdo.RetainedConstruction
