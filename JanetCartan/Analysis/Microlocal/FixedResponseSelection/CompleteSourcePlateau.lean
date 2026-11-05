module

public import JanetCartan.Analysis.Microlocal.FixedResponseSelection.TerminalGeometry
public import JanetCartan.Analysis.Microlocal.NormalizedRegularSolver.AngularMask

/-!
# The literal completed source on the protected terminal collar

The outer compact from the relative no-return geometry is the actual finite
selector's compact. Its geometric collar is chosen before the family and gives
a plateau of the literal normalized characteristic-plus-elliptic source, with
its unchanged doubled radial cutoff. No angular plateau is an input.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.NormalizedSolver
open FiniteMasks FiniteMasks.ActualFamily EllipticComplement
open FourierIntegral.LowBounds.FrequencyCutoff

/-- The actual completed mask is one on every protected outer buffer.
This applies the proved full-source partition to the same `f`; only the
geometric outer inclusion is supplied by terminal no-return protection
(`resolved-angular-tail`, `app:ch_regular:lem:finite-chain`). -/
theorem complete_source_plateau_on_outer_terminal_buffer
    {d : ℕ} {Γout : Set (Euclidean (d+1))} (hout : IsCompact Γout)
    (hsym : ∀ ξ ∈ Γout, -ξ ∈ Γout)
    {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
    {A₀ : Fin (d+1) → MetricTensor (d+1)}
    (f : ActualMaskFamily Ω x RQ A₀ Γout M)
    {ξ : Euclidean (d+1)} {θ : ℝ}
    (hbuffer : closedBall ξ θ ∪ closedBall (-ξ) θ ⊆ interior Γout) :
    (closedBall ξ θ ∪ closedBall (-ξ) θ ⊆
      interior {η | gammaTotal f hout η = 1}) ∧
    ∀ L > (0 : ℝ), ∀ ζ : Euclidean (d+1),
      NormedSpace.normalize ζ ∈ closedBall ξ θ ∪ closedBall (-ξ) θ →
      normalizedSourceMask f hout L ζ + physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1 ∧
      (4*L ≤ ‖ζ‖ → normalizedSourceMask f hout L ζ = 1) := by
  have hone : Γout ⊆ {η | gammaTotal f hout η = 1} := by
    intro η hη
    have hp : fullSourceAngularMask f hout η = 1 :=
      interior_subset (s := {η | fullSourceAngularMask f hout η = 1})
        ((fullSourceAngularMask_properties f hout).2.2 hη)
    have hn : fullSourceAngularMask f hout (-η) = 1 :=
      interior_subset (s := {η | fullSourceAngularMask f hout η = 1})
        ((fullSourceAngularMask_properties f hout).2.2 (hsym η hη))
    norm_num [gammaTotal, hp, hn]
  obtain ⟨V, _, hΓV, _, hpartition⟩ :=
    exists_normalizedSourceMask_partition_near f hout (Subset.rfl : Γout ⊆ Γout) hsym
  refine ⟨hbuffer.trans (interior_mono hone), ?_⟩
  intro L hL ζ hζ
  exact hpartition L hL ζ (hΓV (interior_subset (hbuffer hζ)))

/-- A single geometric collar precedes the selected family and lies in the
unit plateau of its actual completed normalized source at both terminal signs.
The original `2*L` radial collar is retained, including its low shoulder and
exact high-frequency threshold (`resolved-angular-tail`,
`app:ch_regular:lem:finite-chain`, `sector-theorem-identity`). -/
theorem exists_uniform_complete_source_terminal_plateau
    {d : ℕ} (hd : 5 ≤ d+1) {Γin Γout : Set (Euclidean (d+1))}
    (hin : IsCompact Γin) (hout : IsCompact Γout)
    (hnest : Γin ⊆ interior Γout) (hsym : ∀ ξ ∈ Γout, -ξ ∈ Γout)
    (hbad : Γout ⊆ (cubeBadSubspaceUnion (d+1))ᶜ) :
    ∃ θ > (0 : ℝ),
      ∀ {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
        {A₀ : Fin (d+1) → MetricTensor (d+1)}
        (f : ActualMaskFamily Ω x RQ A₀ Γout M),
      ∀ ξ ∈ Γin,
        (closedBall ξ θ ∪ closedBall (-ξ) θ ⊆
          interior {η | gammaTotal f hout η = 1}) ∧
        ∀ L > (0 : ℝ), ∀ ζ : Euclidean (d+1),
          NormedSpace.normalize ζ ∈ closedBall ξ θ ∪ closedBall (-ξ) θ →
          normalizedSourceMask f hout L ζ + physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1 ∧
          (4*L ≤ ‖ζ‖ → normalizedSourceMask f hout L ζ = 1) := by
  obtain ⟨_, _, aperture, _, _, θ, hθ, hbuffer⟩ :=
    ProtectedFlow.protected_terminal_compact_selection_data hd hin hout hnest hsym hbad
  refine ⟨θ, hθ, ?_⟩
  intro Ω x RQ M A₀ f ξ hξ
  exact complete_source_plateau_on_outer_terminal_buffer hout hsym f
    (union_subset (hbuffer ξ hξ).1 (hbuffer ξ hξ).2)

end JanetCartan.RegularSector.NormalizedSolver
