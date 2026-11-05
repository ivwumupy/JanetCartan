module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.Neighborhoods

/-!
# The actual local chart with its joint coefficient root

The root, flow producer and masks are chosen together, before finite selection.
The extra coefficient facts are proved outputs for these witnesses; they are
not asserted for arbitrary `LocalChart` values. Consumer: the compact algebraic
buffers in `app:ch_regular_base:eq:complement-inverse`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicChart
open ActualCarriers UniformAmplitudes FiniteMasks.ActualFamily RootFamily AmplitudeBounds
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => MetricTensor (d + 1)

/-- Construct the local chart with the stronger uniform producer, preserving
its radius comparisons on the same root, section, masks and varying-field
evolution. These are proved conclusions, before any finite selection.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_localChart_with_algebraic_data
    {Ω : Set E} (hΩ : IsOpen Ω) (x : E) {RQ : ℝ}
    (hRQ : 0 < RQ) (hKΩ : closedBall x RQ ⊆ Ω)
    (A₀ : Fin (d + 1) → Mat) (ξ : E)
    (hξ : ξ ≠ 0) (hp : determinant A₀ ξ = 0)
    (hreg : fderiv ℝ (determinant A₀) ξ ≠ 0) {M : ℝ} (hM : 0 ≤ M) :
    ∃ c : LocalChart Ω x RQ A₀ ξ M,
      c.bufferRadius ≤ c.targetRadius ∧ c.maskRadius ≤ c.bufferRadius / 4 ∧
      RootBuffer c.index c.row c.col A₀ ξ c.root c.coefficientRadius c.rootRadius
        c.minorGap c.transportGap ∧
      MapsTo (rootPhysicalPosition (coordinateSplit c.index)) (tsupport c.sourceMask)
        (closedBall x RQ) := by
  obtain ⟨r, c, hm⟩ := exists_nonzero_adjugate_entry_of_regular A₀ ξ hreg
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost, hℓ, halgebraic, haL, hrootPhys,
    σ, κ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, hevolution⟩ :=
    exists_uniform_supported_conic_pencilAmplitudes_with_algebraic_data hΩ x hRQ hKΩ
      A₀ ξ r c hξ hp hreg hm hM
  refine ⟨⟨i, r, c, hm, ℓ, H, ε, L, a, b, ρ, ρo, src, μ, ν,
    phaseCost, σ, κ, hε, hL, ha, hb, hρ, hρo, hsrc, hsrca, hμ, hν,
    hphaseCost, hℓ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ,
    hevolution⟩, hρb, hsrcρ, halgebraic, ?_⟩
  intro w hw
  apply hrootPhys
  apply closedBall_subset_closedBall (show src / 2 ≤ L by linarith)
  exact ball_subset_closedBall (hsσ hw)

end JanetCartan.RegularSector.Characteristic.AlgebraicChart
