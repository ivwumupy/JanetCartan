module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.Neighborhoods
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformAmplitudes.ProtectionCertificates

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

/-- Protection data for a constructed local chart. The complete supported
amplitude conclusion occurs inside `UniformProtectionEvolution`, on the same
flow and inverse as its bounds. The producer below discharges every field
from the original frozen pencil and physical coefficient bounds; no arbitrary
`LocalChart` is claimed to have this property. Consumer: the finite protection
export, then `SelectedSectorProtection.exists_selectedSector_nested_proof_masks`
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
def LocalProtectionCertificate
    {Ω : Set E} {x : E} {RQ : ℝ} {A₀ : Fin (d + 1) → Mat} {ξ : E} {M : ℝ}
    (c : LocalChart Ω x RQ A₀ ξ M)
    (evolutionTime speedGap rootSize : ℝ) (rootCost : ℕ → ℝ) : Prop :=
  let e := coordinateSplit c.index
  let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e ξ).2))
  0 < evolutionTime ∧ 0 < speedGap ∧ 0 < rootSize ∧ (∀ m, 0 < rootCost m) ∧
  2 * c.sourceRadius ≤ c.rootRadius / 4 ∧
  2 * c.sourceRadius ≤ evolutionTime / 4 ∧
  closedBall (z.1, z) (2 * c.sourceRadius) ⊆
    twoTimeDomain z (c.rootRadius / 2) evolutionTime ∧
  c.sourceRadius < c.rootRadius ∧
  (∀ w ∈ closedBall z c.rootRadius,
    w ∈ fieldDomain e Ω c.radialSection z.2.2 c.coefficientRadius ∧
    rootPhysicalPosition e w ∈ closedBall x RQ ∧
    w.2.2 ∈ closedBall z.2.2 c.coefficientRadius ∧
    (1 / 2 : ℝ) ≤ c.radialSection w.2.2) ∧
  UniformProtectionEvolution Ω x RQ A₀ ξ M c.index c.row c.col c.radialSection c.root
    c.coefficientRadius c.rootRadius c.sourceRadius c.targetRadius c.bufferRadius
    c.outerRadius c.maskRadius c.minorGap c.transportGap c.phaseCost rootCost
    evolutionTime speedGap rootSize c.sourceMask c.timeMask

/-- Construct the local chart with the stronger uniform producer, preserving
its radius comparisons on the same root, section, masks and varying-field
evolution. These are proved conclusions, before any finite selection.
Source: `app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`,
`app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_localChart_with_protection_certificates
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
        (closedBall x RQ) ∧
      ∃ evolutionTime speedGap rootSize rootCost,
        LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost := by
  obtain ⟨r, c, hm⟩ := exists_nonzero_adjugate_entry_of_regular A₀ ξ hreg
  obtain ⟨i, ℓ, H, ε, hε, L, hL, a, ha, b, hb, ρ, hρ, ρo, hρo,
    src, hsrc, hsrca, hρb, hsrcρ, μ, hμ, ν, hν, phaseCost, hphaseCost, rootCost, hrootCost,
    evolutionTime, hevolutionTime, speedGap, hspeedGap, rootSize, hrootSize,
    haR, haT, htimeDomain, hℓ, halgebraic, haL, hrootPhys, hwholeState,
    σ, κ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ, hevolution⟩ :=
    exists_uniform_supported_conic_pencilAmplitudes_with_protection_certificates hΩ x hRQ hKΩ
      A₀ ξ r c hξ hp hreg hm hM
  refine ⟨⟨i, r, c, hm, ℓ, H, ε, L, a, b, ρ, ρo, src, μ, ν,
    phaseCost, σ, κ, hε, hL, ha, hb, hρ, hρo, hsrc, hsrca, hμ, hν,
    hphaseCost, hℓ, hσ, hκ, hσr, hκr, hcσ, hcκ, hsσ, hsκ, hpσ, hpκ,
    hevolution.toUniformChartEvolution⟩, hρb, hsrcρ, halgebraic, ?_,
    evolutionTime, speedGap, rootSize, rootCost,
    hevolutionTime, hspeedGap, hrootSize, hrootCost, haR, haT, htimeDomain,
    haL, hwholeState, hevolution⟩
  intro w hw
  apply hrootPhys
  apply closedBall_subset_closedBall (show src / 2 ≤ L by linarith)
  exact ball_subset_closedBall (hsσ hw)

end JanetCartan.RegularSector.Characteristic.AlgebraicChart
