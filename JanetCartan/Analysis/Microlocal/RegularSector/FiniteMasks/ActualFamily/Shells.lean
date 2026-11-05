module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.CoordinateCollars

/-!
# Actual chart shell covers in the original physical coordinates

Apply `DilatedShellCover` to the literal original right multiplier and the
actual selected physical/angular domains. The common enlarged collar keeps
both normalization inequalities with constant one, without identifying
cutoff profiles in different coordinate systems.
Consumer: the signed retarded constructor in `app:ch_regular_base:lem:retarded-kernel`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open Characteristic Characteristic.ResidualCoordinates
open FourierIntegral.PrimitiveProfiles
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => (E × E) × E
variable {Ω : Set (Euclidean (d + 1))} {x ξ : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)}

namespace LocalChart

/-- The selected open shell domain in the ORIGINAL physical coordinates.
Both positions and the frequency are restricted by the actual chart
construction (`retarded-kernel`). -/
def shellDomain (c : LocalChart Ω x RQ A₀ ξ M) : Set P :=
  (c.physicalNeighborhood ×ˢ c.physicalNeighborhood) ×ˢ c.angularNeighborhood

/-- The actual shell domain is open (`retarded-kernel`). -/
theorem isOpen_shellDomain (c : LocalChart Ω x RQ A₀ ξ M) : IsOpen c.shellDomain :=
  (c.isOpen_physicalNeighborhood.prod c.isOpen_physicalNeighborhood).prod
    c.isOpen_angularNeighborhood

/-- Positive scaling preserves the actual physical angular neighborhood
(`thm:sector`). -/
theorem smul_mem_angularNeighborhood (c : LocalChart Ω x RQ A₀ ξ M)
    {ζ : E} (hζ : ζ ∈ c.angularNeighborhood) {r : ℝ} (hr : 0 < r) :
    r • ζ ∈ c.angularNeighborhood := by
  change (coordinateSplit c.index (r • ζ)).2 ∈ c.spatialCone
  simpa only [map_smul, Prod.smul_snd] using c.smul_mem_spatialCone hζ hr

/-- The actual compact normalized carrier lies in its selected open chart.
This discharges the shell-cover premise from the constructed masks
(`retarded-kernel`). -/
theorem normalizedMaskCarrier_subset_shellDomain (c : LocalChart Ω x RQ A₀ ξ M)
    {X : Set (E × E)} (hX : X ⊆ c.physicalNeighborhood ×ˢ c.physicalNeighborhood)
    {χ : E → ℝ} (hχ : tsupport χ ⊆ c.angularNeighborhood) :
    normalizedMaskCarrier X χ ⊆ c.shellDomain := by
  rintro p ⟨hp, ⟨⟨r, ζ⟩, ⟨hr, hζ, _⟩, he⟩⟩
  refine ⟨hX hp, ?_⟩
  rw [← he]
  exact c.smul_mem_angularNeighborhood (hχ hζ) (by linarith [hr.1])

/-- Construct the finite shell cover for the actual enlarged physical collar.
The source/output mask owner supplies its literal compact position support;
its containment in this chart is already proved by the common physical-ball
construction. Both scale inequalities have constant ONE (`retarded-kernel`). -/
theorem exists_dilated_shell_cover (c : LocalChart Ω x RQ A₀ ξ M)
    {X : Set (E × E)} (hX : IsCompact X)
    (hXchart : X ⊆ c.physicalNeighborhood ×ˢ c.physicalNeighborhood)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsχ : tsupport χ ⊆ c.angularNeighborhood) :
    ∃ (s : Finset (normalizedMaskCarrier X χ)) (ρ : normalizedMaskCarrier X χ → ℝ),
      (∀ p, 0 < ρ p) ∧
      (∀ p ∈ s, closedBall (p : P) (ρ p) ⊆ c.shellDomain) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ p ∈ s, ∀ m,
        BoundedNormalizedSeminorm (closedBall (p : P) (ρ p)) m
          (fun z : P ↦ (dilatedConicMask χ L z.2 : ℂ))) ∧
      ∀ L : ℝ, 1 ≤ L →
        ∀ p ∈ X ×ˢ tsupport (fun ζ ↦ (dilatedConicMask χ L ζ : ℂ)),
          ∃ q ∈ s, ∃ R : ℝ, 1 ≤ R ∧ ∃ v ∈ closedBall (q : P) (ρ q),
            p = (v.1, R • v.2) ∧ 1 + ‖p.2‖ ≤ R ∧ R ≤ 1 * (1 + ‖p.2‖) :=
  exists_finite_dilatedConicMask_shell_cover hX hχ c.isOpen_shellDomain
    (c.normalizedMaskCarrier_subset_shellDomain hXchart hsχ)

end LocalChart
end JanetCartan.RegularSector.FiniteMasks.ActualFamily
