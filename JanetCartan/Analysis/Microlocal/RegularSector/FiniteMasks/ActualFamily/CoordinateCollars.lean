module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.Collars

/-!
# One physical radial threshold across different transverse coordinates

The cutoff profile is an abstract smooth bump; invariance under coordinate
permutations is not assumed. Doubling the selected radial threshold puts the
full pulled-back physical multiplier support inside the canonical multiplier's
support. Thus the existing spatial plateau applies while the original physical
masks retain their exact common low-frequency partition.
Consumer: `app:ch_regular_base:prop:complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.RegularSector.FiniteMasks.ActualFamily
open Characteristic Characteristic.ResidualCoordinates CompatibleResponse
open FourierIntegral.LowBounds.FrequencyCutoff
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- The selected coordinate permutation preserves the Euclidean norm;
this follows from its proved Fourier pairing (`finite-calculus`). -/
theorem norm_physicalCoordinates (i : Fin (d + 1)) (ζ : E) :
    ‖physicalCoordinates i ζ‖ = ‖ζ‖ := by
  rw [norm_eq_sqrt_real_inner, physicalCoordinates_inner, ← norm_eq_sqrt_real_inner]

/-- Unit normalization commutes with the actual coordinate permutation,
including at zero (`finite-calculus`). -/
theorem normalize_physicalCoordinates (i : Fin (d + 1)) (ζ : E) :
    NormedSpace.normalize (physicalCoordinates i ζ) =
      physicalCoordinates i (NormedSpace.normalize ζ) := by
  simp only [NormedSpace.normalize, norm_physicalCoordinates, map_smul]

/-- Exact factorization of the original physical multiplier at twice the
canonical threshold. The extra factor is kept literally; no rotational
invariance of the chosen bump profile is used (`prop:complete-residual`). -/
theorem dilatedConicMask_physicalCoordinates_factor
    (χ : E → ℝ) (i : Fin (d + 1)) {L : ℝ} (hL : 0 < L) (ζ : E) :
    dilatedConicMask χ (2 * L) (physicalCoordinates i ζ) =
      (1 - physicalCutoff 0 ((2 * L)⁻¹ • physicalCoordinates i ζ)) *
        dilatedConicMask (χ ∘ physicalCoordinates i) L ζ := by
  by_cases hz : ‖ζ‖ ≤ 2 * L
  · have hb : ‖(2 * L)⁻¹ • physicalCoordinates i ζ‖ ≤ radius 0 := by
      rw [norm_smul, norm_physicalCoordinates,
        Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
      simp only [radius, Nat.cast_zero, zero_add]
      exact (inv_mul_le_iff₀ (by positivity : 0 < 2 * L)).mpr (by simpa using hz)
    simp only [dilatedConicMask, conicMask, physicalCutoff_eq_one 0 hb, sub_self, zero_mul]
  · have hnorm : 2 ≤ ‖L⁻¹ • ζ‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hL.le)]
      exact (le_inv_mul_iff₀ hL).mpr (by linarith)
    change (1 - physicalCutoff 0 ((2 * L)⁻¹ • physicalCoordinates i ζ)) *
      radialSourceCutoff χ ((2 * L)⁻¹ • physicalCoordinates i ζ) =
        (1 - physicalCutoff 0 ((2 * L)⁻¹ • physicalCoordinates i ζ)) *
          conicMask (χ ∘ physicalCoordinates i) (L⁻¹ • ζ)
    rw [conicMask_eq_radial hnorm]
    simp only [radialSourceCutoff,
      NormedSpace.normalize_smul_of_pos (inv_pos.mpr (by positivity : 0 < 2 * L)),
      NormedSpace.normalize_smul_of_pos (inv_pos.mpr hL),
      normalize_physicalCoordinates, Function.comp_apply]

/-- Full closed-support nesting under the selected coordinate permutation.
This includes the physical and canonical cutoff shoulders and is the input
to the finite spatial plateau (`energy-complete-residual`). -/
theorem tsupport_physical_dilatedConicMask_subset
    (χ : E → ℝ) (i : Fin (d + 1)) {L : ℝ} (hL : 0 < L) :
    tsupport (dilatedConicMask χ (2 * L) ∘ physicalCoordinates i) ⊆
      tsupport (dilatedConicMask (χ ∘ physicalCoordinates i) L) := by
  have he : dilatedConicMask χ (2 * L) ∘ physicalCoordinates i =
      (fun ζ ↦ 1 - physicalCutoff 0 ((2 * L)⁻¹ • physicalCoordinates i ζ)) *
        dilatedConicMask (χ ∘ physicalCoordinates i) L :=
    funext (dilatedConicMask_physicalCoordinates_factor χ i hL)
  rw [he]
  exact tsupport_mul_subset_right

/-- The actual finite family has a SINGLE physical threshold, with the
source collar plateau on each full pulled-back right support. The exact
partition is in the original coordinates, including its one low-frequency
complement. All cones and local outputs are the selected ones
(`thm:sector`, `prop:complete-residual`). -/
theorem exists_common_physical_radial_masks
    {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)}
    {ι : Type*} [Fintype ι] (ξ : ι → E)
    (chart : ∀ p, LocalChart Ω x RQ A₀ (ξ p) M) (χ : ι → E → ℝ)
    (hsupp : ∀ p, tsupport (χ p) ⊆ (chart p).angularNeighborhood) :
    ∃ (a : ι → Euclidean d → ℝ) (L : ℝ), 1 ≤ L ∧
      (∀ p, ContDiff ℝ ∞ (a p) ∧ (∀ η, a p η ∈ Icc (0 : ℝ) 1) ∧
        HasCompactSupport (a p) ∧ tsupport (a p) ⊆ (chart p).spatialCone) ∧
      (∀ p, ∀ ζ ∈ tsupport (dilatedConicMask (χ p) L ∘
        physicalCoordinates (chart p).index),
        conicMask (a p) =ᶠ[𝓝 (Characteristic.EvolutionIntegral.spatialPart ζ)] (fun _ ↦ 1)) ∧
      (∀ ζ, (∑ p, dilatedConicMask (χ p) L ζ) +
        dilatedConicMask (fun η ↦ 1 - ∑ p, χ p η) L ζ +
        physicalCutoff 0 (L⁻¹ • ζ) = 1) := by
  obtain ⟨a, L, hL, ha, hplateau⟩ := exists_chart_nested_spatial_masks ξ chart χ hsupp
  refine ⟨a, 2 * L, by linarith, ha, ?_, dilatedConicMask_complete_partition χ (2 * L)⟩
  intro p ζ hζ
  exact hplateau p ζ
    (tsupport_physical_dilatedConicMask_subset (χ p) (chart p).index
      (zero_lt_one.trans_le hL) hζ)

end JanetCartan.RegularSector.FiniteMasks.ActualFamily
