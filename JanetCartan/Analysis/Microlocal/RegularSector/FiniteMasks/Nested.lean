module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.SymbolBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Coordinates

/-!
# Nested spatial and spacetime Fourier collars

The amplitude's spatial collar must be one on the complete closed support
of the right spacetime multiplier. Construct that nesting from the original
compact angular carrier in the same open spatial cone. The one fixed radial
threshold precedes all coefficients and derivative orders. This closes the
cutoff plateau used by the direct physical cancellation and its upper endpoint
in `app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteMasks
open CompatibleResponse Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ}

/-- The same angular mask with one larger, fixed low-frequency collar.
The complete residual retains the corresponding low-frequency complement. -/
def dilatedConicMask (b : Euclidean (d + 1) → ℝ) (L : ℝ)
    (ξ : Euclidean (d + 1)) : ℝ := conicMask b (L⁻¹ • ξ)

/-- Dilation of the already constructed smooth mask preserves global
smoothness, including the zero covector (`finite-calculus`). -/
theorem contDiff_dilatedConicMask {b : Euclidean (d + 1) → ℝ}
    (hb : ContDiff ℝ ∞ b) (L : ℝ) : ContDiff ℝ ∞ (dilatedConicMask b L) :=
  (contDiff_conicMask hb).comp (contDiff_id.const_smul L⁻¹)

/-- The same exact partition retains the enlarged low-frequency piece.
It is not replaced by the identity in the complete residual. -/
theorem dilatedConicMask_complete_partition {ι : Type*} [Fintype ι]
    (b : ι → Euclidean (d + 1) → ℝ) (L : ℝ) (ξ : Euclidean (d + 1)) :
    (∑ i, dilatedConicMask (b i) L ξ) +
      dilatedConicMask (fun η ↦ 1 - ∑ i, b i η) L ξ +
      FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0 (L⁻¹ • ξ) = 1 :=
  conicMask_complete_partition b (L⁻¹ • ξ)

/-- Construct the spatial amplitude collar and the fixed right-multiplier
threshold together. The spatial mask is one as a germ at EVERY frequency in
the right multiplier's closed support, including all shoulders. Only the
original angular carrier's containment in its actual open cone is supplied;
no cutoff nesting is assumed (`energy-complete-residual`). -/
theorem exists_nested_spatial_conicMask
    (b : Euclidean (d + 1) → ℝ) {D : Set (Euclidean d)}
    (hD : IsOpen D) (hzero : (0 : Euclidean d) ∉ D)
    (hcone : ∀ η ∈ D, ∀ t : ℝ, 0 < t → t • η ∈ D)
    (hcarrier : ∀ ξ ∈ tsupport b ∩ sphere (0 : Euclidean (d + 1)) 1,
      spatialPart ξ ∈ D) :
    ∃ (a : Euclidean d → ℝ) (L : ℝ), 1 ≤ L ∧
      ContDiff ℝ ∞ a ∧ (∀ η, a η ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport a ∧ tsupport a ⊆ D ∧
      ∀ L' ≥ L, ∀ ξ ∈ tsupport (dilatedConicMask b L'),
        conicMask a =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1) := by
  let K := tsupport b ∩ sphere (0 : Euclidean (d + 1)) 1
  have hK : IsCompact K := (isCompact_sphere (0 : Euclidean (d + 1)) 1).inter_left
    (isClosed_tsupport b)
  have hne (ξ : Euclidean (d + 1)) (hξ : ξ ∈ K) : spatialPart ξ ≠ 0 := by
    intro hz
    exact hzero (hz ▸ hcarrier ξ hξ)
  have hncont : ContinuousOn (fun ξ ↦ NormedSpace.normalize (spatialPart ξ)) K := by
    intro ξ hξ
    exact (((spatialProjection.continuous.continuousAt.norm).inv₀
      (norm_ne_zero_iff.mpr (hne ξ hξ))).smul spatialProjection.continuous.continuousAt).continuousWithinAt
  let J := (fun ξ ↦ NormedSpace.normalize (spatialPart ξ)) '' K
  have hJD : J ⊆ D := by
    rintro η ⟨ξ, hξ, rfl⟩
    exact hcone _ (hcarrier ξ hξ) _ (inv_pos.mpr (norm_pos_iff.mpr (hne ξ hξ)))
  obtain ⟨a, ha, harange, hac, has, hap⟩ :=
    exists_compact_family_cutoff (hK.image_of_continuousOn hncont) hD hJD
  obtain ⟨c, hc, hlow⟩ := hK.exists_forall_le'
    (spatialProjection.continuous.norm.continuousOn)
    (fun ξ hξ ↦ norm_pos_iff.mpr (hne ξ hξ))
  let L := max 1 (3 / c)
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hLc : 2 < L * c := by
    have ht := mul_le_mul_of_nonneg_right (le_max_right 1 (3 / c)) hc.le
    rw [div_mul_cancel₀ _ hc.ne'] at ht
    linarith
  refine ⟨a, L, hL, ha, harange, hac, has, ?_⟩
  intro L' hLL ξ hξ
  have hLp' : 0 < L' := hLp.trans_le hLL
  have hs := conicMask_tsupport_subset b
    (tsupport_comp_subset_preimage (conicMask b) (continuous_id.const_smul L'⁻¹) hξ)
  change 1 ≤ ‖L'⁻¹ • ξ‖ ∧ NormedSpace.normalize (L'⁻¹ • ξ) ∈ tsupport b at hs
  have hnorm : L' ≤ ‖ξ‖ := by
    have h := hs.1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hLp'.le)] at h
    have ht := mul_le_mul_of_nonneg_left h hLp'.le
    simpa only [mul_one, ← mul_assoc, mul_inv_cancel₀ hLp'.ne', one_mul] using ht
  have hξp : 0 < ‖ξ‖ := hLp'.trans_le hnorm
  have hdir : NormedSpace.normalize ξ ∈ K := by
    refine ⟨?_, ?_⟩
    · simpa only [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hLp')] using hs.2
    · simpa only [mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (norm_pos_iff.mp hξp)
  have hsp : spatialPart ξ = ‖ξ‖ • spatialPart (NormedSpace.normalize ξ) := by
    rw [← spatialPart_smul, NormedSpace.norm_smul_normalize]
  have hspnorm : 2 < ‖spatialPart ξ‖ := by
    rw [hsp, norm_smul, Real.norm_of_nonneg hξp.le]
    exact hLc.trans_le (mul_le_mul (hLL.trans hnorm) (hlow _ hdir) hc.le hξp.le)
  have hspne : spatialPart ξ ≠ 0 := norm_pos_iff.mp (by linarith)
  have hnormalize : NormedSpace.normalize (spatialPart ξ) ∈ J := by
    refine ⟨NormedSpace.normalize ξ, hdir, ?_⟩
    conv_rhs => rw [hsp]
    exact (NormedSpace.normalize_smul_of_pos hξp _).symm
  have hcNorm : ContinuousAt (NormedSpace.normalize : Euclidean d → Euclidean d)
      (spatialPart ξ) :=
    (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hspne)).smul continuousAt_id
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hspnorm),
    hcNorm.eventually (isOpen_interior.mem_nhds (hap hnormalize))] with η hη hηa
  rw [conicMask_eq_radial hη.le]
  exact interior_subset (s := {η | a η = 1}) hηa

/-- The finite family uses ONE radial collar, chosen before any current
coefficient or derivative order. Consequently its exact partition has the
single low-frequency complement in `dilatedConicMask_complete_partition`.
All spatial amplitude masks retain their own fixed open cones
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_finite_nested_spatial_conicMasks {ι : Type*} [Fintype ι]
    (b : ι → Euclidean (d + 1) → ℝ) (D : ι → Set (Euclidean d))
    (hD : ∀ i, IsOpen (D i)) (hzero : ∀ i, (0 : Euclidean d) ∉ D i)
    (hcone : ∀ i, ∀ η ∈ D i, ∀ t : ℝ, 0 < t → t • η ∈ D i)
    (hcarrier : ∀ i, ∀ ξ ∈ tsupport (b i) ∩ sphere (0 : Euclidean (d + 1)) 1,
      spatialPart ξ ∈ D i) :
    ∃ (a : ι → Euclidean d → ℝ) (L : ℝ), 1 ≤ L ∧
      (∀ i, ContDiff ℝ ∞ (a i) ∧ (∀ η, a i η ∈ Icc (0 : ℝ) 1) ∧
        HasCompactSupport (a i) ∧ tsupport (a i) ⊆ D i) ∧
      ∀ i, ∀ ξ ∈ tsupport (dilatedConicMask (b i) L),
        conicMask (a i) =ᶠ[𝓝 (spatialPart ξ)] (fun _ ↦ 1) := by
  classical
  choose a L hL ha hr hc hs hn using
    fun i ↦ exists_nested_spatial_conicMask (b i) (hD i) (hzero i) (hcone i) (hcarrier i)
  have hsum : 0 ≤ ∑ i, L i := Finset.sum_nonneg fun i _ ↦ zero_le_one.trans (hL i)
  refine ⟨a, 1 + ∑ i, L i, by linarith, fun i ↦ ⟨ha i, hr i, hc i, hs i⟩, ?_⟩
  intro i ξ hξ
  apply hn i _ _ ξ hξ
  have hi : L i ≤ ∑ j, L j := Finset.single_le_sum
    (fun j _ ↦ zero_le_one.trans (hL j)) (Finset.mem_univ i)
  linarith

end JanetCartan.RegularSector.FiniteMasks
