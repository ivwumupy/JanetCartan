module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.FiniteCover
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily.CoordinateCollars

/-!
# The exact physical right multiplier on a selected chart

The physical cutoff is pulled back by the actual coordinate permutation.
Its normalized budgets follow by a linear contraction on the frequency
coordinate, using the smooth frequency-cutoff estimates behind
`boundedNormalizedSeminorm_dilatedConicMask`. No permutation invariance of
the bump is required. Closed-support nesting retains the entire shoulder.
Consumer: the signed retarded construction for
`app:ch_regular_base:eq:fixed-time-representation` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteEvolution.PhysicalCutoff
open Characteristic.ResidualCoordinates FiniteMasks FiniteMasks.ActualFamily
open FourierIntegral.PrimitiveProfiles Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "E" => Euclidean (d + 1)

/-- All normalized multiplier budgets on a compact shell away from zero,
for the literal physical multiplier. The coordinate permutation costs no
derivatives (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem boundedNormalizedSeminorm_physical_dilatedConicMask
    {mask : E → ℝ} (hm : ContDiff ℝ ∞ mask) (i : Fin (d+1))
    {L : ℝ} (hL : 1 ≤ L) {K : Set (X × E)} (hK : IsCompact K)
    (hzero : ∀ p ∈ K, p.2 ≠ 0) (m : ℕ) :
    BoundedNormalizedSeminorm K m
      (fun p : X × E ↦ (dilatedConicMask mask (2*L) (physicalCoordinates i p.2) : ℂ)) := by
  let T : X × E →L[ℝ] X × E :=
    (ContinuousLinearMap.fst ℝ X E).prod
      ((physicalCoordinates i).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ X E))
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change max ‖p.1‖ ‖physicalCoordinates i p.2‖ ≤ 1 * ‖p‖
    rw [norm_physicalCoordinates, one_mul]
    exact le_rfl
  have hTi := hK.image T.continuous
  have hTzero : ∀ p ∈ T '' K, p.2 ≠ 0 := by
    rintro p ⟨q, hq, rfl⟩
    change physicalCoordinates i q.2 ≠ 0
    intro hz
    exact hzero q hq ((physicalCoordinates i).injective (hz.trans (map_zero _).symm))
  have hmask := boundedNormalizedSeminorm_dilatedConicMask hm
    (show 1 ≤ 2*L by linarith) hTi hTzero m
  refine ⟨normalizedSeminorm (T '' K) m
    (fun p : X × E ↦ (dilatedConicMask mask (2*L) p.2 : ℂ)), ?_⟩
  rintro _ ⟨R, rfl⟩
  have hs : ContDiff ℝ ∞ (normalizedField (R : ℝ)
      (fun p : X × E ↦ (dilatedConicMask mask (2*L) p.2 : ℂ))) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_dilatedConicMask hm (2*L)).comp
      (contDiff_snd.const_smul (R : ℝ)))
  have h := cNorm_preAffine_contraction_le T hT 0 hTi isOpen_univ
    (subset_univ _) hs.contDiffOn
    (show MapsTo (fun p ↦ T p + 0) K (T '' K) from fun p hp ↦ by
      simpa only [add_zero] using mem_image_of_mem T hp) m
  have he : normalizedField (R : ℝ)
      (fun p : X × E ↦ (dilatedConicMask mask (2*L) (physicalCoordinates i p.2) : ℂ)) =
      (normalizedField (R : ℝ)
        (fun p : X × E ↦ (dilatedConicMask mask (2*L) p.2 : ℂ))) ∘
          (fun p ↦ T p + 0) := by
    funext p
    simp only [normalizedField, Function.comp_apply, add_zero]
    change (dilatedConicMask mask (2*L) (physicalCoordinates i ((R : ℝ) • p.2)) : ℂ) =
      (dilatedConicMask mask (2*L) ((R : ℝ) • physicalCoordinates i p.2) : ℂ)
    rw [map_smul]
  change cNorm K m (normalizedField (R : ℝ)
    (fun p : X × E ↦ (dilatedConicMask mask (2*L) (physicalCoordinates i p.2) : ℂ))) ≤ _
  rw [he]
  exact h.trans (cNorm_normalizedField_le hmask R.2)

/-- Complex closed-support nesting for the exact physical multiplier,
including both cutoff shoulders. This is the cover and spatial plateau
input to `energy-complete-residual`; it is not a multiplier equality. -/
theorem tsupport_complex_physical_dilatedConicMask_subset
    (mask : E → ℝ) (i : Fin (d+1)) {L : ℝ} (hL : 0 < L) :
    tsupport (fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates i ξ) : ℂ)) ⊆
      tsupport (fun ξ ↦ (dilatedConicMask (mask ∘ physicalCoordinates i) L ξ : ℂ)) := by
  have he : (fun ξ ↦ (dilatedConicMask mask (2*L) (physicalCoordinates i ξ) : ℂ)) =
      (fun ξ ↦ ((1 - FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0
        ((2*L)⁻¹ • physicalCoordinates i ξ)) : ℂ)) *
      (fun ξ ↦ (dilatedConicMask (mask ∘ physicalCoordinates i) L ξ : ℂ)) := by
    funext ξ
    simp only [Pi.mul_apply, dilatedConicMask_physicalCoordinates_factor mask i hL,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  rw [he]
  exact tsupport_mul_subset_right

end JanetCartan.RegularSector.FiniteEvolution.PhysicalCutoff
