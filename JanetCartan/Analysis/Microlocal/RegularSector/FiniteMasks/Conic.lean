module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks
public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.AngularSource
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Basic

/-!
# Conic sector masks with a fixed low-frequency complement

Radially lift the fixed angular masks, using the existing source-cutoff
normalization, and remove the unit frequency ball with the fixed smooth
profile. This produces globally smooth Fourier masks, rather than asserting
smoothness of a degree-zero angular function at zero. The exact partition
retains both the angular complement and the low-frequency term.

Consumers: `EvolutionIntegral.SymbolBudgets` and the angular/low discrepancy
in `app:ch_regular_base:prop:complete-residual` of `paper.tex`, retained in
`paper-v2.tex`, `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.RegularSector.FiniteMasks
open CompatibleResponse FourierIntegral.LowBounds.FrequencyCutoff
variable {n : ℕ}

/-- The actual sector Fourier mask with one fixed low-frequency cutoff.
The same cutoff is retained in its complete complement (`finite-calculus`). -/
def conicMask (a : Euclidean n → ℝ) (ξ : Euclidean n) : ℝ :=
  (1 - physicalCutoff 0 ξ) * radialSourceCutoff a ξ

/-- Every conic mask vanishes on the entire closed unit ball; no local
phase or amplitude is used at zero (`app:ch_regular_base:setup:finite-calculus`). -/
theorem conicMask_eq_zero {a : Euclidean n → ℝ} {ξ : Euclidean n}
    (hξ : ‖ξ‖ ≤ 1) : conicMask a ξ = 0 := by
  rw [conicMask, physicalCutoff_eq_one 0 (by simpa [radius] using hξ)]
  ring

/-- Beyond the fixed radius two the mask is exactly the degree-zero angular
factor, with no change to the selected direction (`sector-theorem-identity`). -/
theorem conicMask_eq_radial {a : Euclidean n → ℝ} {ξ : Euclidean n}
    (hξ : 2 ≤ ‖ξ‖) : conicMask a ξ = radialSourceCutoff a ξ := by
  rw [conicMask, physicalCutoff_eq_zero 0 (by simpa [radius] using hξ)]
  ring

/-- The actual conic mask is globally smooth, including at zero, because it
vanishes on a fixed neighborhood there (`app:ch_regular_base:setup:finite-calculus`). -/
theorem contDiff_conicMask {a : Euclidean n → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (conicMask a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Euclidean n) (by norm_num : (0 : ℝ) < 1)]
      with η hη
    exact conicMask_eq_zero (le_of_lt (by simpa [mem_ball, dist_zero_right] using hη))
  · exact ((contDiff_const.sub (physicalCutoff_contDiff 0)).contDiffAt).mul
      ((radialSourceCutoff_contDiffOn ha).contDiffAt
        (isOpen_ne.preimage continuous_id |>.mem_nhds hξ))

/-- The literal conic Fourier mask stays in `[0,1]` (`finite-calculus`). -/
theorem conicMask_mem_Icc {a : Euclidean n → ℝ}
    (ha : ∀ ξ, a ξ ∈ Icc (0 : ℝ) 1) (ξ : Euclidean n) :
    conicMask a ξ ∈ Icc (0 : ℝ) 1 := by
  have hp := physicalCutoff_nonneg 0 ξ
  have hq := physicalCutoff_le_one 0 ξ
  have h := ha (NormedSpace.normalize ξ)
  change 0 ≤ (1 - physicalCutoff 0 ξ) * a (NormedSpace.normalize ξ) ∧
    (1 - physicalCutoff 0 ξ) * a (NormedSpace.normalize ξ) ≤ 1
  constructor
  · exact mul_nonneg (by linarith) h.1
  · nlinarith [h.2, mul_nonneg hp h.1]

/-- Closed support retains the angular shoulder and excludes the open unit
ball. This is the fixed conic support margin used by the graph constructor
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem conicMask_tsupport_subset (a : Euclidean n → ℝ) :
    tsupport (conicMask a) ⊆
      {ξ | 1 ≤ ‖ξ‖ ∧ NormedSpace.normalize ξ ∈ tsupport a} := by
  intro ξ hξ
  have hn : 1 ≤ ‖ξ‖ := by
    by_contra h
    have hz : conicMask a =ᶠ[𝓝 ξ] 0 := by
      filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds (lt_of_not_ge h))]
        with η hη
      exact conicMask_eq_zero hη.le
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hξ
  refine ⟨hn, normalize_mem_tsupport_of_radialSourceCutoff ?_ ?_⟩
  · intro h
    norm_num [h] at hn
  · exact (tsupport_mul_subset_right (f := fun ξ ↦ 1 - physicalCutoff 0 ξ)) hξ

/-- A fixed open cone containing the angular closed support also contains
the full collared closed support. This retains all shoulders for the elapsed
graph support and temporal/spatial cone conditions (`retarded-kernel`). -/
theorem conicMask_tsupport_subset_cone (a : Euclidean n → ℝ)
    {D : Set (Euclidean n)} (ha : tsupport a ⊆ D)
    (hD : ∀ ξ ∈ D, ∀ r : ℝ, 0 < r → r • ξ ∈ D) :
    tsupport (conicMask a) ⊆ D := by
  intro ξ hξ
  have h := conicMask_tsupport_subset a hξ
  simpa only [NormedSpace.norm_smul_normalize] using
    hD _ (ha h.2) ‖ξ‖ (zero_lt_one.trans_le h.1)

/-- One finite partition supplies an exact Fourier partition. The low-frequency
term and the angular complement are literal summands, not absorbed into the
principal cutoff (`app:ch_regular_base:prop:complete-residual`). -/
theorem conicMask_complete_partition {ι : Type*} [Fintype ι]
    (a : ι → Euclidean n → ℝ) (ξ : Euclidean n) :
    (∑ i, conicMask (a i) ξ) +
      conicMask (fun η ↦ 1 - ∑ i, a i η) ξ + physicalCutoff 0 ξ = 1 := by
  simp only [conicMask, radialSourceCutoff, ← Finset.mul_sum]
  ring

/-- The summed principal mask is one at high frequency on the original
protected angular plateau (`app:ch_regular_base:thm:sector`). -/
theorem sum_conicMask_eq_one {ι : Type*} [Fintype ι]
    (a : ι → Euclidean n → ℝ) {ξ : Euclidean n} (hξ : 2 ≤ ‖ξ‖)
    (ha : ∑ i, a i (NormedSpace.normalize ξ) = 1) :
    ∑ i, conicMask (a i) ξ = 1 := by
  simpa only [conicMask_eq_radial hξ, radialSourceCutoff] using ha

/-- Real even angular masks remain real even after the fixed radial collar.
This is the physical plus-pair convention's principal cutoff
(`app:ch_regular_base:thm:sector`). -/
theorem conicMask_neg {a : Euclidean n → ℝ} (ha : ∀ ξ, a (-ξ) = a ξ)
    (ξ : Euclidean n) : conicMask a (-ξ) = conicMask a ξ := by
  have hcut : physicalCutoff 0 (-ξ) = physicalCutoff 0 ξ := by
    simpa only [physicalCutoff, smul_neg] using profile.neg ((radius 0)⁻¹ • ξ)
  simp only [conicMask, hcut, radialSourceCutoff, NormedSpace.normalize_neg, ha]

end JanetCartan.RegularSector.FiniteMasks
