module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.Basic
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Zero-loss amplitude bounds for fixed radial continuation

The normalization and radial weight are fixed before the local amplitude.
Thus composition and multiplication preserve a single additive high norm,
with no extra derivative reserve. Consumer: the normalized `W₀,W₁,PW₁`
budgets of `app:ch_regular_base:lem:retarded-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Fixed cost of radial continuation of an order `-o` amplitude. It depends
on the section and compact normalized chart, not on the amplitude or radial
scale (`app:ch_regular_base:lem:retarded-kernel`). -/
def jetBoundConstant (ℓ : E →L[ℝ] ℝ) (o : ℕ) (K : Set (TwoTimePoint E)) (m : ℕ) : ℝ :=
  1 + (∑ j ∈ Finset.range (m + 1), ‖ContinuousLinearMap.lsmul ℝ ℝ (E := F)‖ *
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
    cNorm K m (fun q ↦ (ℓ q.2.2.2)⁻¹ ^ o) *
    (compositionMultiplicity m * (1 + cNorm K m (ConicPhase.normalize ℓ)) ^ m)

/-- The continuation cost is positive, including at derivative order zero
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem jetBoundConstant_pos (ℓ : E →L[ℝ] ℝ) (o : ℕ)
    (K : Set (TwoTimePoint E)) (m : ℕ) : 0 < jetBoundConstant (F := F) ℓ o K m := by
  unfold jetBoundConstant compositionMultiplicity
  have := cNorm_nonneg K m (fun q : TwoTimePoint E ↦ (ℓ q.2.2.2)⁻¹ ^ o)
  have := cNorm_nonneg K m (ConicPhase.normalize ℓ)
  positivity

/-- The actual continued amplitude is bounded linearly by its original local
jets at the SAME order. This discharges the conic-amplitude budget, rather
than assuming a symbol estimate (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem cNorm_extend_le (ℓ : E →L[ℝ] ℝ) (o : ℕ)
    {K J U : Set (TwoTimePoint E)} (hK : IsCompact K) (hJ : IsCompact J)
    (hU : IsOpen U) (hJU : J ⊆ U)
    (hpos : ∀ q ∈ K, 0 < ℓ q.2.2.2) (hmap : MapsTo (ConicPhase.normalize ℓ) K J)
    {f : TwoTimePoint E → F} (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) :
    cNorm K m (extend ℓ o f) ≤ jetBoundConstant (F := F) ℓ o K m * cNorm J m f := by
  have hnorm : ∀ q ∈ K, ContDiffAt ℝ m (ConicPhase.normalize ℓ) q :=
    fun q hq ↦ (ConicPhase.contDiffAt_normalize ℓ (hpos q hq).ne').of_le (by simp)
  have hflocal : ∀ q ∈ J, ContDiffAt ℝ m f q :=
    fun q hq ↦ (hf.contDiffAt (hU.mem_nhds (hJU hq))).of_le (by simp)
  have hc := cNorm_comp_le_polynomial hnorm (fun q hq ↦ hflocal _ (hmap hq))
    (fun _ hi ↦ bddAbove_norm_iteratedFDeriv_of_contDiffAt hK hnorm hi)
    (cNorm_nonneg J m f)
    (fun i hi q hq ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ hflocal (hmap hq) hi)
  have hKU : K ⊆ ConicPhase.domain ℓ U := fun q hq ↦ ⟨hpos q hq, hJU (hmap hq)⟩
  have hweight : ContDiffOn ℝ ∞ (fun q : TwoTimePoint E ↦ (ℓ q.2.2.2)⁻¹ ^ o)
      (ConicPhase.domain ℓ U) := by
    intro q hq
    exact (((ℓ.contDiff.contDiffAt.comp q contDiffAt_snd.snd.snd).inv hq.1.ne').pow o).contDiffWithinAt
  have hcomp : ContDiffOn ℝ ∞ (f ∘ ConicPhase.normalize ℓ) (ConicPhase.domain ℓ U) := by
    intro q hq
    exact ((hf.contDiffAt (hU.mem_nhds hq.2)).comp q
      (ConicPhase.contDiffAt_normalize ℓ hq.1.ne')).contDiffWithinAt
  have hm := FullPhaseCharts.InverseEstimates.cNorm_bilinear_le_on
    (ContinuousLinearMap.lsmul ℝ ℝ (E := F)) hK (ConicPhase.isOpen_domain ℓ hU) hKU
    hweight hcomp m
  change cNorm K m (extend ℓ o f) ≤ _ at hm
  apply hm.trans
  calc
    _ ≤ (∑ j ∈ Finset.range (m + 1), ‖ContinuousLinearMap.lsmul ℝ ℝ (E := F)‖ *
          ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) *
        cNorm K m (fun q ↦ (ℓ q.2.2.2)⁻¹ ^ o) *
        (compositionMultiplicity m * cNorm J m f *
          (1 + cNorm K m (ConicPhase.normalize ℓ)) ^ m) := by
      apply mul_le_mul_of_nonneg_left hc
      exact mul_nonneg (Finset.sum_nonneg fun _ _ ↦
        mul_nonneg (norm_nonneg (ContinuousLinearMap.lsmul ℝ ℝ (E := F)))
          (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _))
        (cNorm_nonneg _ _ _)
    _ ≤ jetBoundConstant (F := F) ℓ o K m * cNorm J m f := by
      unfold jetBoundConstant
      nlinarith [cNorm_nonneg J m f]

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
