module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition.Continuity
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compact buffers for the literal characteristic formula

The consumers are the exponential and inverse substitutions in the scalar
comparison for `app:ch_background:prop:bg-frame`. The compact outer buffer is
chosen from the reference image. Its containment for varying maps follows from
the zeroth-order part of their difference, rather than an extra range premise.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
open HamiltonPhase.CompositionContinuity FullPhaseCharts.InverseEstimates

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Choose the outer compact buffer and the comparison threshold before the
varying maps. Used for the literal exponential and inverse-label substitutions
in `app:ch_waves:thm:leading` and `app:ch_background:prop:bg-frame`.
Only smoothness on the original open domain and a reference range are needed. -/
theorem exists_cNorm_comp_sub_lt_with_buffer
    {K : Set E} {U : Set F} (hK : IsCompact K) (hU : IsOpen U)
    {f₀ : F → G} {g₀ : E → F}
    (hf₀ : ContDiffOn ℝ ∞ f₀ U) (hg₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ g₀ x)
    (hrange₀ : MapsTo g₀ K U) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Set F, IsCompact L ∧ L ⊆ U ∧ ∃ δ > 0,
      ∀ (f : F → G) (g : E → F), ContDiffOn ℝ ∞ f U →
        (∀ x ∈ K, ContDiffAt ℝ ∞ g x) →
        cNorm L m (f - f₀) < δ → cNorm K m (g - g₀) < δ →
        cNorm K m (f ∘ g - f₀ ∘ g₀) < ε := by
  have hS := hK.image_of_continuousOn (fun x hx ↦ (hg₀ x hx).continuousAt.continuousWithinAt)
  obtain ⟨C, hC, hSC⟩ := exists_compact_superset hS
  obtain ⟨r, hr, hbuffer⟩ := hS.exists_cthickening_subset_open
    (hU.inter isOpen_interior) (subset_inter (image_subset_iff.mpr hrange₀) hSC)
  let L := cthickening r (g₀ '' K)
  have hL : IsCompact L := hC.of_isClosed_subset isClosed_cthickening
    (fun _ hx ↦ interior_subset (hbuffer hx).2)
  have hLU : L ⊆ U := fun _ hx ↦ (hbuffer hx).1
  have hr₀ : MapsTo g₀ K L := fun x hx ↦ self_subset_cthickening _ (mem_image_of_mem g₀ hx)
  obtain ⟨d, hd, hcomp⟩ := exists_cNorm_comp_sub_lt hK hL
    (fun y hy ↦ (hf₀.contDiffAt (hU.mem_nhds (hLU hy))).of_le (by simp))
    (fun x hx ↦ (hg₀ x hx).of_le (by simp)) hr₀ hε
  refine ⟨L, hL, hLU, min r d, lt_min hr hd, ?_⟩
  intro f g hf hg hsmallf hsmallg
  have hgL : MapsTo g K L := by
    intro x hx
    apply mem_cthickening_of_dist_le _ (g₀ x) r _ (mem_image_of_mem g₀ hx)
    rw [dist_eq_norm]
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun y hy ↦ ((hg y hy).sub (hg₀ y hy)).of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
      hx (Nat.zero_le m)
    rw [norm_iteratedFDeriv_zero] at hb
    exact hb.trans (hsmallg.trans_le (min_le_left _ _)).le
  exact hcomp f g (fun y hy ↦ (hf.contDiffAt (hU.mem_nhds (hLU hy))).of_le (by simp))
    (fun x hx ↦ (hg x hx).of_le (by simp)) hgL
    (hsmallf.trans_le (min_le_right _ _)) (hsmallg.trans_le (min_le_right _ _))

omit [FiniteDimensional ℝ F] in
/-- Adding the unchanged time coordinate costs no difference budget. This is
used for both the forward characteristic and inverse-label graph in
`app:ch_waves:thm:leading`. -/
theorem cNorm_timeGraph_sub_le {K : Set (ℝ × E)} (hK : IsCompact K) (m : ℕ)
    {f g : ℝ × E → F} (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x)
    (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x) :
    cNorm K m ((fun x ↦ (x.1, f x)) - (fun x ↦ (x.1, g x))) ≤ cNorm K m (f - g) := by
  have he : ((fun x : ℝ × E ↦ (x.1, f x)) - (fun x ↦ (x.1, g x))) =
      (fun x ↦ ((0 : ℝ), (f - g) x)) := by ext x <;> simp
  rw [he]
  have hh := cNorm_prodMk_le_on K hK m
    (fun _ _ ↦ (contDiffAt_const : ContDiffAt ℝ m (fun _ : ℝ × E ↦ (0 : ℝ)) _))
    (fun x hx ↦ ((hf x hx).sub (hg x hx)).of_le (by simp))
  change cNorm K m (fun x ↦ ((0 : ℝ), (f - g) x)) ≤ cNorm K m (0 : ℝ × E → ℝ) + cNorm K m (f - g) at hh
  simpa only [cNorm_zero, zero_add] using hh

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence
