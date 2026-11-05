module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.LocalL2
public import JanetCartan.Analysis.Sobolev.Local.Smooth

/-!
# Supported smooth representatives on the original Euclidean domain

The representative and zero-extension steps of
`app:ch_regular:thm:exact-correction`. All a.e. statements use Lebesgue
measure, restricted to the same open domain as the original L² inverse.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal NNReal

namespace JanetCartan.FixedDomainInverse

open LocalSobolev SmallSupport

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {W : Set (EuclideanSpace ℝ (Fin n))}

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Continuous representatives inherit pointwise support from their L² class
on an open domain (`app:ch_regular:thm:exact-correction`). -/
theorem continuousRepresentative_zero_off_closed (hW : IsOpen W)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsClosed S)
    {u : LocalL2 W F} {f : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContinuousOn f W) (hfu : f =ᵐ[volume.restrict W] u)
    (hu : ∀ᵐ y ∂volume.restrict W, y ∉ S → u y = 0) :
    ∀ y ∈ W, y ∉ S → f y = 0 := by
  have heq : f =ᵐ[volume.restrict (W ∩ Sᶜ)] (fun _ ↦ (0 : F)) := by
    have hfu' := ae_restrict_of_ae_restrict_of_subset (show W ∩ Sᶜ ⊆ W from inter_subset_left) hfu
    have hu' := ae_restrict_of_ae_restrict_of_subset (show W ∩ Sᶜ ⊆ W from inter_subset_left) hu
    filter_upwards [hfu', hu', ae_restrict_mem (hW.inter hS.isOpen_compl).measurableSet]
      with y hy hz hyS
    exact hy.trans (hz hyS.2)
  exact fun y hy hout ↦ Measure.eqOn_open_of_ae_eq heq
    (hW.inter hS.isOpen_compl) (hf.mono inter_subset_left) continuousOn_const ⟨hy, hout⟩

omit [FiniteDimensional ℝ F] in
/-- A smooth representative supported in a closed subset of the open domain
has a smooth zero extension (`app:ch_regular:thm:exact-correction`). The
consumer takes this closed set to be the compact `tsupport χ₂`. -/
theorem contDiff_indicator_of_zero_off_closed (hW : IsOpen W)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsClosed S) (hSW : S ⊆ W)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiffOn ℝ ∞ f W)
    (hz : ∀ y ∈ W, y ∉ S → f y = 0) : ContDiff ℝ ∞ (W.indicator f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ W
  · apply (hf.contDiffAt (hW.mem_nhds hy)).congr_of_eventuallyEq
    filter_upwards [hW.mem_nhds hy] with q hq
    exact indicator_of_mem hq f
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    have hyS : y ∈ Sᶜ := fun h ↦ hy (hSW h)
    filter_upwards [hS.isOpen_compl.mem_nhds hyS] with q hq
    by_cases hqW : q ∈ W
    · rw [indicator_of_mem hqW, hz q hqW hq]
    · exact indicator_of_notMem hqW f

/-- The all-order Sobolev class has one globally smooth, supported
representative. It is the zero extension of its restriction to `W`, and
represents exactly the original local L² class
(`app:ch_regular:thm:exact-correction`). -/
theorem exists_supported_smoothRepresentative (hW : IsOpen W)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsClosed S) (hSW : S ⊆ W)
    (u : LocalL2 W F) (hu : ∀ s, MemRestrictionSobolev W s u)
    (hz : ∀ᵐ y ∂volume.restrict W, y ∉ S → u y = 0) :
    ∃ z : EuclideanSpace ℝ (Fin n) → F,
      ContDiff ℝ ∞ z ∧ z =ᵐ[volume.restrict W] u ∧ tsupport z ⊆ S ∧
        W.indicator z = z := by
  obtain ⟨f, hf, hfu⟩ := exists_contDiffOn_infty_ae_eq_of_memRestrictionSobolev hW u hu
  have hfz := continuousRepresentative_zero_off_closed hW hS hf.continuousOn hfu hz
  have hs : Function.support (W.indicator f) ⊆ S := by
    intro y hy
    by_contra hout
    by_cases hyW : y ∈ W
    · exact hy (by rw [indicator_of_mem hyW, hfz y hyW hout])
    · exact hy (indicator_of_notMem hyW f)
  refine ⟨W.indicator f, contDiff_indicator_of_zero_off_closed hW hS hSW hf hfz,
    ?_, closure_minimal hs hS, ?_⟩
  · filter_upwards [hfu, ae_restrict_mem hW.measurableSet] with y hy hyW
    simpa only [indicator_of_mem hyW] using hy
  · ext y
    by_cases hy : y ∈ W <;> simp [hy]

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Uniqueness of the continuous representative on the open domain; outside
it the zero-extension convention gives global uniqueness
(`app:ch_regular:thm:exact-correction`). -/
theorem supported_continuousRepresentative_unique (hW : IsOpen W)
    {u : LocalL2 W F} {f g : EuclideanSpace ℝ (Fin n) → F}
    (hf : ContinuousOn f W) (hg : ContinuousOn g W)
    (hfu : f =ᵐ[volume.restrict W] u) (hgu : g =ᵐ[volume.restrict W] u)
    (hfW : W.indicator f = f) (hgW : W.indicator g = g) : f = g := by
  have heq := Measure.eqOn_open_of_ae_eq (hfu.trans hgu.symm) hW hf hg
  funext y
  by_cases hy : y ∈ W
  · exact heq hy
  · rw [← hfW, ← hgW, indicator_of_notMem hy, indicator_of_notMem hy]

/-- Cutting off an all-order local Sobolev class preserves every order.
This proves the input obligation for the corrected source, rather than
assuming regularity of that corrected source
(`app:ch_regular:thm:exact-correction`). -/
theorem memRestrictionSobolev_bumpL2_of_all_orders (hW : IsOpen W)
    {x : EuclideanSpace ℝ (Fin n)} (χ : ContDiffBump x)
    (hχ : tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ W)
    (u : LocalL2 W F) (hu : ∀ s, MemRestrictionSobolev W s u) (s : ℕ) :
    MemRestrictionSobolev W s (bumpL2 (p := 2) le_rfl χ u) := by
  obtain ⟨f, hf, hfu⟩ := exists_contDiffOn_infty_ae_eq_of_memRestrictionSobolev hW u hu
  let g := fun y ↦ χ y • f y
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    · exact χ.contDiffAt.smul (hf.contDiffAt (hW.mem_nhds (hχ hy)))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with q hq
      simp [g, hq]
  have hgc : HasCompactSupport g := χ.hasCompactSupport.smul_right
  refine ⟨{
    toFun := g
    jet := fun j ↦ iteratedFDeriv ℝ j g
    weakJet := Mollification.hasWeakJetOn_of_contDiff volume (hg.of_le (by simp)) univ
    memLp_fun := hg.continuous.memLp_of_hasCompactSupport hgc
    memLp_jet := fun j _ ↦ (hg.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
      (hgc.iteratedFDeriv j)
    restrict_eq := ?_ }⟩
  filter_upwards [hfu, bumpL2_coeFn (p := 2) le_rfl χ u] with y hy hχy
  exact (congrArg (χ y • ·) hy).trans hχy.symm

end JanetCartan.FixedDomainInverse
