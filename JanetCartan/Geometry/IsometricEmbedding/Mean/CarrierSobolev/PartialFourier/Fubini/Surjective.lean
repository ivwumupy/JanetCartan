module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Fubini.Map

/-!
# Surjectivity of the carrier Fubini map

Finite-measure outer indicators with arbitrary transverse L² values have
explicit product-space preimages. Density and completeness give surjectivity,
as required for `app:ch_background:prop:bg-inverse`.
-/

@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace JanetCartan.CarrierSobolev
open ContinuumRow
namespace Fubini

/-- The product function underlying an outer indicator has finite L² norm.
This supplies the dense family of preimages in the Fubini surjectivity proof
(`app:ch_background:prop:bg-inverse`). -/
theorem memLp_indicator_fiber {n : ℕ} (c : TransverseL2 n) {s : Set CarrierParameter}
    (hs : MeasurableSet s) (hμs : (volume.prod volume) s < ∞) :
    MemLp (fun p : CarrierVariable n => s.indicator (fun _ => c p.2) p.1)
      2 (carrierMeasure n) := by
  classical
  have hm : StronglyMeasurable
      (fun p : CarrierVariable n => s.indicator (fun _ => c p.2) p.1) := by
    exact ((Lp.stronglyMeasurable c).comp_measurable measurable_snd).indicator
      (hs.preimage measurable_fst)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (volume.prod volume) :=
    (integrable_indicator_iff hs).mpr (integrableOn_const (C := (1 : ℝ)) hμs.ne)
  convert hi.mul_prod ((Lp.memLp c).integrable_norm_pow (by decide : 2 ≠ 0)) using 1
  · ext p
    by_cases hp : p.1 ∈ s <;> simp [hp]
  · rfl

/-- Every finite-measure outer indicator has an actual product-space preimage
(`app:ch_background:prop:bg-inverse`). -/
theorem indicator_mem_range {n : ℕ} (c : TransverseL2 n) {s : Set CarrierParameter}
    (hs : MeasurableSet s) (hμs : (volume.prod volume) s < ∞) :
    ∃ f : CarrierL2 n, linearIsometry n f = indicatorConstLp 2 hs hμs.ne c := by
  classical
  let F : CarrierVariable n → ℂ := fun p => s.indicator (fun _ => c p.2) p.1
  have hF : MemLp F 2 (carrierMeasure n) := memLp_indicator_fiber (n := n) c hs hμs
  refine ⟨hF.toLp F, ?_⟩
  apply Lp.ext
  filter_upwards [toIterated_coeFn_coeFn (hF.toLp F),
    ae_ae_of_ae_prod hF.coeFn_toLp, indicatorConstLp_coeFn (p := 2) (hs := hs)
      (hμs := hμs.ne) (c := c)] with z hz hFz hcz
  change (toIterated (hF.toLp F)) z = _
  rw [hcz]
  apply Lp.ext
  by_cases hzs : z ∈ s
  · simp only [Set.indicator_of_mem hzs]
    filter_upwards [hz, hFz] with η hη hFη
    simpa [F, hzs] using hη.trans hFη
  · simp only [Set.indicator_of_notMem hzs]
    filter_upwards [hz, hFz, Lp.coeFn_zero ℂ 2 (volume : Measure (Euclidean (n - 1)))]
      with η hη hFη hzero
    simpa [F, hzs, hzero] using hη.trans hFη

/-- Surjectivity follows from explicit indicator preimages and the closed range
of an isometry from a complete L² space (`app:ch_background:prop:bg-inverse`). -/
theorem linearIsometry_surjective (n : ℕ) : Function.Surjective (linearIsometry n) := by
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun g => ∃ f, linearIsometry n f = g)
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact indicator_mem_range (n := n) c hs hμs
  · intro f g hf hg hd hfr hgr
    obtain ⟨f', hf'⟩ := hfr
    obtain ⟨g', hg'⟩ := hgr
    refine ⟨f' + g', ?_⟩
    change toIterated (f' + g') = _
    rw [toIterated_add]
    exact congrArg₂ (· + ·) hf' hg'
  · exact (linearIsometry n).isometry.isClosedEmbedding.isClosed_range

end Fubini
end JanetCartan.CarrierSobolev
