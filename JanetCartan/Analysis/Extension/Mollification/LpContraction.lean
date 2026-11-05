module

public import JanetCartan.Analysis.Extension.Mollification.Contraction
public import JanetCartan.Analysis.Extension.Mollification.Lp
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Affine contraction in L²

Change of variables and strong continuity for the contraction step in Appendix B,
`app:ch_regular_base:lem:ball-extension` of `paper.tex`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped ENNReal Topology

namespace JanetCartan.Mollification

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the preimage of the closed ball
under a positive affine contraction is the expanded closed ball. -/
theorem preimage_contract_closedBall (c : E) (R : ℝ) {a : ℝ} (ha : 0 < a) :
    contract c a ⁻¹' closedBall c R = closedBall c (R / a) := by
  ext x
  simp only [mem_preimage, mem_closedBall, dist_contract_center, abs_of_pos ha]
  rw [le_div_iff₀ ha, mul_comm]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the Jacobian of affine contraction
with respect to any additive Haar measure. -/
theorem map_contract (c : E) {a : ℝ} (ha : 0 < a) :
    Measure.map (contract c a) μ = ENNReal.ofReal ((a ^ Module.finrank ℝ E)⁻¹) • μ := by
  change Measure.map ((fun x : E ↦ c + x) ∘ (fun x ↦ a • x) ∘ (fun x ↦ x - c)) μ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_sub_right μ c).map_eq, Measure.map_addHaar_smul μ ha.ne',
    Measure.map_smul _ (by fun_prop), (measurePreserving_add_left μ c).map_eq,
    abs_of_pos (inv_pos.mpr (pow_pos ha _))]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: change of variables between the
expanded ball and the original ball. -/
theorem map_contract_restrict_closedBall (c : E) (R : ℝ) {a : ℝ} (ha : 0 < a) :
    Measure.map (contract c a) (μ.restrict (closedBall c (R / a))) =
      ENNReal.ofReal ((a ^ Module.finrank ℝ E)⁻¹) • μ.restrict (closedBall c R) := by
  rw [← preimage_contract_closedBall c R ha,
    ← Measure.restrict_map ((contDiff_contract c a 0).continuous.measurable)
      isClosed_closedBall.measurableSet, map_contract μ c ha, Measure.restrict_smul]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: global L² membership is preserved
by positive affine contraction, in particular for zero-extended representatives. -/
theorem memLp_comp_contract {f : E → F} (hf : MemLp f 2 μ) (c : E) {a : ℝ}
    (ha : 0 < a) : MemLp (f ∘ contract c a) 2 μ := by
  apply MemLp.comp_of_map _ ((contDiff_contract c a 0).continuous.measurable.aemeasurable)
  rw [map_contract μ c ha]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: exact global L² change of variables;
the factor displayed is the square root of the inverse Jacobian. -/
theorem eLpNorm_two_comp_contract {f : E → F} (hf : MemLp f 2 μ) (c : E) {a : ℝ}
    (ha : 0 < a) :
    eLpNorm (f ∘ contract c a) 2 μ =
      ENNReal.ofReal ((a ^ Module.finrank ℝ E)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm f 2 μ := by
  have hm : AEStronglyMeasurable f (Measure.map (contract c a) μ) := by
    rw [map_contract μ c ha]
    exact hf.aestronglyMeasurable.smul_measure _
  rw [← eLpNorm_map_measure hm ((contDiff_contract c a 0).continuous.measurable.aemeasurable),
    map_contract μ c ha, eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  norm_num

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: L² data on the original closed ball
pull back to L² data on the expanded closed ball. -/
theorem memLp_comp_contract_closedBall {f : E → F} {c : E} {R a : ℝ}
    (hf : MemLp f 2 (μ.restrict (closedBall c R))) (ha : 0 < a) :
    MemLp (f ∘ contract c a) 2 (μ.restrict (closedBall c (R / a))) := by
  apply MemLp.comp_of_map _ ((contDiff_contract c a 0).continuous.measurable.aemeasurable)
  rw [map_contract_restrict_closedBall μ c R ha]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: exact L² norm bound on the expanded
closed ball, with the change-of-variables constant independent of the input function. -/
theorem eLpNorm_two_comp_contract_closedBall {f : E → F} {c : E} {R a : ℝ}
    (hf : MemLp f 2 (μ.restrict (closedBall c R))) (ha : 0 < a) :
    eLpNorm (f ∘ contract c a) 2 (μ.restrict (closedBall c (R / a))) =
      ENNReal.ofReal ((a ^ Module.finrank ℝ E)⁻¹) ^ (1 / 2 : ℝ) *
        eLpNorm f 2 (μ.restrict (closedBall c R)) := by
  have hm : AEStronglyMeasurable f
      (Measure.map (contract c a) (μ.restrict (closedBall c (R / a)))) := by
    rw [map_contract_restrict_closedBall μ c R ha]
    exact hf.aestronglyMeasurable.smul_measure _
  rw [← eLpNorm_map_measure hm ((contDiff_contract c a 0).continuous.measurable.aemeasurable),
    map_contract_restrict_closedBall μ c R ha,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  norm_num

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: contraction transports support
from the original closed ball to the expanded closed ball. -/
theorem support_comp_contract_subset_closedBall {f : E → F} {c : E} {R a : ℝ}
    (hf : support f ⊆ closedBall c R) (ha : 0 < a) :
    support (f ∘ contract c a) ⊆ closedBall c (R / a) := by
  rw [← preimage_contract_closedBall c R ha]
  exact fun _ hx ↦ hf hx

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: L² membership on the original
ball after contraction. -/
theorem memLp_comp_contract_restrict_closedBall {f : E → F} {c : E} {R a : ℝ}
    (hf : MemLp f 2 (μ.restrict (closedBall c R))) (hR : 0 ≤ R)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    MemLp (f ∘ contract c a) 2 (μ.restrict (closedBall c R)) := by
  apply (memLp_comp_contract_closedBall μ hf ha).mono_measure
  apply Measure.restrict_mono_set _
  exact closedBall_subset_closedBall ((le_div_iff₀ ha).mpr (mul_le_of_le_one_right hR ha1))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the topological support of a
contracted field lies in the expanded closed ball. -/
theorem tsupport_comp_contract_subset_closedBall {f : E → F} {c : E} {R a : ℝ}
    (hf : support f ⊆ closedBall c R) (ha : 0 < a) :
    tsupport (f ∘ contract c a) ⊆ closedBall c (R / a) :=
  closure_minimal (support_comp_contract_subset_closedBall hf ha) isClosed_closedBall

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: affine contraction commutes with
zero extension when the ball radius is expanded by the inverse contraction factor. -/
theorem indicator_closedBall_comp_contract (f : E → F) (c : E) (R : ℝ) {a : ℝ}
    (ha : 0 < a) :
    (closedBall c R).indicator f ∘ contract c a =
      (closedBall c (R / a)).indicator (f ∘ contract c a) := by
  rw [← preimage_contract_closedBall c R ha]
  ext x
  exact (Set.indicator_comp_right (contract c a)).symm

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the zero extension of contracted
ball data belongs to global L². -/
theorem memLp_indicator_closedBall_comp_contract {f : E → F} {c : E} {R a : ℝ}
    (hf : MemLp f 2 (μ.restrict (closedBall c R))) (ha : 0 < a) :
    MemLp ((closedBall c (R / a)).indicator (f ∘ contract c a)) 2 μ := by
  rw [memLp_indicator_iff_restrict isClosed_closedBall.measurableSet.nullMeasurableSet]
  exact memLp_comp_contract_closedBall μ hf ha

variable [NormedSpace ℝ F]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: the scaled contracted field on the
original ball obeys the same explicit L² bound for every derivative order. -/
theorem eLpNorm_two_scaled_comp_contract_le {f : E → F} {c : E} {R a : ℝ}
    (hf : MemLp f 2 (μ.restrict (closedBall c R))) (hR : 0 ≤ R)
    (ha : 0 < a) (ha1 : a ≤ 1) (j : ℕ) :
    eLpNorm (fun x ↦ a ^ j • f (contract c a x)) 2 (μ.restrict (closedBall c R)) ≤
      ENNReal.ofReal ((a ^ Module.finrank ℝ E)⁻¹) ^ (1 / 2 : ℝ) *
        eLpNorm f 2 (μ.restrict (closedBall c R)) := by
  calc
    _ = ‖a ^ j‖ₑ * eLpNorm (f ∘ contract c a) 2 (μ.restrict (closedBall c R)) :=
      eLpNorm_const_smul _ _ _ _
    _ ≤ 1 * eLpNorm (f ∘ contract c a) 2 (μ.restrict (closedBall c (R / a))) := by
      gcongr
      · rw [Real.enorm_eq_ofReal (pow_nonneg ha.le _)]
        exact ENNReal.ofReal_le_one.mpr (pow_le_one₀ ha.le ha1)
      · exact (le_div_iff₀ ha).mpr (mul_le_of_le_one_right hR ha1)
    _ = _ := by rw [one_mul, eLpNorm_two_comp_contract_closedBall μ hf ha]

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: continuous fields converge in L²
under contraction with the derivative scaling factor. -/
theorem tendsto_eLpNorm_two_scaled_comp_contract_sub_of_continuous
    {c : E} {R : ℝ} (j : ℕ) {f : E → F} (hf : Continuous f) :
    Tendsto (fun a ↦ eLpNorm (fun x ↦ a ^ j • f (contract c a x) - f x)
      2 (μ.restrict (closedBall c R))) (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
  have hu := tendstoUniformlyOn_scaled_comp_contract (c := c) (R := R) j hf.continuousOn
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  let C : ℝ≥0∞ := (μ.restrict (closedBall c R)) univ ^ (2 : ℝ)⁻¹
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (by
    simpa using (isCompact_closedBall c R).measure_ne_top (μ := μ))
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hC hε.ne'
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu (δ : ℝ) hδ).filter_mono
    (nhdsWithin_mono (1 : ℝ) Ioo_subset_Icc_self)] with a ha
  calc
    _ ≤ C * ENNReal.ofReal (δ : ℝ) := by
      apply eLpNorm_le_of_ae_bound
        (((hf.comp (contDiff_contract c a 0).continuous).const_smul _).sub hf).aestronglyMeasurable
      filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with x hx
      change ‖a ^ j • f (contract c a x) - f x‖ ≤ (δ : ℝ)
      simpa only [dist_eq_norm, norm_sub_rev] using (ha x hx).le
    _ ≤ ε := by simpa [ENNReal.ofReal_coe_nnreal, mul_comm] using hδε.le

/-- Appendix B, `app:ch_regular_base:lem:ball-extension`: arbitrary L² fields on a positive
closed ball converge in L² under affine contraction, including the factor for the jth derivative.
The continuous approximation used in the proof is supplied by L² density. -/
theorem tendsto_eLpNorm_two_scaled_comp_contract_sub {f : E → F} {c : E} {R : ℝ}
    (hf : MemLp f 2 (μ.restrict (closedBall c R))) (hR : 0 < R) (j : ℕ) :
    Tendsto (fun a ↦ eLpNorm (fun x ↦ a ^ j • f (contract c a x) - f x)
      2 (μ.restrict (closedBall c R))) (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
  have hK : ContinuousAt
      (fun a : ℝ ↦ ENNReal.ofReal ((a ^ Module.finrank ℝ E)⁻¹) ^ (1 / 2 : ℝ)) 1 := by
    exact ENNReal.continuous_rpow_const.continuousAt.comp
      (ENNReal.continuous_ofReal.continuousAt.comp
        ((continuousAt_id.pow _).inv₀ (by simp)))
  have hK' : ∀ᶠ a in 𝓝[Ioo (0 : ℝ) 1] 1,
      ENNReal.ofReal ((a ^ Module.finrank ℝ E)⁻¹) ^ (1 / 2 : ℝ) ≤ 2 := by
    have h := hK.tendsto.eventually (gt_mem_nhds (show
      ENNReal.ofReal (((1 : ℝ) ^ Module.finrank ℝ E)⁻¹) ^ (1 / 2 : ℝ) < 2 by simp))
    exact (h.filter_mono nhdsWithin_le_nhds).mono (fun _ ha ↦ ha.le)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt (by norm_num : (4 : ℝ≥0∞) ≠ ∞) hε.ne'
  obtain ⟨g, hg, hgm⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le (by norm_num)
    (ENNReal.coe_ne_zero.mpr hδ.ne')
  have hgconv := tendsto_eLpNorm_two_scaled_comp_contract_sub_of_continuous μ
    (c := c) (R := R) j g.continuous
  filter_upwards [hK', self_mem_nhdsWithin,
    (ENNReal.tendsto_nhds_zero.mp hgconv (δ : ℝ≥0∞) (ENNReal.coe_pos.mpr hδ))]
    with a haK ha hag
  let u : E → F := fun x ↦ a ^ j • (f - g) (contract c a x)
  let v : E → F := fun x ↦ a ^ j • g (contract c a x) - g x
  let w : E → F := g - f
  have heq : (fun x ↦ a ^ j • f (contract c a x) - f x) = u + v + w := by
    ext x
    simp only [u, v, w, Pi.add_apply, Pi.sub_apply, smul_sub]
    abel
  have hu : eLpNorm u 2 (μ.restrict (closedBall c R)) ≤ 2 * δ := by
    exact (eLpNorm_two_scaled_comp_contract_le μ (hf.sub hgm) hR.le ha.1 ha.2.le j).trans
      (mul_le_mul' haK hg)
  have hw : eLpNorm w 2 (μ.restrict (closedBall c R)) ≤ δ := by
    dsimp [w]
    rwa [eLpNorm_sub_comm]
  calc
    _ = eLpNorm (u + v + w) 2 (μ.restrict (closedBall c R)) := by rw [heq]
    _ ≤ (eLpNorm u 2 (μ.restrict (closedBall c R)) +
        eLpNorm v 2 (μ.restrict (closedBall c R))) +
        eLpNorm w 2 (μ.restrict (closedBall c R)) :=
      (eLpNorm_add_le (μ := μ.restrict (closedBall c R)) (p := 2)
        (f := u + v) (g := w) (by norm_num)).trans
        (add_le_add (eLpNorm_add_le (μ := μ.restrict (closedBall c R)) (p := 2)
          (f := u) (g := v) (by norm_num)) le_rfl)
    _ ≤ (2 * δ + δ) + δ := add_le_add (add_le_add hu hag) hw
    _ = (δ : ℝ≥0∞) * 4 := by ring
    _ ≤ ε := hδε.le

end JanetCartan.Mollification
