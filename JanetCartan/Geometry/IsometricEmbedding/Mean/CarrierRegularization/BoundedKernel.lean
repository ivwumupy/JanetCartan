module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import JanetCartan.Analysis.Operator.HilbertSchmidt.Kernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Bounded measurable kernels on the literal carrier spaces

Analytic construction used by the finite regularization of `app:ch_background:eq:bg-T`.
The output measure is the published torus volume and the input is the literal
Lebesgue product. These lemmas are internal prerequisites of the amplitude/mask
construction; no operator bound or adjoint identity is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace JanetCartan.ContinuumRow.CarrierRegularization

variable {n : ℕ}
local notation "V" => EuclideanSpace ℂ (Fin n)
local notation "μ" => carrierMeasure n
local notation "ν" => (volume : Measure (Torus n))

variable {K : Torus n → CarrierVariable n → EuclideanSpace ℂ (Fin n)}
  {S : Set (CarrierVariable n)} {B : ℝ}
  (hK : StronglyMeasurable (Function.uncurry K))
  (hS : MeasurableSet S) (hfin : carrierMeasure n S ≠ ∞)
  (hs : ∀ x u, u ∉ S → K x u = 0)
  (hb : ∀ x u, ‖K x u‖ ≤ B)

include hS hfin hs hb in
private theorem input_majorant (f : CarrierL2 n) :
    Integrable (fun u ↦ B * ‖S.indicator f u‖) μ ∧
      ∀ x u, ‖f u • K x u‖ ≤ B * ‖S.indicator f u‖ := by
  constructor
  · exact ((integrableOn_Lp_of_measure_ne_top f (by norm_num) hfin).integrable_indicator hS).norm.const_mul B
  · intro x u
    by_cases hu : u ∈ S
    · simpa [Set.indicator_of_mem hu, norm_smul, mul_comm] using
        mul_le_mul_of_nonneg_right (hb x u) (norm_nonneg (f u))
    · simp [Set.indicator_of_notMem hu, hs x u hu]

include hK hS hfin hs hb

/-- Absolute convergence of each source integral in `app:ch_background:eq:bg-T`. -/
theorem integrable_source (f : CarrierL2 n) (x : Torus n) :
    Integrable (fun u ↦ f u • K x u) μ :=
  (input_majorant hS hfin hs hb f).1.mono'
    ((Lp.aestronglyMeasurable f).smul hK.of_uncurry_left.aestronglyMeasurable)
    (Eventually.of_forall ((input_majorant hS hfin hs hb f).2 x))

/-- The actual source integral is in torus L² (`app:ch_background:eq:bg-T`). -/
theorem memLp_source (f : CarrierL2 n) :
    MemLp (fun x ↦ ∫ u, f u • K x u ∂μ) 2 ν := by
  apply MemLp.of_bound
    (((Lp.aestronglyMeasurable f).comp_snd.smul hK.aestronglyMeasurable).integral_prod_right') (∫ u, B * ‖S.indicator f u‖ ∂μ)
  exact Eventually.of_forall fun x ↦ norm_integral_le_of_norm_le
    (input_majorant hS hfin hs hb f).1
    (Eventually.of_forall ((input_majorant hS hfin hs hb f).2 x))

omit hS hfin hs in
/-- Absolute convergence of each adjoint integral in
`app:ch_background:eq:bg-realification`. -/
theorem integrable_adjoint (w : ComplexOutputL2 n) (u : CarrierVariable n) :
    Integrable (fun x ↦ inner ℂ (K x u) (w x)) ν := by
  apply (((Lp.memLp w).integrable (by norm_num)).norm.const_mul B).mono'
    (hK.of_uncurry_right.aestronglyMeasurable.inner (Lp.aestronglyMeasurable w))
  exact Eventually.of_forall fun x ↦ (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hb x u) (norm_nonneg _))

/-- The literal adjoint representative is in the full carrier L² space
(`app:ch_background:eq:bg-realification`). -/
theorem memLp_adjoint (w : ComplexOutputL2 n) :
    MemLp (fun u ↦ ∫ x, inner ℂ (K x u) (w x) ∂ν) 2 μ := by
  have hm : AEStronglyMeasurable
      (fun u ↦ ∫ x, inner ℂ (K x u) (w x) ∂ν) μ :=
    (show AEStronglyMeasurable (fun p : CarrierVariable n × Torus n ↦
        inner ℂ (K p.2 p.1) (w p.2)) ((μ).prod ν) from
      hK.prod_swap.aestronglyMeasurable.inner
        (Lp.aestronglyMeasurable w).comp_snd).integral_prod_right'
  apply (memLp_indicator_const 2 hS.nullMeasurableSet
    (∫ x, B * ‖w x‖ ∂ν) (Or.inr hfin)).mono' hm
  apply Eventually.of_forall
  intro u
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu]
    apply norm_integral_le_of_norm_le
      (((Lp.memLp w).integrable (by norm_num)).norm.const_mul B)
    exact Eventually.of_forall fun x ↦ (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hb x u) (norm_nonneg _))
  · simp [Set.indicator_of_notMem hu, hs _ _ hu]

/-- Absolute integrability on the literal torus/carrier product, justifying
Fubini in `app:ch_background:eq:bg-realification`. -/
theorem integrable_pairing (f : CarrierL2 n) (w : ComplexOutputL2 n) :
    Integrable (fun p : Torus n × CarrierVariable n ↦
      inner ℂ (f p.2 • K p.1 p.2) (w p.1)) ((ν).prod μ) := by
  apply ((((Lp.memLp w).integrable (by norm_num)).norm).mul_prod
    (input_majorant hS hfin hs hb f).1).mono'
  · exact ((Lp.aestronglyMeasurable f).comp_snd.smul hK.aestronglyMeasurable).inner
      (Lp.aestronglyMeasurable w).comp_fst
  · exact Eventually.of_forall fun p ↦ (norm_inner_le_norm _ _).trans (by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        ((input_majorant hS hfin hs hb f).2 p.1 p.2) (norm_nonneg (w p.1)))

/-- Integral map on L² equivalence classes, before boundedness
(`app:ch_background:eq:bg-T`). -/
def sourceLinearMap : CarrierL2 n →ₗ[ℂ] ComplexOutputL2 n where
  toFun f := (memLp_source hK hS hfin hs hb f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_source hK hS hfin hs hb (f + g)).coeFn_toLp,
      (memLp_source hK hS hfin hs hb f).coeFn_toLp,
      (memLp_source hK hS hfin hs hb g).coeFn_toLp,
      Lp.coeFn_add ((memLp_source hK hS hfin hs hb f).toLp _)
        ((memLp_source hK hS hfin hs hb g).toLp _)] with x hx hf hg ha
    rw [hx, ha, Pi.add_apply, hf, hg, ← integral_add
      (integrable_source hK hS hfin hs hb f x) (integrable_source hK hS hfin hs hb g x)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with u hu
    rw [hu, Pi.add_apply, add_smul]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_source hK hS hfin hs hb (c • f)).coeFn_toLp,
      (memLp_source hK hS hfin hs hb f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_source hK hS hfin hs hb f).toLp _)] with x hx hf hc
    simp only [RingHom.id_apply]
    rw [hx, hc, Pi.smul_apply, hf, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with u hu
    simp [hu, smul_smul]

/-- The source quotient has the literal integral representative
(`app:ch_background:eq:bg-T`). -/
theorem sourceLinearMap_ae (f : CarrierL2 n) :
    sourceLinearMap hK hS hfin hs hb f =ᵐ[ν] fun x ↦ ∫ u, f u • K x u ∂μ :=
  (memLp_source hK hS hfin hs hb f).coeFn_toLp

/-- Fubini identifies the actual L² pairing, with no assumed adjoint formula
(`app:ch_background:eq:bg-realification`). -/
theorem sourceLinearMap_inner (f : CarrierL2 n) (w : ComplexOutputL2 n) :
    inner ℂ (sourceLinearMap hK hS hfin hs hb f) w =
      inner ℂ f ((memLp_adjoint hK hS hfin hs hb w).toLp _) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, ∫ u, inner ℂ (f u • K x u) (w x) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [sourceLinearMap_ae hK hS hfin hs hb f] with x hx
      rw [hx, ← inner_conj_symm, ← integral_inner
        (integrable_source hK hS hfin hs hb f x), ← integral_conj]
      congr 1
      funext u
      exact inner_conj_symm _ _
    _ = ∫ u, ∫ x, inner ℂ (f u • K x u) (w x) ∂ν ∂μ :=
      integral_integral_swap (integrable_pairing hK hS hfin hs hb f w)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_adjoint hK hS hfin hs hb w).coeFn_toLp] with u hu
      simp only [hu, inner_smul_left, RCLike.inner_apply,
        starRingEnd_apply, mul_comm, integral_mul_const]

/-- Closed-graph boundedness follows from the proved integral pairing
(`app:ch_background:eq:bg-T`). -/
theorem continuous_sourceLinearMap : Continuous (sourceLinearMap hK hS hfin hs hb) := by
  apply LinearMap.continuous_of_seq_closed_graph
  intro v f g hv hTv
  apply ext_inner_right ℂ
  intro w
  have hlim := hv.inner (𝕜 := ℂ) (tendsto_const_nhds (x :=
    (memLp_adjoint hK hS hfin hs hb w).toLp _))
  simp_rw [← sourceLinearMap_inner hK hS hfin hs hb] at hlim
  exact tendsto_nhds_unique (hTv.inner (𝕜 := ℂ) tendsto_const_nhds) hlim

/-- Constructed bounded operator on the published carrier/output spaces
(`app:ch_background:eq:bg-T`). -/
def boundedKernelOperator : CarrierL2 n →L[ℂ] ComplexOutputL2 n :=
  ⟨sourceLinearMap hK hS hfin hs hb, continuous_sourceLinearMap hK hS hfin hs hb⟩

/-- Literal AE source formula (`app:ch_background:eq:bg-T`). -/
theorem boundedKernelOperator_ae (f : CarrierL2 n) :
    boundedKernelOperator hK hS hfin hs hb f =ᵐ[ν] fun x ↦ ∫ u, f u • K x u ∂μ :=
  sourceLinearMap_ae hK hS hfin hs hb f

/-- Literal AE formula for the actual Hilbert adjoint
(`app:ch_background:eq:bg-realification`). -/
theorem boundedKernelOperator_adjoint_ae (w : ComplexOutputL2 n) :
    (boundedKernelOperator hK hS hfin hs hb).adjoint w =ᵐ[μ]
      fun u ↦ ∫ x, inner ℂ (K x u) (w x) ∂ν := by
  have he : (boundedKernelOperator hK hS hfin hs hb).adjoint w =
      (memLp_adjoint hK hS hfin hs hb w).toLp _ := by
    apply ext_inner_left ℂ
    intro f
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact sourceLinearMap_inner hK hS hfin hs hb f w
  rw [he]
  exact (memLp_adjoint hK hS hfin hs hb w).coeFn_toLp

end JanetCartan.ContinuumRow.CarrierRegularization
