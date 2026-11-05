module

public import JanetCartan.Analysis.Microlocal.SingleChannel.TimeIntegration
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.Vector
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The literal single-channel integral on every L² input

Compact support and continuity construct the integral in
`app:ch_osc:prop:osc-channel` on the full input space, with finite Euclidean
components. No oscillatory operator estimate is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace JanetCartan.SingleChannel

variable {d r : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "X" => ℝ × EuclideanSpace ℝ (Fin d)
variable {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsLocallyFiniteMeasure μ]
variable {k : (ℝ × EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℂ (Fin r)}

/-- The literal vector kernel integral of `app:ch_osc:prop:osc-channel`.
The input measure is retained, including a restricted chart measure. -/
def channelIntegral (k : X → Y → V) (f : Lp ℂ 2 μ) (x : X) : V :=
  ∫ u, f u • k x u ∂μ

private theorem kernel_majorant
    (hk : Continuous (Function.uncurry k))
    (hs : HasCompactSupport (Function.uncurry k)) (f : Lp ℂ 2 μ) :
    ∃ b : Y → ℝ, Integrable b μ ∧ ∀ x u, ‖f u • k x u‖ ≤ b u := by
  let Q := Prod.snd '' tsupport (Function.uncurry k)
  have hQ : IsCompact Q := hs.image continuous_snd
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hk
  refine ⟨fun u ↦ C * ‖Q.indicator f u‖, ?_, ?_⟩
  · exact (((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hQ
      |>.integrable_indicator hQ.measurableSet).norm.const_mul C
  · intro x u
    by_cases hu : u ∈ Q
    · simpa only [Set.indicator_of_mem hu, norm_smul, mul_comm,
        Function.uncurry_apply_pair] using
        mul_le_mul_of_nonneg_right (hC (x, u)) (norm_nonneg (f u))
    · have hz : k x u = 0 := image_eq_zero_of_notMem_tsupport
        (f := Function.uncurry k) (fun hp ↦ hu ⟨(x, u), hp, rfl⟩)
      simp [hz, Set.indicator_of_notMem hu]

/-- Every pointwise input integral is absolutely integrable, even for arbitrary
L² data (`app:ch_osc:prop:osc-channel`). -/
theorem integrable_channelIntegrand
    (hk : Continuous (Function.uncurry k))
    (hs : HasCompactSupport (Function.uncurry k)) (f : Lp ℂ 2 μ) (x : X) :
    Integrable (fun u ↦ f u • k x u) μ := by
  obtain ⟨b, hb, hbound⟩ := kernel_majorant hk hs f
  exact hb.mono' ((Lp.aestronglyMeasurable f).smul
    (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall (hbound x))

/-- The full-input channel integral is continuous in physical space
(`app:ch_osc:prop:osc-channel`). -/
theorem continuous_channelIntegral
    (hk : Continuous (Function.uncurry k))
    (hs : HasCompactSupport (Function.uncurry k)) (f : Lp ℂ 2 μ) :
    Continuous (channelIntegral k f) := by
  obtain ⟨b, hb, hbound⟩ := kernel_majorant hk hs f
  apply continuous_of_dominated (bound := b)
  · intro x
    exact (Lp.aestronglyMeasurable f).smul
      (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact fun x ↦ Eventually.of_forall (hbound x)
  · exact hb
  · exact Eventually.of_forall fun u ↦
      (hk.comp (continuous_id.prodMk (continuous_const (y := u)))).const_smul (f u)

omit [IsLocallyFiniteMeasure μ] in
/-- Physical compact support survives input integration
(`app:ch_osc:prop:osc-channel`). -/
theorem hasCompactSupport_channelIntegral
    (hs : HasCompactSupport (Function.uncurry k)) (f : Lp ℂ 2 μ) :
    HasCompactSupport (channelIntegral k f) := by
  apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_fst)
  intro x hx
  by_contra hn
  apply hx
  have hz : ∀ u, k x u = 0 := fun u ↦ image_eq_zero_of_notMem_tsupport
    (f := Function.uncurry k) (fun hp ↦ hn ⟨(x, u), hp, rfl⟩)
  simp [channelIntegral, hz]

/-- The actual integral belongs to the entire physical L² output space
(`app:ch_osc:prop:osc-channel`), before using the uniform frequency bound. -/
theorem memLp_channelIntegral
    (hk : Continuous (Function.uncurry k))
    (hs : HasCompactSupport (Function.uncurry k)) (f : Lp ℂ 2 μ) :
    MemLp (channelIntegral k f) 2 (volume : Measure X) :=
  (continuous_channelIntegral hk hs f).memLp_of_hasCompactSupport
    (hasCompactSupport_channelIntegral hs f)

/-- The literal integral is a complex linear map on all L² input classes
(`app:ch_osc:prop:osc-channel`). Its quantitative continuity is proved using
slice bounds, not placed in this construction as an assumption. -/
def channelIntegralLinearMap
    (hk : Continuous (Function.uncurry k))
    (hs : HasCompactSupport (Function.uncurry k)) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp V 2 (volume : Measure X) where
  toFun f := (memLp_channelIntegral hk hs f).toLp (channelIntegral k f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_channelIntegral hk hs (f + g)).coeFn_toLp,
      (memLp_channelIntegral hk hs f).coeFn_toLp,
      (memLp_channelIntegral hk hs g).coeFn_toLp,
      Lp.coeFn_add ((memLp_channelIntegral hk hs f).toLp _)
        ((memLp_channelIntegral hk hs g).toLp _)] with x hx hf hg ha
    rw [hx, ha, Pi.add_apply, hf, hg]
    unfold channelIntegral
    rw [← integral_add (integrable_channelIntegrand hk hs f x)
      (integrable_channelIntegrand hk hs g x)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with u hu
    rw [hu, Pi.add_apply, add_smul]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_channelIntegral hk hs (c • f)).coeFn_toLp,
      (memLp_channelIntegral hk hs f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_channelIntegral hk hs f).toLp _)] with x hx hf hc
    simp only [RingHom.id_apply]
    rw [hx, hc, Pi.smul_apply, hf]
    unfold channelIntegral
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with u hu
    rw [hu, Pi.smul_apply, smul_smul]
    rfl

/-- The constructed linear map represents the original integral on every input
(`app:ch_osc:prop:osc-channel`). -/
theorem channelIntegralLinearMap_ae_integral
    (hk : Continuous (Function.uncurry k))
    (hs : HasCompactSupport (Function.uncurry k)) (f : Lp ℂ 2 μ) :
    channelIntegralLinearMap hk hs f =ᵐ[volume] channelIntegral k f :=
  (memLp_channelIntegral hk hs f).coeFn_toLp

end JanetCartan.SingleChannel
