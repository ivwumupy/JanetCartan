module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.LowBounds.CompactSupport
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Compact scalar kernels on product carrier domains

The compact-kernel argument from `AmplitudeBound.FullNormalKernel.Adjoint`
and `NormalComparison.KernelCalculus.Scalar`, on metric product domains. This
variant is needed because the actual carrier is a product, not the Euclidean
measurement domain. Consumer: `modifiedCarrierOperator` and its normal identity
in `app:ch_background:prop:bg-adjoint`. Both measures may have infinite mass.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace JanetCartan.ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel

variable {E U : Type*}
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]

omit [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology U] in
private theorem compactKernel_input_majorant
    {μ : Measure U} [IsLocallyFiniteMeasure μ]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (h : Lp ℂ 2 μ) :
    ∃ b : U → ℝ, Integrable b μ ∧ ∀ x u, ‖t x u * h u‖ ≤ b u := by
  let K := Prod.snd '' tsupport (Function.uncurry t)
  have hK : IsCompact K := hs.image continuous_snd
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous ht
  refine ⟨fun u ↦ C * ‖K.indicator h u‖, ?_, ?_⟩
  · exact (((Lp.memLp h).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
      |>.integrable_indicator hK.measurableSet).norm.const_mul C
  · intro x u
    by_cases hu : u ∈ K
    · simpa only [Set.indicator_of_mem hu, norm_mul, Function.uncurry_apply_pair] using
        mul_le_mul_of_nonneg_right (hC (x, u)) (norm_nonneg (h u))
    · have hz : t x u = 0 := image_eq_zero_of_notMem_tsupport (f := Function.uncurry t) (fun hp ↦ hu ⟨(x, u), hp, rfl⟩)
      simp [hz, Set.indicator_of_notMem hu]

omit [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology U] in
/-- Every section of the compact kernel in `app:ch_background:prop:bg-adjoint`
can be integrated against an L² input. -/
theorem integrable_compactKernel_mul_L2
    {μ : Measure U} [IsLocallyFiniteMeasure μ]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (h : Lp ℂ 2 μ) (x : E) :
    Integrable (fun u ↦ t x u * h u) μ := by
  obtain ⟨b, hb, hbound⟩ := compactKernel_input_majorant ht hs h
  exact hb.mono' (((ht.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
    (Lp.aestronglyMeasurable h)) (Eventually.of_forall (hbound x))

omit [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology U] in
/-- The integral against an L² input is continuous for the compact kernel
of `app:ch_background:prop:bg-adjoint`. -/
theorem continuous_compactKernel_integral_L2
    {μ : Measure U} [IsLocallyFiniteMeasure μ]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (h : Lp ℂ 2 μ) :
    Continuous (fun x ↦ ∫ u, t x u * h u ∂μ) := by
  obtain ⟨b, hb, hbound⟩ := compactKernel_input_majorant ht hs h
  apply continuous_of_dominated (bound := b)
  · intro x
    exact ((ht.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable h)
  · exact fun x ↦ Eventually.of_forall (hbound x)
  · exact hb
  · exact Eventually.of_forall fun u ↦
      (ht.comp (continuous_id.prodMk continuous_const)).mul continuous_const

omit [MeasurableSpace E] [BorelSpace E]
  [BorelSpace U] [SecondCountableTopology U] in
/-- Compact physical support is preserved by integration in
`app:ch_background:prop:bg-adjoint`. -/
theorem hasCompactSupport_compactKernel_integral_L2
    {μ : Measure U} {t : E → U → ℂ}
    (hs : HasCompactSupport (Function.uncurry t)) (h : Lp ℂ 2 μ) :
    HasCompactSupport (fun x ↦ ∫ u, t x u * h u ∂μ) := by
  apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_fst)
  intro x hx
  by_contra hn
  apply hx
  have hz : ∀ u, t x u = 0 := fun u ↦
    image_eq_zero_of_notMem_tsupport (f := Function.uncurry t) (fun hp ↦ hn ⟨(x, u), hp, rfl⟩)
  simp [hz]

omit  [SecondCountableTopology U] in
/-- The integral representative belongs to L² for the compact kernel in
`app:ch_background:prop:bg-adjoint`. Both measures may have infinite total mass. -/
theorem memLp_compactKernel_integral_L2
    {μ : Measure U} {ν : Measure E} [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] {t : E → U → ℂ}
    (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (h : Lp ℂ 2 μ) :
    MemLp (fun x ↦ ∫ u, t x u * h u ∂μ) 2 ν :=
  (continuous_compactKernel_integral_L2 ht hs h).memLp_of_hasCompactSupport
    (hasCompactSupport_compactKernel_integral_L2 hs h)

/-- Absolute integrability of the L² pairing needed for Fubini in
`app:ch_background:prop:bg-adjoint`. -/
theorem integrable_compactKernel_L2_pairing
    {μ : Measure U} {ν : Measure E} [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] [SFinite μ] [SFinite ν]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (f : Lp ℂ 2 ν) (h : Lp ℂ 2 μ) :
    Integrable (fun p : E × U ↦ star (t p.1 p.2) * f p.1 * star (h p.2)) (ν.prod μ) := by
  let K := Prod.fst '' tsupport (Function.uncurry t)
  let L := Prod.snd '' tsupport (Function.uncurry t)
  have hK : IsCompact K := hs.image continuous_fst
  have hL : IsCompact L := hs.image continuous_snd
  have hf := ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
    |>.integrable_indicator hK.measurableSet
  have hh := ((Lp.memLp h).locallyIntegrable (by norm_num)).integrableOn_isCompact hL
    |>.integrable_indicator hL.measurableSet
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous ht
  apply ((hf.norm.mul_const C).mul_prod hh.norm).mono'
  · exact (ht.star.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_fst).mul
      (Lp.aestronglyMeasurable h).star.comp_snd
  · apply Eventually.of_forall
    rintro ⟨x, u⟩
    by_cases hx : x ∈ K
    · by_cases hu : u ∈ L
      · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hu, norm_mul, norm_star]
        calc
          ‖t x u‖ * ‖f x‖ * ‖h u‖ ≤ C * ‖f x‖ * ‖h u‖ := by
            gcongr
            exact hC (x, u)
          _ = ‖f x‖ * C * ‖h u‖ := by ring
      · have hz : t x u = 0 := image_eq_zero_of_notMem_tsupport
          (f := Function.uncurry t) (fun hp ↦ hu ⟨(x, u), hp, rfl⟩)
        simp [hz, Set.indicator_of_notMem hu]
    · have hz : t x u = 0 := image_eq_zero_of_notMem_tsupport
        (f := Function.uncurry t) (fun hp ↦ hx ⟨(x, u), hp, rfl⟩)
      simp [hz, Set.indicator_of_notMem hx]

omit [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U] in
private theorem compactKernel_adjoint_support
    {t : E → U → ℂ} (hs : HasCompactSupport (Function.uncurry t)) :
    HasCompactSupport (fun p : U × E ↦ star (t p.2 p.1)) := by
  have hh : HasCompactSupport (fun p : U × E ↦ t p.2 p.1) :=
    hs.comp_homeomorph (Homeomorph.prodComm U E)
  exact hh.comp_left (g := fun z : ℂ ↦ star z) (star_zero ℂ)

omit  [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] in
/-- The displayed adjoint representative in `app:ch_background:prop:bg-adjoint`
is absolutely convergent at every input point. -/
theorem integrable_compactKernel_adjoint_L2
    {ν : Measure E} [IsLocallyFiniteMeasure ν]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (f : Lp ℂ 2 ν) (u : U) :
    Integrable (fun x ↦ star (t x u) * f x) ν :=
  integrable_compactKernel_mul_L2 (t := fun u x ↦ star (t x u))
    (ht.comp continuous_swap).star
    (compactKernel_adjoint_support hs) f u

omit [SecondCountableTopology U] in
/-- The actual adjoint integral representative is in L², as required in
`app:ch_background:prop:bg-adjoint`. -/
theorem memLp_compactKernel_adjoint_L2
    {μ : Measure U} {ν : Measure E} [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] {t : E → U → ℂ}
    (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (f : Lp ℂ 2 ν) :
    MemLp (fun u ↦ ∫ x, star (t x u) * f x ∂ν) 2 μ :=
  memLp_compactKernel_integral_L2 (t := fun u x ↦ star (t x u))
    (ht.comp continuous_swap).star
    (compactKernel_adjoint_support hs) f

/-- The adjoint formula follows from the genuine input-kernel identity, by
Fubini and Hilbert-space uniqueness. This supplies the actual adjoint needed in
`app:ch_background:prop:bg-adjoint` and `app:ch_background:prop:bg-adjoint`.
Only continuity and compact support of the kernel are needed. -/
theorem adjoint_eq_integral_of_compactKernel
    {μ : Measure U} {ν : Measure E} [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] [SFinite μ] [SFinite ν]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t))
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν)
    (hT : ∀ h, T h =ᵐ[ν] fun x ↦ ∫ u, t x u * h u ∂μ)
    (f : Lp ℂ 2 ν) :
    T.adjoint f =ᵐ[μ] fun u ↦ ∫ x, star (t x u) * f x ∂ν := by
  have hg := memLp_compactKernel_adjoint_L2 (μ := μ) ht hs f
  let g : Lp ℂ 2 μ := hg.toLp _
  have hge : g =ᵐ[μ] fun u ↦ ∫ x, star (t x u) * f x ∂ν := hg.coeFn_toLp
  have heq : T.adjoint f = g := by
    apply ext_inner_left ℂ
    intro h
    rw [T.adjoint_inner_right, L2.inner_def, L2.inner_def]
    calc
      (∫ x, inner ℂ (T h x) (f x) ∂ν) =
          ∫ x, ∫ u, star (t x u) * f x * star (h u) ∂μ ∂ν := by
        apply integral_congr_ae
        filter_upwards [hT h] with x hx
        rw [hx, RCLike.inner_apply, ← integral_conj, ← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun u ↦ by
          simp only [map_mul, starRingEnd_apply]
          ring
      _ = ∫ u, ∫ x, star (t x u) * f x * star (h u) ∂ν ∂μ :=
        integral_integral_swap (integrable_compactKernel_L2_pairing ht hs f h)
      _ = ∫ u, inner ℂ (h u) (g u) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hge] with u hu
        rw [hu, RCLike.inner_apply, integral_mul_const, starRingEnd_apply]
  rw [heq]
  exact hge

variable {μ : Measure U} {ν : Measure E}
  [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] {t : E → U → ℂ}

/-- The integral representative as a linear map, before applying the closed
graph theorem (`app:ch_background:prop:bg-adjoint`). -/
def compactKernelLinearMap (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν where
  toFun h := (memLp_compactKernel_integral_L2 (ν := ν) ht hs h).toLp
    (fun x ↦ ∫ u, t x u * h u ∂μ)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_compactKernel_integral_L2 (ν := ν) ht hs (f + g)).coeFn_toLp,
      (memLp_compactKernel_integral_L2 (ν := ν) ht hs f).coeFn_toLp,
      (memLp_compactKernel_integral_L2 (ν := ν) ht hs g).coeFn_toLp,
      Lp.coeFn_add ((memLp_compactKernel_integral_L2 (ν := ν) ht hs f).toLp _)
        ((memLp_compactKernel_integral_L2 (ν := ν) ht hs g).toLp _)] with x hx hf hg ha
    rw [hx, ha, Pi.add_apply, hf, hg, ← integral_add
      (integrable_compactKernel_mul_L2 ht hs f x)
      (integrable_compactKernel_mul_L2 ht hs g x)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with u hu
    rw [hu, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_compactKernel_integral_L2 (ν := ν) ht hs (c • f)).coeFn_toLp,
      (memLp_compactKernel_integral_L2 (ν := ν) ht hs f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_compactKernel_integral_L2 (ν := ν) ht hs f).toLp _)]
      with x hx hf hc
    simp only [RingHom.id_apply]
    rw [hx, hc, Pi.smul_apply, hf, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with u hu
    rw [hu, Pi.smul_apply]
    simp only [smul_eq_mul]
    ring

omit [SecondCountableTopology U] in
/-- The constructed linear map has the prescribed input integral, as required
in `app:ch_background:prop:bg-adjoint`. -/
theorem compactKernelLinearMap_ae_integral
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (h : Lp ℂ 2 μ) :
    compactKernelLinearMap (ν := ν) ht hs h =ᵐ[ν] fun x ↦ ∫ u, t x u * h u ∂μ :=
  (memLp_compactKernel_integral_L2 ht hs h).coeFn_toLp

/-- The integral pairing with the conjugate transposed kernel, prior to
boundedness or adjoints (`app:ch_background:prop:bg-adjoint`). -/
theorem compactKernelLinearMap_inner [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (h : Lp ℂ 2 μ) (f : Lp ℂ 2 ν) :
    inner ℂ (compactKernelLinearMap ht hs h) f =
      inner ℂ h ((memLp_compactKernel_adjoint_L2 (μ := μ) ht hs f).toLp _) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℂ (compactKernelLinearMap ht hs h x) (f x) ∂ν) =
        ∫ x, ∫ u, star (t x u) * f x * star (h u) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [compactKernelLinearMap_ae_integral (ν := ν) ht hs h] with x hx
      rw [hx, RCLike.inner_apply, ← integral_conj, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun u ↦ by
        simp only [map_mul, starRingEnd_apply]
        ring
    _ = ∫ u, ∫ x, star (t x u) * f x * star (h u) ∂ν ∂μ :=
      integral_integral_swap (integrable_compactKernel_L2_pairing ht hs f h)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_compactKernel_adjoint_L2 (μ := μ) ht hs f).coeFn_toLp]
        with u hu
      rw [hu, RCLike.inner_apply, integral_mul_const, starRingEnd_apply]

/-- Compact kernels act continuously on the entire L² input space. The proof
uses the closed graph theorem and the absolutely convergent adjoint pairing,
not an assumed operator bound (`app:ch_background:prop:bg-adjoint`). -/
theorem continuous_compactKernelLinearMap [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t)) :
    Continuous (compactKernelLinearMap (μ := μ) (ν := ν) ht hs) := by
  apply LinearMap.continuous_of_seq_closed_graph
  intro v h g hv hTv
  apply ext_inner_right ℂ
  intro f
  have hlim := hv.inner (𝕜 := ℂ) (tendsto_const_nhds (x :=
    (memLp_compactKernel_adjoint_L2 (μ := μ) ht hs f).toLp _))
  simp_rw [← compactKernelLinearMap_inner ht hs] at hlim
  exact tendsto_nhds_unique (hTv.inner (𝕜 := ℂ) tendsto_const_nhds) hlim

/-- The actual bounded scalar integral operator of
`app:ch_background:prop:bg-adjoint`, constructed from continuity and compact support. -/
def compactKernelOperator [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν :=
  ⟨compactKernelLinearMap ht hs, continuous_compactKernelLinearMap ht hs⟩

/-- Input integral identity for the constructed bounded operator in
`app:ch_background:prop:bg-adjoint`. -/
theorem compactKernelOperator_ae_integral [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (h : Lp ℂ 2 μ) :
    compactKernelOperator (ν := ν) ht hs h =ᵐ[ν] fun x ↦ ∫ u, t x u * h u ∂μ :=
  compactKernelLinearMap_ae_integral ht hs h

/-- Actual Hilbert adjoint of the constructed operator, with no additional
kernel-identity premise (`app:ch_background:prop:bg-adjoint`). -/
theorem compactKernelOperator_adjoint_ae_integral [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (f : Lp ℂ 2 ν) :
    (compactKernelOperator (μ := μ) ht hs).adjoint f =ᵐ[μ]
      fun u ↦ ∫ x, star (t x u) * f x ∂ν :=
  adjoint_eq_integral_of_compactKernel ht hs (compactKernelOperator ht hs)
    (compactKernelOperator_ae_integral ht hs) f

omit [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology U] in
/-- Every compact kernel row is in carrier L². This supplies the test row in
Fubini for the composed normal (`app:ch_background:prop:bg-adjoint`). -/
theorem memLp_compactKernel_row (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (x : E) :
    MemLp (fun u ↦ star (t x u)) 2 μ := by
  apply ((ht.comp (continuous_const.prodMk continuous_id)).star).memLp_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_snd)
  intro u hu
  by_contra hn
  have hz : t x u = 0 := image_eq_zero_of_notMem_tsupport
    (f := Function.uncurry t) (fun hp ↦ hn ⟨(x, u), hp, rfl⟩)
  exact hu (by simp [hz])

/-- Absolute integrability before interchanging the normal integrals, for every
measurement L² datum (`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_compactKernel_normal_weight [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (f : Lp ℂ 2 ν) (x : E) :
    Integrable (fun p : E × U ↦ t x p.2 * star (t p.1 p.2) * f p.1) (ν.prod μ) := by
  have hr := memLp_compactKernel_row (μ := μ) ht hs x
  have hi := integrable_compactKernel_L2_pairing ht hs f (hr.toLp _)
  apply hi.congr
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq_comp hr.coeFn_toLp] with p hp
  dsimp only [Function.comp_def] at hp
  rw [hp, star_star]
  ring

/-- Absolute convergence of the literal normal acting on all measurement L²
inputs (`app:ch_background:prop:bg-adjoint`). -/
theorem integrable_compactKernel_normal_action [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (f : Lp ℂ 2 ν) (x : E) :
    Integrable (fun y ↦ (∫ u, t x u * star (t y u) ∂μ) * f y) ν := by
  simpa only [integral_mul_const] using
    (integrable_compactKernel_normal_weight ht hs f x).integral_prod_left

/-- Fubini identifies the composed normal with its literal paired kernel on
all L² data (`app:ch_background:prop:bg-adjoint`). -/
theorem compactKernelOperator_normal_ae [SFinite μ] [SFinite ν]
    (ht : Continuous (Function.uncurry t)) (hs : HasCompactSupport (Function.uncurry t))
    (f : Lp ℂ 2 ν) :
    compactKernelOperator (μ := μ) (ν := ν) ht hs
      ((compactKernelOperator (μ := μ) (ν := ν) ht hs).adjoint f) =ᵐ[ν]
      fun x ↦ ∫ y, (∫ u, t x u * star (t y u) ∂μ) * f y ∂ν := by
  have hadj := compactKernelOperator_adjoint_ae_integral (μ := μ) ht hs f
  filter_upwards [compactKernelOperator_ae_integral (ν := ν) ht hs
    ((compactKernelOperator (μ := μ) ht hs).adjoint f)] with x hx
  rw [hx]
  calc
    _ = ∫ u, t x u * ∫ y, star (t y u) * f y ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [hadj] with u hu
      rw [hu]
    _ = ∫ u, ∫ y, t x u * star (t y u) * f y ∂ν ∂μ := by
      simp only [← integral_const_mul, mul_assoc]
    _ = ∫ y, ∫ u, t x u * star (t y u) * f y ∂μ ∂ν :=
      (integral_integral_swap (integrable_compactKernel_normal_weight ht hs f x)).symm
    _ = _ := by simp only [integral_mul_const]

end JanetCartan.ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel
