module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Multipliers
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The actual adjoint of a compactly supported integral kernel

The adjoint-kernel prerequisite for `app:ch_osc:lem:osc-amplitude` and
`app:ch_osc:eq:two-position-normal-bound`. Compact support localizes L² inputs
before applying Fubini; the input domain need not have finite measure.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace JanetCartan.AmplitudeBound

variable {d m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "U" => EuclideanSpace ℝ (Fin m)

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

/-- Every section of the compact kernel in `app:ch_osc:lem:osc-amplitude`
can be integrated against an L² input. -/
theorem integrable_compactKernel_mul_L2
    {μ : Measure U} [IsLocallyFiniteMeasure μ]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (h : Lp ℂ 2 μ) (x : E) :
    Integrable (fun u ↦ t x u * h u) μ := by
  obtain ⟨b, hb, hbound⟩ := compactKernel_input_majorant ht hs h
  exact hb.mono' (((ht.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
    (Lp.aestronglyMeasurable h)) (Eventually.of_forall (hbound x))

/-- The integral against an L² input is continuous for the compact kernel
of `app:ch_osc:lem:osc-amplitude`. -/
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

/-- Compact physical support is preserved by integration in
`app:ch_osc:lem:osc-amplitude`. -/
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

/-- The integral representative belongs to L² for the compact kernel in
`app:ch_osc:lem:osc-amplitude`. Both measures may have infinite total mass. -/
theorem memLp_compactKernel_integral_L2
    {μ : Measure U} {ν : Measure E} [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] {t : E → U → ℂ}
    (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (h : Lp ℂ 2 μ) :
    MemLp (fun x ↦ ∫ u, t x u * h u ∂μ) 2 ν :=
  (continuous_compactKernel_integral_L2 ht hs h).memLp_of_hasCompactSupport
    (hasCompactSupport_compactKernel_integral_L2 hs h)

/-- Absolute integrability of the L² pairing needed for Fubini in
`app:ch_osc:eq:two-position-normal-bound`. -/
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

private theorem compactKernel_adjoint_support
    {t : E → U → ℂ} (hs : HasCompactSupport (Function.uncurry t)) :
    HasCompactSupport (fun p : U × E ↦ star (t p.2 p.1)) := by
  have hh : HasCompactSupport (fun p : U × E ↦ t p.2 p.1) :=
    hs.comp_homeomorph (Homeomorph.prodComm U E)
  exact hh.comp_left (g := fun z : ℂ ↦ star z) (star_zero ℂ)

/-- The displayed adjoint representative in `app:ch_osc:eq:two-position-normal-bound`
is absolutely convergent at every input point. -/
theorem integrable_compactKernel_adjoint_L2
    {ν : Measure E} [IsLocallyFiniteMeasure ν]
    {t : E → U → ℂ} (ht : Continuous (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t)) (f : Lp ℂ 2 ν) (u : U) :
    Integrable (fun x ↦ star (t x u) * f x) ν :=
  integrable_compactKernel_mul_L2 (t := fun u x ↦ star (t x u))
    (ht.comp continuous_swap).star
    (compactKernel_adjoint_support hs) f u

/-- The actual adjoint integral representative is in L², as required in
`app:ch_osc:eq:two-position-normal-bound`. -/
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
`app:ch_osc:lem:osc-amplitude` and `app:ch_osc:eq:two-position-normal-bound`.
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

/-- The smooth Euclidean-domain adjoint formula in
`app:ch_osc:eq:two-position-normal-bound`, derived from the action of `T`.
No finite-measure assumption on `D` or global L¹ assumption on `f` is used. -/
theorem adjoint_ae_integral_of_smooth_compactKernel
    (D : Set U) (_hD : MeasurableSet D) {t : E → U → ℂ}
    (ht : ContDiff ℝ ∞ (Function.uncurry t))
    (hs : HasCompactSupport (Function.uncurry t))
    (T : Lp ℂ 2 (volume.restrict D) →L[ℂ] Lp (α := E) ℂ 2)
    (hT : ∀ h, T h =ᵐ[volume] fun x ↦ ∫ u, t x u * h u ∂(volume.restrict D))
    (f : Lp (α := E) ℂ 2) :
    T.adjoint f =ᵐ[volume.restrict D] fun u ↦ ∫ x, star (t x u) * f x :=
  adjoint_eq_integral_of_compactKernel ht.continuous hs T hT f

end JanetCartan.AmplitudeBound
