module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Smooth integrals over compact parameter sets

The parameter integrals in `app:ch_background:prop:bg-normalized` of `paper.tex`
include the divided-phase integral and the carrier mean. Joint smoothness on an
open product and finiteness of the measure on the compact carrier set suffice:
integrability and local domination are consequences, not extra assumptions.
The spatial variable may include any finite-dimensional spectator parameters.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan

universe u v w

variable {E : Type u} {Z : Type w} {F : Type (max u v)}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set E} {V K : Set Z} {f : E × Z → F}

/-- `app:ch_background:prop:bg-normalized`: the actual spatial Fréchet derivative
of a jointly smooth integrand is jointly smooth on the same open product. -/
theorem contDiffOn_parameterFDeriv (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun p : E × Z ↦ fderiv ℝ (fun x ↦ f (x, p.2)) p.1)
      (U ×ˢ V) := by
  intro p hp
  have hfp : ContDiffAt ℝ ∞ f p := hf.contDiffAt ((hU.prod hV).mem_nhds hp)
  have h : ContDiffAt ℝ ∞ (fun q : (E × Z) × E ↦ f (q.2, q.1.2)) (p, p.1) :=
    hfp.comp (p, p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact (h.fderiv contDiffAt_fst (by simp)).contDiffWithinAt

variable [MeasurableSpace Z] [BorelSpace Z] {μ : Measure Z}

omit [NormedSpace ℝ E] [NormedSpace ℝ Z] [NormedSpace ℝ F] in
/-- `app:ch_background:prop:bg-normalized`: each carrier section is integrable
on the compact carrier set under the sole measure hypothesis of finite mass. -/
theorem integrableOn_compactParameter [IsFiniteMeasure (μ.restrict K)]
    (hK : IsCompact K) (hKV : K ⊆ V)
    (hf : ContinuousOn f (U ×ˢ V)) {x : E} (hx : x ∈ U) :
    IntegrableOn (fun z ↦ f (x, z)) K μ := by
  have hc : ContinuousOn (fun z ↦ f (x, z)) K :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hz ↦ ⟨hx, hKV hz⟩)
  apply hc.integrableOn_of_subset_isCompact hK hK.measurableSet Subset.rfl
  simpa only [Measure.restrict_apply_univ] using measure_ne_top (μ.restrict K) univ

/-- `app:ch_background:prop:bg-normalized`: the spatial derivative is integrable
over the compact carrier set, as a function with values in continuous linear maps. -/
theorem integrableOn_parameterFDeriv [IsFiniteMeasure (μ.restrict K)]
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) {x : E} (hx : x ∈ U) :
    IntegrableOn (fun z ↦ fderiv ℝ (fun y ↦ f (y, z)) x) K μ :=
  integrableOn_compactParameter hK hKV
    (contDiffOn_parameterFDeriv hU hV hf).continuousOn hx

variable [FiniteDimensional ℝ E]

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- `app:ch_background:prop:bg-normalized`: compactness supplies one bound for
the spatial derivative, uniform over the carrier set and a neighborhood of `x`. -/
theorem exists_bound_parameterFDeriv (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V))
    {x : E} (hx : x ∈ U) :
    ∃ r > 0, Metric.closedBall x r ⊆ U ∧ ∃ C : ℝ,
      ∀ y ∈ Metric.closedBall x r, ∀ z ∈ K,
        ‖fderiv ℝ (fun y ↦ f (y, z)) y‖ ≤ C := by
  let : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).prod hK).exists_bound_of_continuousOn
    ((contDiffOn_parameterFDeriv hU hV hf).continuousOn.mono
      (Set.prod_mono hrU hKV))
  exact ⟨r, hr, hrU, C, fun y hy z hz ↦ hC (y, z) ⟨hy, hz⟩⟩

/-- `app:ch_background:prop:bg-normalized`: differentiation passes through the
compact carrier integral. The derivative is the integral of the actual spatial
Fréchet derivatives; all measurability, integrability and domination are derived. -/
theorem hasFDerivAt_compactParameterIntegral [CompleteSpace F]
    [IsFiniteMeasure (μ.restrict K)] (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V))
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ z in K, f (y, z) ∂μ)
      (∫ z in K, fderiv ℝ (fun y ↦ f (y, z)) x ∂μ) x := by
  obtain ⟨r, hr, hrU, C, hC⟩ := exists_bound_parameterFDeriv hU hV hK hKV hf hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y z ↦ fderiv ℝ (fun y ↦ f (y, z)) y)
    (s := Metric.ball x r) (bound := fun _ ↦ C) (Metric.ball_mem_nhds x hr)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (integrableOn_compactParameter hK hKV hf.continuousOn hy).aestronglyMeasurable
  · exact integrableOn_compactParameter hK hKV hf.continuousOn hx
  · exact (integrableOn_parameterFDeriv hU hV hK hKV hf hx).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact fun y hy ↦ hC y (Metric.ball_subset_closedBall hy) z hz
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    intro y hy
    have hyU := hrU (Metric.ball_subset_closedBall hy)
    have hfy := hf.contDiffAt
      ((hU.prod hV).mem_nhds (show (y, z) ∈ U ×ˢ V from ⟨hyU, hKV hz⟩))
    exact ((hfy.comp y (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      (by simp)).hasFDerivAt

/-- `app:ch_background:prop:bg-normalized`: the spatial Fréchet derivative of
the carrier integral equals the integral of the spatial Fréchet derivative. -/
theorem fderiv_compactParameterIntegral [CompleteSpace F]
    [IsFiniteMeasure (μ.restrict K)] (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V))
    {x : E} (hx : x ∈ U) :
    fderiv ℝ (fun y ↦ ∫ z in K, f (y, z) ∂μ) x =
      ∫ z in K, fderiv ℝ (fun y ↦ f (y, z)) x ∂μ :=
  (hasFDerivAt_compactParameterIntegral hU hV hK hKV hf hx).fderiv

/-- `app:ch_background:prop:bg-normalized`: integration over a fixed compact
carrier set preserves joint smoothness in all finite-dimensional spatial and
spectator variables. The carrier space need not itself be finite-dimensional. -/
theorem contDiffOn_compactParameterIntegral [CompleteSpace F]
    [IsFiniteMeasure (μ.restrict K)] (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ z in K, f (x, z) ∂μ) U := by
  have aux (n : ℕ) : ∀ {G : Type (max u v)} [NormedAddCommGroup G] [NormedSpace ℝ G]
      [CompleteSpace G] (g : E × Z → G), ContDiffOn ℝ ∞ g (U ×ˢ V) →
      ContDiffOn ℝ n (fun x ↦ ∫ z in K, g (x, z) ∂μ) U := by
    induction n with
    | zero =>
      intro G _ _ _ g hg
      exact contDiffOn_zero.mpr (fun x hx ↦
        (hasFDerivAt_compactParameterIntegral hU hV hK hKV hg hx).continuousAt.continuousWithinAt)
    | succ n ih =>
      intro G _ _ _ g hg
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = n + 1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨?_, by simp, ?_⟩
      · intro x hx
        apply DifferentiableAt.differentiableWithinAt
        exact (hasFDerivAt_compactParameterIntegral hU hV hK hKV hg hx).differentiableAt
      · exact (ih _ (contDiffOn_parameterFDeriv hU hV hg)).congr fun x hx ↦
          fderiv_compactParameterIntegral hU hV hK hKV hg hx
  exact contDiffOn_infty.mpr fun n ↦ aux n f hf

/-- `app:ch_background:prop:bg-normalized`: the unit-interval integral used to
extend the divided phase smoothly through zero, with all spectators retained. -/
theorem contDiffOn_unitIntervalParameterIntegral [CompleteSpace F]
    {g : E × ℝ → F} {W : Set ℝ} (hU : IsOpen U) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hg : ContDiffOn ℝ ∞ g (U ×ˢ W)) :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ t in (0 : ℝ)..1, g (x, t)) U := by
  simp only [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact contDiffOn_compactParameterIntegral hU hW isCompact_Icc hIW hg

/-- `app:ch_background:prop:bg-normalized`: the actual spatial derivative of
the divided-phase unit-interval integral is the integral of the spatial derivative. -/
theorem hasFDerivAt_unitIntervalParameterIntegral [CompleteSpace F]
    {g : E × ℝ → F} {W : Set ℝ} (hU : IsOpen U) (hW : IsOpen W)
    (hIW : Icc (0 : ℝ) 1 ⊆ W) (hg : ContDiffOn ℝ ∞ g (U ×ˢ W))
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ t in (0 : ℝ)..1, g (y, t))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y ↦ g (y, t)) x) x := by
  simp only [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact hasFDerivAt_compactParameterIntegral hU hW isCompact_Icc hIW hg hx

end JanetCartan
