module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Joint smoothness of parameter-dependent time integrals

The characteristic exponential formula in `app:ch_waves:thm:leading` and
`app:ch_background:prop:bg-positive` involves an interval integral whose upper
endpoint and coefficient depend on parameters. We prove its joint smoothness
on the entire original open product domain.

First, differentiation under a fixed interval integral follows from a uniform
bound on a compact time segment times a small closed parameter ball. Induction
on the differentiability order gives smoothness for Banach-valued integrands.
An affine substitution from `[0, 1]` then treats the variable endpoint, including
endpoints on either side of the initial time and the initial time itself.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan

universe u v

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_waves:thm:leading`: differentiate a smooth parameter-dependent
integral over a fixed interval. Compactness supplies the local domination. -/
theorem hasFDerivAt_fixedIntervalIntegral {F : ℝ × P → E} {U : Set P} {a b : ℝ}
    (hU : IsOpen U) (hF : ∀ q ∈ uIcc a b ×ˢ U, ContDiffAt ℝ ∞ F q)
    {x : P} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ s in a..b, F (s, y))
      (∫ s in a..b, (fderiv ℝ F (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ P)) x := by
  let G : ℝ × P → P →L[ℝ] E :=
    fun q ↦ (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ P)
  have hG (q) (hq : q ∈ uIcc a b ×ˢ U) : ContDiffAt ℝ ∞ G q :=
    ((hF q hq).fderiv_right (by simp)).clm_comp contDiffAt_const
  have hFc : ContinuousOn F (uIcc a b ×ˢ U) :=
    fun q hq ↦ (hF q hq).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (uIcc a b ×ˢ U) :=
    fun q hq ↦ (hG q hq).continuousAt.continuousWithinAt
  have hFs (y) (hy : y ∈ U) : ContinuousOn (fun s ↦ F (s, y)) (uIcc a b) :=
    hFc.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs ↦ ⟨hs, hy⟩)
  have hGs (y) (hy : y ∈ U) : ContinuousOn (fun s ↦ G (s, y)) (uIcc a b) :=
    hGc.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs ↦ ⟨hs, hy⟩)
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall x r)).exists_bound_of_continuousOn
    (hGc.mono (Set.prod_mono Subset.rfl hrU))
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y s ↦ G (s, y)) (bound := fun _ ↦ C) (Metric.closedBall_mem_nhds x hr)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact ((hFs y hy).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact (hFs x hx).intervalIntegrable
  · exact ((hGs x hx).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with s hs y hy
    exact hC (s, y) ⟨uIoc_subset_uIcc hs, hy⟩
  · exact intervalIntegrable_const
  · filter_upwards with s hs y hy
    exact ((hF (s, y) ⟨uIoc_subset_uIcc hs, hrU hy⟩).differentiableAt (by simp)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right s y)

/-- `app:ch_waves:thm:leading`: fixed-interval smoothness in a universe closed
under taking derivatives; the public theorem below removes this restriction. -/
private theorem contDiffOn_fixedIntervalIntegral_aux {P : Type u} {E : Type (max u v)}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ × P → E} {U : Set P} {a b : ℝ}
    (hU : IsOpen U) (hF : ∀ q ∈ uIcc a b ×ˢ U, ContDiffAt ℝ ∞ F q) :
    ContDiffOn ℝ ∞ (fun y ↦ ∫ s in a..b, F (s, y)) U := by
  apply contDiffOn_infty.mpr
  intro n
  induction n generalizing E with
  | zero =>
    apply contDiffOn_zero.mpr
    intro x hx
    exact (hasFDerivAt_fixedIntervalIntegral hU hF hx).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx ↦ (hasFDerivAt_fixedIntervalIntegral hU hF hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have hG : ∀ q ∈ uIcc a b ×ˢ U, ContDiffAt ℝ ∞
        (fun q ↦ (fderiv ℝ F q).comp (ContinuousLinearMap.inr ℝ ℝ P)) q := by
      intro q hq
      exact ((hF q hq).fderiv_right (by simp)).clm_comp contDiffAt_const
    exact (ih hG).congr (fun x hx ↦ (hasFDerivAt_fixedIntervalIntegral hU hF hx).fderiv)

/-- `app:ch_waves:thm:leading`: smooth fixed-interval integration with an
arbitrary Banach target and all parameters retained. -/
theorem contDiffOn_fixedIntervalIntegral {P : Type u} {E : Type v}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ × P → E} {U : Set P} {a b : ℝ}
    (hU : IsOpen U) (hF : ∀ q ∈ uIcc a b ×ˢ U, ContDiffAt ℝ ∞ F q) :
    ContDiffOn ℝ ∞ (fun y ↦ ∫ s in a..b, F (s, y)) U := by
  let e : ULift.{u} E ≃L[ℝ] E := ContinuousLinearEquiv.ulift
  have h := contDiffOn_fixedIntervalIntegral_aux (F := fun q ↦ e.symm (F q)) hU
    (fun q hq ↦ e.symm.contDiff.contDiffAt.comp q (hF q hq))
  apply (e.contDiff.comp_contDiffOn h).congr
  intro y hy
  have hFC : ContinuousOn (fun q ↦ e.symm (F q)) (uIcc a b ×ˢ U) :=
    fun q hq ↦ (e.symm.continuous.continuousAt.comp
      (hF q hq).continuousAt).continuousWithinAt
  have hc : ContinuousOn (fun s ↦ e.symm (F (s, y))) (uIcc a b) :=
    hFC.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs ↦ ⟨hs, hy⟩)
  simpa using (e.toContinuousLinearMap.intervalIntegral_comp_comm hc.intervalIntegrable)

/-- `app:ch_waves:thm:leading` and `app:ch_background:prop:bg-positive`:
joint smoothness of the variable-endpoint integral in the characteristic
exponential formula, on the entire open time-parameter product. -/
theorem contDiffOn_parametricIntervalIntegral {P : Type u}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {c : ℝ × P → ℝ} {I : Set ℝ} {U : Set P} {t₀ : ℝ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hU : IsOpen U)
    (hc : ContDiffOn ℝ ∞ c (I ×ˢ U)) (ht₀ : t₀ ∈ I) :
    ContDiffOn ℝ ∞ (fun q : ℝ × P ↦ ∫ s in t₀..q.1, c (s, q.2)) (I ×ˢ U) := by
  let F : ℝ × (ℝ × P) → ℝ := fun z ↦ c ((z.2.1 - t₀) * z.1 + t₀, z.2.2)
  have hF : ∀ z ∈ uIcc (0 : ℝ) 1 ×ˢ (I ×ˢ U), ContDiffAt ℝ ∞ F z := by
    intro z hz
    have hs : z.1 ∈ Icc (0 : ℝ) 1 := by simpa using hz.1
    have ht : (z.2.1 - t₀) * z.1 + t₀ ∈ I := by
      apply hIc.uIcc_subset ht₀ hz.2.1
      rcases le_total t₀ z.2.1 with h | h
      · rw [uIcc_of_le h]
        constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr h) hs.1,
          mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hs.2)]
      · rw [uIcc_of_ge h]
        constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr h) hs.1,
          mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hs.2)]
    exact (hc.contDiffAt (x := ((z.2.1 - t₀) * z.1 + t₀, z.2.2))
      ((hI.prod hU).mem_nhds ⟨ht, hz.2.2⟩)).comp z
      ((((contDiffAt_snd.fst.sub contDiffAt_const).mul contDiffAt_fst).add
        contDiffAt_const).prodMk contDiffAt_snd.snd)
  have hi := contDiffOn_fixedIntervalIntegral (hI.prod hU) hF
  apply ((contDiffOn_fst.sub contDiffOn_const).mul hi).congr
  intro q _
  simpa [F] using
    (intervalIntegral.smul_integral_comp_mul_add (fun s ↦ c (s, q.2))
      (a := 0) (b := 1) (q.1 - t₀) t₀).symm

end JanetCartan
