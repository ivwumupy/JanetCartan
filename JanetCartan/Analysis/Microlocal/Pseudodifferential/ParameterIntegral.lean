module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Differentiating finite Taylor integrals

Parameter integrals over the unit interval used in
`app:ch_regular_base:eq:actual-pdo-remainder`. Smoothness is assumed jointly in
the external parameter and the integration variable. Each quantitative estimate
uses only the indicated number of external derivatives; it loses no derivatives.
-/

open MeasureTheory Filter Set
open scoped ContDiff Topology

@[expose] public noncomputable section
universe u v
namespace JanetCartan.Pseudodifferential
variable {E : Type u} {F : Type (max u v)} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
/-- `app:ch_regular_base:eq:actual-pdo-remainder`: joint smoothness of the
external derivative of a smooth Taylor integrand. -/
theorem contDiff_parameterFDeriv (g : E × ℝ → F) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p : E × ℝ ↦ fderiv ℝ (fun x ↦ g (x, p.2)) p.1) := by
  have h : ContDiff ℝ ∞ (fun q : (E × ℝ) × E ↦ g (q.2, q.1.2)) :=
    hg.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact h.fderiv contDiff_fst (by simp)

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: the external derivative
passes through the actual Taylor integral. The dominating bound is obtained
locally from compactness, and is not an additional hypothesis. -/
theorem hasFDerivAt_unitIntervalIntegral (g : E × ℝ → F)
    (hg : ContDiff ℝ ∞ g) (x : E) :
    HasFDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, g (x, t))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun x ↦ g (x, t)) x) x := by
  let G := fun p : E × ℝ ↦ fderiv ℝ (fun x ↦ g (x, p.2)) p.1
  have hG : ContDiff ℝ ∞ G := contDiff_parameterFDeriv g hg
  have : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
      hG.continuous.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun x t ↦ G (x, t)) (bound := fun _ ↦ C)
      (s := Metric.ball x 1) (Metric.ball_mem_nhds x zero_lt_one)
  · exact Eventually.of_forall fun z ↦
      (hg.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hG.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro t ht z hz
    have ht' : 0 < t ∧ t ≤ 1 := by simpa using ht
    exact hC (z, t) ⟨Metric.ball_subset_closedBall hz, ht'.1.le, ht'.2⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t _ z _ ↦
      ((hg.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) z).hasFDerivAt

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: at every finite order,
uniform bounds for the external derivatives of the integrand bound the same
order of derivatives of its integral, with constant one. -/
theorem norm_iteratedFDeriv_unitIntervalIntegral_le (n : ℕ) :
    ∀ {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : E × ℝ → F), ContDiff ℝ ∞ g → ∀ (x : E) (M : ℝ),
      (∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ n (fun z ↦ g (z, t)) x‖ ≤ M) →
      ‖iteratedFDeriv ℝ n (fun z ↦ ∫ t in (0 : ℝ)..1, g (z, t)) x‖ ≤ M := by
  induction n with
  | zero =>
    intro F _ _ g _ x M hM
    simp only [norm_iteratedFDeriv_zero] at *
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) ?_).trans_eq (by simp)
    intro t ht
    have ht' : 0 < t ∧ t ≤ 1 := by simpa using ht
    exact hM t ⟨ht'.1.le, ht'.2⟩
  | succ n ih =>
    intro F _ _ g hg x M hM
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ (fun z ↦ ∫ t in (0 : ℝ)..1, g (z, t)) =
        fun z ↦ ∫ t in (0 : ℝ)..1, fderiv ℝ (fun z ↦ g (z, t)) z := by
      funext z
      exact (hasFDerivAt_unitIntervalIntegral g hg z).fderiv
    rw [hd]
    refine ih (fun p : E × ℝ ↦ fderiv ℝ (fun z ↦ g (z, p.2)) p.1) ?_ x M ?_
    · exact contDiff_parameterFDeriv g hg
    · intro t ht
      simpa only [norm_iteratedFDeriv_fderiv] using hM t ht

/-- `app:ch_regular_base:eq:actual-pdo-remainder`: smooth Taylor integrands
give smooth parameter integrals. -/
theorem contDiff_unitIntervalIntegral (g : E × ℝ → F) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in (0 : ℝ)..1, g (x, t)) := by
  have aux (n : ℕ) : ∀ {F : Type (max u v)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : E × ℝ → F), ContDiff ℝ ∞ g →
      ContDiff ℝ n (fun x ↦ ∫ t in (0 : ℝ)..1, g (x, t)) := by
    intro F _ _ g hg
    have hdiff : Differentiable ℝ (fun x ↦ ∫ t in (0 : ℝ)..1, g (x, t)) :=
      fun x ↦ (hasFDerivAt_unitIntervalIntegral g hg x).differentiableAt
    induction n generalizing F with
    | zero => exact contDiff_zero.mpr hdiff.continuous
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = n + 1 by simp, contDiff_succ_iff_fderiv]
      refine ⟨hdiff, by simp, ?_⟩
      have hd : fderiv ℝ (fun z ↦ ∫ t in (0 : ℝ)..1, g (z, t)) =
          fun z ↦ ∫ t in (0 : ℝ)..1, fderiv ℝ (fun z ↦ g (z, t)) z := by
        funext z
        exact (hasFDerivAt_unitIntervalIntegral g hg z).fderiv
      rw [hd]
      exact ih _ (contDiff_parameterFDeriv g hg) (fun x ↦
        (hasFDerivAt_unitIntervalIntegral _ (contDiff_parameterFDeriv g hg) x).differentiableAt)
  exact contDiff_infty.mpr fun n ↦ aux n g hg

end JanetCartan.Pseudodifferential
