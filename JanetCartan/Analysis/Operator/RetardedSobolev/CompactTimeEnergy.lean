module

public import JanetCartan.Analysis.Operator.RetardedSobolev.WeightedTimeEnergy

/-!
# Uniform time bounds for smooth compactly supported cutoffs

For `app:ch_osc:prop:osc-retarded-tube`, the cutoff jet assumptions in the
quantitative time estimates follow from smoothness and compact support. The
common bound is chosen before the input. These are classical, time-only energies
on the rectangle, not yet the manuscript's full spatial Sobolev norms.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.RetardedSobolev
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The time derivative is evaluation in the time direction
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem timeDeriv_eq_fderiv {f : ℝ × Y → ℂ} (hf : Differentiable ℝ f) :
    timeDeriv f = fun x ↦ fderiv ℝ f x (1, 0) := by
  funext x
  exact ((hf x).hasFDerivAt.comp x.1
    (hasFDerivAt_prodMk_left x.1 x.2)).hasDerivAt.deriv

/-- Every time jet of a smooth function is jointly smooth
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem contDiff_timeJet {f : ℝ × Y → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ (timeJet j f) := by
  induction j with
  | zero => simpa only [timeJet_zero] using hf
  | succ j ih =>
    rw [timeJet_succ, timeDeriv_eq_fderiv (ih.differentiable (by simp))]
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- Time differentiation preserves compact support
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem hasCompactSupport_timeJet {f : ℝ × Y → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (j : ℕ) : HasCompactSupport (timeJet j f) := by
  induction j with
  | zero => simpa only [timeJet_zero] using hs
  | succ j ih =>
    rw [timeJet_succ, timeDeriv_eq_fderiv ((contDiff_timeJet hf j).differentiable (by simp))]
    exact ih.fderiv_apply ℝ (1, 0)

/-- A single bound controls all cutoff time jets through a fixed order
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem exists_timeJet_bound {f : ℝ × Y → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ x, ‖timeJet j f x‖ ≤ C := by
  induction m with
  | zero =>
    obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hs
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro j hj x
    have : j = 0 := by omega
    simpa only [this, timeJet_zero] using (hC x).trans (le_max_left C 0)
  | succ m ih =>
    obtain ⟨C, hC, hb⟩ := ih
    obtain ⟨D, hD⟩ := (contDiff_timeJet hf (m + 1)).continuous.bounded_above_of_compact_support
      (hasCompactSupport_timeJet hf hs (m + 1))
    refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
    intro j hj x
    by_cases h : j ≤ m
    · exact (hb j h x).trans (le_max_left _ _)
    · have heq : j = m + 1 := by omega
      subst j
      exact (hD x).trans (le_max_right _ _)


variable [MeasurableSpace Y] [BorelSpace Y]

/-- Both literal operators gain one time order, with a common constant
depending only on the smooth compactly supported cutoffs, order, and interval
(`app:ch_osc:prop:osc-retarded-tube`). Cutoff measurability and jet bounds are
proved here. Spatial and weak Sobolev assertions remain separate obligations. -/
theorem timeSobolev_bounds_of_contDiff_hasCompactSupport (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) (χin χout : ℝ × Y → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hsin : HasCompactSupport χin) (hsout : HasCompactSupport χout) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ × Y → ℂ,
      (∀ y, ContDiff ℝ m (fun t ↦ f (t, y))) → TimeJetsMemLp ν a b m f →
      TimeJetsMemLp ν a b (m + 1) (Retarded.lower a χin χout f) ∧
      TimeJetsMemLp ν a b (m + 1) (Retarded.upper b χin χout f) ∧
      timeSobolevEnergy ν a b (m + 1) (Retarded.lower a χin χout f) ≤
        C * timeSobolevEnergy ν a b m f ∧
      timeSobolevEnergy ν a b (m + 1) (Retarded.upper b χin χout f) ≤
        C * timeSobolevEnergy ν a b m f := by
  have hci : ContDiff ℝ ∞ (fun x ↦ (χin x : ℂ)) := Complex.ofRealCLM.contDiff.comp hin
  have hco : ContDiff ℝ ∞ (fun x ↦ (χout x : ℂ)) := Complex.ofRealCLM.contDiff.comp hout
  obtain ⟨Cin, hCin, hbi⟩ := exists_timeJet_bound hci (hsin.comp_left Complex.ofReal_zero) (m + 1)
  obtain ⟨Cout, hCout, hbo⟩ := exists_timeJet_bound hco (hsout.comp_left Complex.ofReal_zero) (m + 1)
  have hmi j : AEStronglyMeasurable
      (fun p : Y × ℝ ↦ timeJet j (fun x ↦ (χin x : ℂ)) (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))) :=
    ((contDiff_timeJet hci j).continuous.comp continuous_swap).aestronglyMeasurable
  have hmo j : AEStronglyMeasurable
      (fun p : Y × ℝ ↦ timeJet j (fun x ↦ (χout x : ℂ)) (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))) :=
    ((contDiff_timeJet hco j).continuous.comp continuous_swap).aestronglyMeasurable
  have htin (y : Y) : ContDiff ℝ (m + 1 : ℕ) (fun t ↦ χin (t, y)) :=
    (hin.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have htout (y : Y) : ContDiff ℝ (m + 1 : ℕ) (fun t ↦ χout (t, y)) :=
    (hout.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  let CL := timeMultiplierConstant (m + 1) Cout * (1 + (b - a) ^ 2) *
    timeMultiplierConstant m Cin
  let CU := timeMultiplierConstant (m + 1) Cin * (1 + (b - a) ^ 2) *
    timeMultiplierConstant m Cout
  have hCL : 0 ≤ CL := mul_nonneg
    (mul_nonneg (timeMultiplierConstant_nonneg _ _) (by positivity))
    (timeMultiplierConstant_nonneg _ _)
  refine ⟨max CL CU, hCL.trans (le_max_left _ _), ?_⟩
  intro f hfc hf
  have hl := lower_timeSobolev_succ_bound ν a b hab m χin χout f
    (fun y ↦ (htin y).of_le (by exact_mod_cast Nat.le_succ m)) htout hfc
    (fun j _ ↦ hmi j) (fun j _ ↦ hmo j) hCin hCout
    (fun j hj ↦ Filter.Eventually.of_forall (fun p ↦ hbi j (by omega) (p.2, p.1)))
    (fun j hj ↦ Filter.Eventually.of_forall (fun p ↦ hbo j hj (p.2, p.1))) hf
  have hu := upper_timeSobolev_succ_bound ν a b hab m χin χout f
    (fun y ↦ (htout y).of_le (by exact_mod_cast Nat.le_succ m)) htin hfc
    (fun j _ ↦ hmo j) (fun j _ ↦ hmi j) hCout hCin
    (fun j hj ↦ Filter.Eventually.of_forall (fun p ↦ hbo j (by omega) (p.2, p.1)))
    (fun j hj ↦ Filter.Eventually.of_forall (fun p ↦ hbi j hj (p.2, p.1))) hf
  have he : 0 ≤ timeSobolevEnergy ν a b m f := by
    unfold timeSobolevEnergy
    exact Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
  exact ⟨hl.1, hu.1,
    hl.2.trans (mul_le_mul_of_nonneg_right (le_max_left CL CU) he),
    hu.2.trans (mul_le_mul_of_nonneg_right (le_max_right CL CU) he)⟩
end JanetCartan.RetardedSobolev
