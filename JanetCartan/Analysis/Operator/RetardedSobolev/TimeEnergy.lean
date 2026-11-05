module

public import JanetCartan.Analysis.Operator.RetardedSobolev.Concrete

/-!
# Integer time-derivative energies of the primitive

The time part of the argument in `app:ch_osc:prop:osc-retarded-tube` is an exact
energy recurrence. Here the exterior and interior weights are one; applying
Leibniz estimates to the weights is a separate step. These are anisotropic
(time-only) energies on a rectangle, not the full spatial Sobolev norms.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace JanetCartan.RetardedSobolev

variable {Y : Type*}

/-- The actual iterated time derivative in `app:ch_osc:prop:osc-retarded-tube`. -/
def timeJet (j : ℕ) (f : ℝ × Y → ℂ) (x : ℝ × Y) : ℂ :=
  iteratedDeriv j (fun t ↦ f (t, x.2)) x.1

/-- Order zero is the input itself (`app:ch_osc:prop:osc-retarded-tube`). -/
@[simp] theorem timeJet_zero (f : ℝ × Y → ℂ) : timeJet 0 f = f := by
  funext x
  simp [timeJet]

/-- The time jet recurrence for `app:ch_osc:prop:osc-retarded-tube`. -/
theorem timeJet_succ (j : ℕ) (f : ℝ × Y → ℂ) :
    timeJet (j + 1) f = timeDeriv (timeJet j f) := by
  funext x
  simp only [timeJet, timeDeriv, iteratedDeriv_succ]

/-- The time jet of the lower primitive (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem timeJet_lower_one_succ (a : ℝ) (f : ℝ × Y → ℂ)
    (hf : ∀ y, Continuous (fun t ↦ f (t, y))) (j : ℕ) :
    timeJet (j + 1) (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f) = timeJet j f := by
  funext x
  simpa only [timeJet, Complex.ofReal_one, one_mul] using
    iteratedDeriv_lower_one a (fun _ ↦ 1) f x.2 x.1 j (by simpa using hf x.2)

/-- The time jet of the upper primitive (`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem timeJet_upper_one_succ (b : ℝ) (f : ℝ × Y → ℂ)
    (hf : ∀ y, Continuous (fun t ↦ f (t, y))) (j : ℕ) :
    timeJet (j + 1) (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f) =
      fun x ↦ -timeJet j f x := by
  funext x
  simpa only [timeJet, Complex.ofReal_one, one_mul] using
    iteratedDeriv_upper_one b (fun _ ↦ 1) f x.2 x.1 j (by simpa using hf x.2)

variable [MeasurableSpace Y]

/-- The sum of squared L² norms of time derivatives through order `m` on the
rectangle in `app:ch_osc:prop:osc-retarded-tube`. Transverse derivatives are not
included. Use together with `TimeJetsMemLp` to assert integrability. -/
def timeSobolevEnergy (ν : Measure Y) (a b : ℝ) (m : ℕ) (f : ℝ × Y → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    ∫ p : Y × ℝ, ‖timeJet j f (p.2, p.1)‖ ^ 2 ∂ν.prod (volume.restrict (Icc a b))

/-- L² membership of the classical time jets through order `m`, for the
integer estimates in `app:ch_osc:prop:osc-retarded-tube`. This predicate alone
does not assert that these jets are weak derivatives of a nonsmooth input. -/
def TimeJetsMemLp (ν : Measure Y) (a b : ℝ) (m : ℕ) (f : ℝ × Y → ℂ) : Prop :=
  ∀ j ≤ m, MemLp (fun p : Y × ℝ ↦ timeJet j f (p.2, p.1)) 2
    (ν.prod (volume.restrict (Icc a b)))

/-- The order-zero energy is dominated by every integer time energy
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem integral_sq_le_timeSobolevEnergy (ν : Measure Y) (a b : ℝ) (m : ℕ)
    (f : ℝ × Y → ℂ) :
    (∫ p : Y × ℝ, ‖f (p.2, p.1)‖ ^ 2 ∂ν.prod (volume.restrict (Icc a b))) ≤
      timeSobolevEnergy ν a b m f := by
  simpa only [timeJet_zero, timeSobolevEnergy] using
    (Finset.single_le_sum (f := fun j ↦ ∫ p : Y × ℝ, ‖timeJet j f (p.2, p.1)‖ ^ 2
      ∂ν.prod (volume.restrict (Icc a b)))
      (fun j _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
      (show 0 ∈ Finset.range (m + 1) by simp))

/-- The exact lower time-energy recurrence from the primitive identity in
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem timeSobolevEnergy_lower_one_succ (ν : Measure Y) (a b : ℝ)
    (m : ℕ) (f : ℝ × Y → ℂ) (hf : ∀ y, Continuous (fun t ↦ f (t, y))) :
    timeSobolevEnergy ν a b (m + 1) (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f) =
      timeSobolevEnergy ν a b m f +
        ∫ p : Y × ℝ, ‖Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f (p.2, p.1)‖ ^ 2
          ∂ν.prod (volume.restrict (Icc a b)) := by
  unfold timeSobolevEnergy
  rw [Finset.sum_range_succ']
  simp only [timeJet_lower_one_succ a f hf, timeJet_zero]

/-- The same energy recurrence for the upper primitive; the endpoint sign
vanishes after squaring (`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem timeSobolevEnergy_upper_one_succ (ν : Measure Y) (a b : ℝ)
    (m : ℕ) (f : ℝ × Y → ℂ) (hf : ∀ y, Continuous (fun t ↦ f (t, y))) :
    timeSobolevEnergy ν a b (m + 1) (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f) =
      timeSobolevEnergy ν a b m f +
        ∫ p : Y × ℝ, ‖Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f (p.2, p.1)‖ ^ 2
          ∂ν.prod (volume.restrict (Icc a b)) := by
  unfold timeSobolevEnergy
  rw [Finset.sum_range_succ']
  simp only [timeJet_upper_one_succ b f hf, timeJet_zero, norm_neg]

/-- Every integer time energy gains one order under the lower primitive on the
rectangle (`app:ch_osc:prop:osc-retarded-tube`). This proves membership as well
as the bound; it is a time-only estimate before inserting smooth cutoffs. -/
theorem lower_one_timeSobolev_bound (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) (f : ℝ × Y → ℂ)
    (hcont : ∀ y, Continuous (fun t ↦ f (t, y))) (hf : TimeJetsMemLp ν a b m f) :
    TimeJetsMemLp ν a b (m + 1) (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f) ∧
    timeSobolevEnergy ν a b (m + 1) (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f) ≤
      (1 + (b - a) ^ 2) * timeSobolevEnergy ν a b m f := by
  have hf0 : MemLp (fun p : Y × ℝ ↦ f (p.2, p.1)) 2
      (ν.prod (volume.restrict (Icc a b))) := by simpa using hf 0 (Nat.zero_le m)
  have hL := Retarded.lower_l2_bound ν a b hab (fun _ ↦ 1) (fun _ ↦ 1) f
    (Cin := 1) (Cout := 1) (by norm_num) (by norm_num)
    (by intros; norm_num) (by intros; norm_num)
    aestronglyMeasurable_const aestronglyMeasurable_const hf0
  simp only [one_mul, one_pow] at hL
  constructor
  · intro j hj
    cases j with
    | zero => simpa using hL.1
    | succ j =>
      simp only [timeJet_lower_one_succ a f hcont]
      exact hf j (Nat.le_of_succ_le_succ hj)
  · rw [timeSobolevEnergy_lower_one_succ ν a b m f hcont]
    have hz := mul_le_mul_of_nonneg_left
      (integral_sq_le_timeSobolevEnergy ν a b m f) (sq_nonneg (b - a))
    nlinarith [hL.2]

/-- The all-order time estimate for the upper primitive
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem upper_one_timeSobolev_bound (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) (f : ℝ × Y → ℂ)
    (hcont : ∀ y, Continuous (fun t ↦ f (t, y))) (hf : TimeJetsMemLp ν a b m f) :
    TimeJetsMemLp ν a b (m + 1) (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f) ∧
    timeSobolevEnergy ν a b (m + 1) (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f) ≤
      (1 + (b - a) ^ 2) * timeSobolevEnergy ν a b m f := by
  have hf0 : MemLp (fun p : Y × ℝ ↦ f (p.2, p.1)) 2
      (ν.prod (volume.restrict (Icc a b))) := by simpa using hf 0 (Nat.zero_le m)
  have hU := Retarded.upper_l2_bound ν a b hab (fun _ ↦ 1) (fun _ ↦ 1) f
    (Cin := 1) (Cout := 1) (by norm_num) (by norm_num)
    (by intros; norm_num) (by intros; norm_num)
    aestronglyMeasurable_const aestronglyMeasurable_const hf0
  simp only [one_mul, one_pow] at hU
  constructor
  · intro j hj
    cases j with
    | zero => simpa using hU.1
    | succ j =>
      simp only [timeJet_upper_one_succ b f hcont]
      exact (hf j (Nat.le_of_succ_le_succ hj)).neg
  · rw [timeSobolevEnergy_upper_one_succ ν a b m f hcont]
    have hz := mul_le_mul_of_nonneg_left
      (integral_sq_le_timeSobolevEnergy ν a b m f) (sq_nonneg (b - a))
    nlinarith [hU.2]

/-- Each time jet is dominated by the total time energy
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem timeJet_integral_sq_le (ν : Measure Y) (a b : ℝ) (m j : ℕ)
    (f : ℝ × Y → ℂ) (hj : j ≤ m) :
    (∫ p : Y × ℝ, ‖timeJet j f (p.2, p.1)‖ ^ 2 ∂ν.prod (volume.restrict (Icc a b))) ≤
      timeSobolevEnergy ν a b m f := by
  unfold timeSobolevEnergy
  exact Finset.single_le_sum (f := fun k ↦ ∫ p : Y × ℝ, ‖timeJet k f (p.2, p.1)‖ ^ 2
    ∂ν.prod (volume.restrict (Icc a b)))
    (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (Finset.mem_range.mpr (by omega))

/-- Time energies increase with the order (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem timeSobolevEnergy_mono (ν : Measure Y) (a b : ℝ) {m k : ℕ} (hmk : m ≤ k)
    (f : ℝ × Y → ℂ) :
    timeSobolevEnergy ν a b m f ≤ timeSobolevEnergy ν a b k f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hmk 1))
  intro j _ _
  exact integral_nonneg (fun _ ↦ sq_nonneg _)

end JanetCartan.RetardedSobolev
