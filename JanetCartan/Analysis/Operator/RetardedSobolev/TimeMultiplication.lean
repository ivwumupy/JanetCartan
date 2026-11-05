module

public import JanetCartan.Analysis.Operator.RetardedSobolev.TimeEnergy
public import JanetCartan.Analysis.Operator.RetardedSobolev.Energy

/-!
# Cutoff multiplication for integer time energies

The all-order time Leibniz estimate used in `app:ch_osc:prop:osc-retarded-tube`.
These energies contain only time derivatives. The measurable bounded multiplier
jets are explicit inputs, and the conclusion includes L² membership of every
output jet. No spatial Sobolev or weak-derivative identification is asserted.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace JanetCartan.RetardedSobolev

variable {Y : Type*}

/-- The time Leibniz formula in `app:ch_osc:prop:osc-retarded-tube`. -/
theorem timeJet_mul (w f : ℝ × Y → ℂ) (j : ℕ)
    (hw : ∀ y, ContDiff ℝ j (fun t ↦ w (t, y)))
    (hf : ∀ y, ContDiff ℝ j (fun t ↦ f (t, y))) (x : ℝ × Y) :
    timeJet j (fun x ↦ w x * f x) x =
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℂ) * timeJet i w x * timeJet (j - i) f x := by
  exact iteratedDeriv_fun_mul (hw x.2).contDiffAt (hf x.2).contDiffAt

variable [MeasurableSpace Y]

/-- An explicit squared-energy multiplier constant for
`app:ch_osc:prop:osc-retarded-tube`, depending only on the order and cutoff jets. -/
def timeMultiplierConstant (m : ℕ) (C : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (j + 1 : ℝ) *
    ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * C) ^ 2

/-- Positivity of the Leibniz constant (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem timeMultiplierConstant_nonneg (m : ℕ) (C : ℝ) :
    0 ≤ timeMultiplierConstant m C := by
  unfold timeMultiplierConstant
  positivity

/-- Bounded cutoff multiplication at every nonnegative time order
(`app:ch_osc:prop:osc-retarded-tube`). The hypotheses concern the actual classical
jets, not an assumed operator bound. -/
theorem timeSobolev_mul_bound (ν : Measure Y) (a b : ℝ) (m : ℕ)
    (w f : ℝ × Y → ℂ)
    (hw : ∀ y, ContDiff ℝ m (fun t ↦ w (t, y)))
    (hfcont : ∀ y, ContDiff ℝ m (fun t ↦ f (t, y)))
    (hmw : ∀ j ≤ m, AEStronglyMeasurable (fun p : Y × ℝ ↦ timeJet j w (p.2, p.1))
      (ν.prod (volume.restrict (Icc a b))))
    {C : ℝ} (hC : 0 ≤ C)
    (hbw : ∀ j ≤ m, ∀ᵐ p : Y × ℝ ∂ν.prod (volume.restrict (Icc a b)),
      ‖timeJet j w (p.2, p.1)‖ ≤ C)
    (hf : TimeJetsMemLp ν a b m f) :
    TimeJetsMemLp ν a b m (fun x ↦ w x * f x) ∧
    timeSobolevEnergy ν a b m (fun x ↦ w x * f x) ≤
      timeMultiplierConstant m C * timeSobolevEnergy ν a b m f := by
  let μ := ν.prod (volume.restrict (Icc a b))
  have hterm (j : ℕ) (hj : j ≤ m) (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
      MemLp (fun p : Y × ℝ ↦ (j.choose i : ℂ) * timeJet i w (p.2, p.1) *
        timeJet (j - i) f (p.2, p.1)) 2 μ ∧
      (∫ p : Y × ℝ, ‖(j.choose i : ℂ) * timeJet i w (p.2, p.1) *
        timeJet (j - i) f (p.2, p.1)‖ ^ 2 ∂μ) ≤
        ((j.choose i : ℝ) * C) ^ 2 * timeSobolevEnergy ν a b m f := by
    have him : i ≤ m := by simp only [Finset.mem_range] at hi; omega
    have hjm : j - i ≤ m := (Nat.sub_le j i).trans hj
    have hb : ∀ᵐ p : Y × ℝ ∂μ, ‖(j.choose i : ℂ) * timeJet i w (p.2, p.1)‖ ≤
        (j.choose i : ℝ) * C := by
      filter_upwards [hbw i him] with p hp
      simpa only [norm_mul, Complex.norm_natCast] using
        mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (j.choose i))
    have h := mul_l2_bound _ _ ((hmw i him).const_mul _) (hf _ hjm)
      (mul_nonneg (Nat.cast_nonneg _) hC) hb
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left
      (timeJet_integral_sq_le ν a b m (j - i) f hjm) (sq_nonneg _))⟩
  have hjet (j : ℕ) (hj : j ≤ m) :
      MemLp (fun p : Y × ℝ ↦ timeJet j (fun x ↦ w x * f x) (p.2, p.1)) 2 μ ∧
      (∫ p : Y × ℝ, ‖timeJet j (fun x ↦ w x * f x) (p.2, p.1)‖ ^ 2 ∂μ) ≤
        ((j + 1 : ℝ) * ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * C) ^ 2) *
          timeSobolevEnergy ν a b m f := by
    simp_rw [timeJet_mul w f j
      (fun y ↦ (hw y).of_le (by exact_mod_cast hj))
      (fun y ↦ (hfcont y).of_le (by exact_mod_cast hj))]
    refine ⟨memLp_finsetSum _ (fun i hi ↦ (hterm j hj i hi).1), ?_⟩
    have hs := integral_sq_sum_le (μ := μ) (Finset.range (j + 1))
      (fun i (p : Y × ℝ) ↦ (j.choose i : ℂ) * timeJet i w (p.2, p.1) *
        timeJet (j - i) f (p.2, p.1)) (fun i hi ↦ (hterm j hj i hi).1)
    have hb := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi ↦ (hterm j hj i hi).2))
      (Nat.cast_nonneg (Finset.range (j + 1)).card : (0 : ℝ) ≤ _)
    convert hs.trans hb using 1; simp [Finset.sum_mul, mul_assoc]
  refine ⟨fun j hj ↦ (hjet j hj).1, ?_⟩
  unfold timeSobolevEnergy timeMultiplierConstant
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j hj ↦ (hjet j (by simp only [Finset.mem_range] at hj; omega)).2)

end JanetCartan.RetardedSobolev
