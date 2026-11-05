module

public import JanetCartan.Analysis.Operator.RetardedSobolev.TransverseJets

/-!
# Mixed derivative energies of the retarded primitive

The nonnegative-order classical estimate in `app:ch_osc:prop:osc-retarded-tube`,
before inserting the cutoffs. A finite family of transverse directions indexes
all words of derivatives, with time order at most `m` minus the word length.
For coordinate directions this includes every mixed Cartesian derivative through
order `m` (with repetitions). Integrability of every jet is part of the conclusion.
This module does not identify a completion with a weak or Fourier Sobolev space.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace JanetCartan.RetardedSobolev

variable {Y ι : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace Y] [Fintype ι]

/-- Sum of mixed squared L² derivative energies through total order `m`, for
`app:ch_osc:prop:osc-retarded-tube`. The finite direction family can be a coordinate
basis. The sum counts all ordered words, including the empty word. -/
def mixedSobolevEnergy (directions : ι → Y) (ν : Measure Y) (a b : ℝ)
    (m : ℕ) (f : ℝ × Y → ℂ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), ∑ word : Fin k → ι,
    timeSobolevEnergy ν a b (m - k) (transverseJet (List.ofFn (directions ∘ word)) f)

/-- L² membership of the actual mixed classical derivatives of total order at
most `m`, for `app:ch_osc:prop:osc-retarded-tube`. -/
def MixedJetsMemLp (directions : ι → Y) (ν : Measure Y) (a b : ℝ)
    (m : ℕ) (f : ℝ × Y → ℂ) : Prop :=
  ∀ k ≤ m, ∀ word : Fin k → ι,
    TimeJetsMemLp ν a b (m - k) (transverseJet (List.ofFn (directions ∘ word)) f)

/-- Mixed classical energies are nonnegative
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem mixedSobolevEnergy_nonneg (directions : ι → Y) (ν : Measure Y) (a b : ℝ)
    (m : ℕ) (f : ℝ × Y → ℂ) : 0 ≤ mixedSobolevEnergy directions ν a b m f := by
  unfold mixedSobolevEnergy timeSobolevEnergy
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _

variable [ProperSpace Y]

/-- Every transverse jet gains one time order under the lower primitive
(`app:ch_osc:prop:osc-retarded-tube`), with the same constant for every word. -/
theorem lower_one_transverseJet_timeSobolev_bound (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) {f : ℝ × Y → ℂ}
    (hfcont : ContDiff ℝ ∞ f) (vs : List Y) (hf : TimeJetsMemLp ν a b m (transverseJet vs f)) :
    TimeJetsMemLp ν a b (m + 1)
      (transverseJet vs (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f)) ∧
    timeSobolevEnergy ν a b (m + 1)
      (transverseJet vs (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f)) ≤
        (1 + (b - a) ^ 2) * timeSobolevEnergy ν a b m (transverseJet vs f) := by
  rw [transverseJet_lower_one a hfcont vs]
  exact lower_one_timeSobolev_bound ν a b hab m _
    (fun _ ↦ (contDiff_transverseJet hfcont vs).continuous.comp
      (continuous_id.prodMk continuous_const)) hf

/-- Every transverse jet gains one time order under the upper primitive
(`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem upper_one_transverseJet_timeSobolev_bound (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) {f : ℝ × Y → ℂ}
    (hfcont : ContDiff ℝ ∞ f) (vs : List Y) (hf : TimeJetsMemLp ν a b m (transverseJet vs f)) :
    TimeJetsMemLp ν a b (m + 1)
      (transverseJet vs (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f)) ∧
    timeSobolevEnergy ν a b (m + 1)
      (transverseJet vs (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f)) ≤
        (1 + (b - a) ^ 2) * timeSobolevEnergy ν a b m (transverseJet vs f) := by
  rw [transverseJet_upper_one b hfcont vs]
  exact upper_one_timeSobolev_bound ν a b hab m _
    (fun _ ↦ (contDiff_transverseJet hfcont vs).continuous.comp
      (continuous_id.prodMk continuous_const)) hf

/-- The lower primitive is bounded at every nonnegative total classical order
in `app:ch_osc:prop:osc-retarded-tube`. All mixed derivatives are included;
cutoff multiplication and weak Sobolev extension are separate steps. -/
theorem lower_one_mixedSobolev_bound (directions : ι → Y) (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) {f : ℝ × Y → ℂ} (hfcont : ContDiff ℝ ∞ f)
    (hf : MixedJetsMemLp directions ν a b m f) :
    MixedJetsMemLp directions ν a b m (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f) ∧
    mixedSobolevEnergy directions ν a b m (Retarded.lower a (fun _ ↦ 1) (fun _ ↦ 1) f) ≤
      (1 + (b - a) ^ 2) * mixedSobolevEnergy directions ν a b m f := by
  have h k (hk : k ≤ m) (word : Fin k → ι) :=
    lower_one_transverseJet_timeSobolev_bound ν a b hab (m - k) hfcont
      (List.ofFn (directions ∘ word)) (hf k hk word)
  constructor
  · intro k hk word j hj
    exact (h k hk word).1 j (hj.trans (Nat.le_succ _))
  · unfold mixedSobolevEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro word _
    exact (timeSobolevEnergy_mono ν a b (Nat.le_succ _) _).trans
      (h k (by simp only [Finset.mem_range] at hk; omega) word).2

/-- The upper primitive satisfies the same bound for every nonnegative total
classical order (`app:ch_osc:eq:retarded-literal-adjoint`). -/
theorem upper_one_mixedSobolev_bound (directions : ι → Y) (ν : Measure Y) [SFinite ν]
    (a b : ℝ) (hab : a ≤ b) (m : ℕ) {f : ℝ × Y → ℂ} (hfcont : ContDiff ℝ ∞ f)
    (hf : MixedJetsMemLp directions ν a b m f) :
    MixedJetsMemLp directions ν a b m (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f) ∧
    mixedSobolevEnergy directions ν a b m (Retarded.upper b (fun _ ↦ 1) (fun _ ↦ 1) f) ≤
      (1 + (b - a) ^ 2) * mixedSobolevEnergy directions ν a b m f := by
  have h k (hk : k ≤ m) (word : Fin k → ι) :=
    upper_one_transverseJet_timeSobolev_bound ν a b hab (m - k) hfcont
      (List.ofFn (directions ∘ word)) (hf k hk word)
  constructor
  · intro k hk word j hj
    exact (h k hk word).1 j (hj.trans (Nat.le_succ _))
  · unfold mixedSobolevEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro word _
    exact (timeSobolevEnergy_mono ν a b (Nat.le_succ _) _).trans
      (h k (by simp only [Finset.mem_range] at hk; omega) word).2

end JanetCartan.RetardedSobolev
