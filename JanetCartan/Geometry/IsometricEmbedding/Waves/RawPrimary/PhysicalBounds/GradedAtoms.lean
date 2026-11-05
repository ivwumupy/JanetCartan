module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Graded physical derivatives of oscillatory atoms

The phase-factor count in `app:ch_waves:eq:raw-physical-bound`: a partition
with `q` blocks in an order-`m` derivative costs `K^q L^(m-q)`.
These estimates are consumed by the literal raw-integral bound. The primitive
quotient estimates are supplied separately by the segment formula.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.RawPrimary

/-- The real derivatives of the unit complex oscillation, used in
`app:ch_waves:eq:raw-physical-bound`. -/
theorem iteratedDeriv_unitOscillation (m : ℕ) (t : ℝ) :
    iteratedDeriv m (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ))) t =
      Complex.I ^ m * Complex.exp (Complex.I * (t : ℂ)) := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv m
      (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ))) =
      (fun t : ℝ ↦ Complex.I ^ m * Complex.exp (Complex.I * (t : ℂ))) from funext ih]
    have hd := (((hasDerivAt_id t).ofReal_comp.const_mul Complex.I).cexp).const_mul
      (Complex.I ^ m)
    convert hd.deriv using 1 <;> simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]

/-- Every derivative of the outer oscillation has norm one; there is no
exponential loss depending on the phase value (`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_iteratedFDeriv_unitOscillation (m : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ m (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ))) t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_unitOscillation]
  simp [norm_pow, Complex.norm_exp_I_mul_ofReal]

/-- Exact grading of one Faà di Bruno term in
`app:ch_waves:eq:raw-physical-bound`. -/
theorem phasePartition_grade {m : ℕ} (p : OrderedFinpartition m)
    (s : ℕ → ℝ) (K L : ℝ) :
    (∏ i, s (p.partSize i) * K * L ^ (p.partSize i - 1)) =
      (∏ i, s (p.partSize i)) * K ^ p.length * L ^ (m - p.length) := by
  have he : ∑ i, (p.partSize i - 1) = m - p.length := by
    rw [Finset.sum_tsub_distrib _ (fun i _ ↦ p.partSize_pos i),
      CompositionBounds.sum_partSize]
    simp
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow_eq_pow_sum, he]

/-- Including the amplitude derivative preserves the exact count: an
order-`m` product term with `p.length` phase factors has grade
`K^p.length L^(m-p.length)` (`app:ch_waves:eq:raw-physical-bound`). -/
theorem phaseAmplitudePartition_grade {m i : ℕ} (hi : i ≤ m)
    (p : OrderedFinpartition i) (a s : ℕ → ℝ) (K L : ℝ) :
    (a (m - i) * L ^ (m - i)) *
        (∏ j, s (p.partSize j) * K * L ^ (p.partSize j - 1)) =
      (a (m - i) * ∏ j, s (p.partSize j)) * K ^ p.length * L ^ (m - p.length) := by
  rw [phasePartition_grade]
  have he : m - i + (i - p.length) = m - p.length := by
    have hp := p.length_le
    omega
  calc
    _ = (a (m - i) * ∏ j, s (p.partSize j)) * K ^ p.length *
        (L ^ (m - i) * L ^ (i - p.length)) := by ring
    _ = _ := by rw [← pow_add, he]

/-- Each graded monomial is bounded by the single physical scale in
`app:ch_waves:eq:raw-physical-bound`. -/
theorem phaseGrade_le_add_pow {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    {m q : ℕ} (hq : q ≤ m) : K ^ q * L ^ (m - q) ≤ (K + L) ^ m := by
  calc
    _ ≤ (K + L) ^ q * (K + L) ^ (m - q) :=
      mul_le_mul (pow_le_pow_left₀ hK (le_add_of_nonneg_right hL) _)
        (pow_le_pow_left₀ hL (le_add_of_nonneg_left hK) _)
        (pow_nonneg hL _) (pow_nonneg (add_nonneg hK hL) _)
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hq]

/-- The order-dependent coefficient of the exponential estimate. It depends
only on the primitive phase-jet constants, not on any frequency or inverse
frequency (`app:ch_waves:eq:raw-physical-bound`). -/
def phaseJetConstant (s : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ p : OrderedFinpartition m, ∏ i, s (p.partSize i)

/-- Positivity of the explicit phase-jet constant
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem phaseJetConstant_nonneg {s : ℕ → ℝ} {m : ℕ}
    (hs : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ s j) : 0 ≤ phaseJetConstant s m := by
  exact Finset.sum_nonneg fun p _ ↦ Finset.prod_nonneg fun i _ ↦
    hs _ (p.partSize_pos i) (p.partSize_le i)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The differentiated exponential estimate is derived from the chain rule
and primitive phase jets, with the exact number of phase factors retained
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_iteratedFDeriv_oscillation_le_graded {φ : E → ℝ} {x : E} {m : ℕ}
    (hφ : ContDiffAt ℝ m φ x) {s : ℕ → ℝ} {K L : ℝ}
    (hb : ∀ j, 1 ≤ j → j ≤ m → ‖iteratedFDeriv ℝ j φ x‖ ≤ s j * K * L ^ (j - 1)) :
    ‖iteratedFDeriv ℝ m (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ))) x‖ ≤
      ∑ p : OrderedFinpartition m,
        (∏ i, s (p.partSize i)) * K ^ p.length * L ^ (m - p.length) := by
  have he : ContDiffAt ℝ m (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ))) (φ x) :=
    (contDiffAt_const.mul Complex.ofRealCLM.contDiff.contDiffAt).cexp
  apply (CompositionBounds.norm_iteratedFDeriv_comp_le_partition_sum he hφ le_rfl).trans
  apply Finset.sum_le_sum
  intro p _
  rw [norm_iteratedFDeriv_unitOscillation, one_mul, ← phasePartition_grade]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    (fun i _ ↦ hb _ (p.partSize_pos i) (p.partSize_le i))

/-- Uniform physical derivative estimate for the oscillation alone, proved
from the primitive phase grading (`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_iteratedFDeriv_oscillation_le {φ : E → ℝ} {x : E} {m : ℕ}
    (hφ : ContDiffAt ℝ m φ x) {s : ℕ → ℝ} {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hs : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ s j)
    (hb : ∀ j, 1 ≤ j → j ≤ m → ‖iteratedFDeriv ℝ j φ x‖ ≤ s j * K * L ^ (j - 1)) :
    ‖iteratedFDeriv ℝ m (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ))) x‖ ≤
      phaseJetConstant s m * (K + L) ^ m := by
  apply (norm_iteratedFDeriv_oscillation_le_graded hφ hb).trans
  rw [phaseJetConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (phaseGrade_le_add_pow hK hL p.length_le)
    (Finset.prod_nonneg fun i _ ↦ hs _ (p.partSize_pos i) (p.partSize_le i))

/-- Coefficient of the Leibniz sum for the actual derivative amplitude in
`app:ch_waves:eq:raw-physical-bound`. Only the fixed primitive jet constants
and the derivative order enter this number. -/
def atomJetConstant (a s : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * phaseJetConstant s i * a (m - i)

/-- Nonnegativity of the fixed atom coefficient
(`app:ch_waves:eq:raw-physical-bound`). -/
theorem atomJetConstant_nonneg {a s : ℕ → ℝ} {m : ℕ}
    (ha : ∀ j ≤ m, 0 ≤ a j) (hs : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ s j) :
    0 ≤ atomJetConstant a s m := by
  apply Finset.sum_nonneg
  intro i hi
  have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (phaseJetConstant_nonneg (fun j hj hj' ↦ hs j hj (hj'.trans hi'))))
    (ha _ (Nat.sub_le _ _))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The physical estimate for a single oscillatory atom follows from the
primitive amplitude and phase grades. It applies in particular to derivative
amplitudes with the Frobenius matrix norm. No differentiated-exponential
bound is an input (`app:ch_waves:eq:raw-physical-bound`). -/
theorem norm_iteratedFDeriv_oscillatoryAtom_le
    {U : Set E} (hU : IsOpen U) {φ : E → ℝ} {A : E → F} {m : ℕ}
    (hφ : ContDiffOn ℝ m φ U) (hA : ContDiffOn ℝ m A U)
    {a s : ℕ → ℝ} {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (ha : ∀ j ≤ m, 0 ≤ a j) (hs : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ s j)
    {x : E} (hx : x ∈ U)
    (hAj : ∀ j ≤ m, ‖iteratedFDeriv ℝ j A x‖ ≤ a j * L ^ j)
    (hφj : ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j φ x‖ ≤ s j * K * L ^ (j - 1)) :
    ‖iteratedFDeriv ℝ m (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) • A y) x‖ ≤
      atomJetConstant a s m * (K + L) ^ m := by
  have he : ContDiffOn ℝ m (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ))) U :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)).cexp
  have hb := norm_iteratedFDerivWithin_smul_le he hA (hU.uniqueDiffOn) hx
    (n := m) le_rfl
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at hb
  apply hb.trans
  rw [atomJetConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hpi : 0 ≤ phaseJetConstant s i :=
    phaseJetConstant_nonneg (fun j hj hj' ↦ hs j hj (hj'.trans hi'))
  have hci : 0 ≤ (m.choose i : ℝ) * phaseJetConstant s i * a (m - i) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hpi) (ha _ (Nat.sub_le _ _))
  have hp := norm_iteratedFDeriv_oscillation_le
    ((hφ.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hi')) hK hL
    (fun j hj hj' ↦ hs j hj (hj'.trans hi'))
    (fun j hj hj' ↦ hφj j hj (hj'.trans hi'))
  calc
    _ ≤ (m.choose i : ℝ) * (phaseJetConstant s i * (K + L) ^ i) *
        (a (m - i) * L ^ (m - i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))
        (hAj _ (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hpi (pow_nonneg (add_nonneg hK hL) _)))
    _ = ((m.choose i : ℝ) * phaseJetConstant s i * a (m - i)) *
        ((K + L) ^ i * L ^ (m - i)) := by ring
    _ ≤ ((m.choose i : ℝ) * phaseJetConstant s i * a (m - i)) * (K + L) ^ m := by
      apply mul_le_mul_of_nonneg_left _ hci
      calc
        _ ≤ (K + L) ^ i * (K + L) ^ (m - i) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hL (le_add_of_nonneg_left hK) _) (pow_nonneg (add_nonneg hK hL) _)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hi']

end JanetCartan.RawPrimary
