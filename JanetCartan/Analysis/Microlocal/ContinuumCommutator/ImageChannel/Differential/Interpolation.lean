module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Interpolation.Coefficients
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Interpolation.Sobolev

/-!
# Single-high interpolation for the image-normal commutator

For `app:ch_background:eq:bg-commutator`, the literal image normal has two
varying coefficient factors. A fixed first-derivative budget and a common
high jet budget give exponents `(p - 1)₊ / s` and `(q - 1)₊ / s` by
`app:lem:elementary-interpolation-jets`. The derivative count leaves enough
exponent for the lower Sobolev datum, so the high budget occurs only once,
multiplying L². Constants precede both coefficients and the high budget.

The consumer is the finite commutator assembly of `imageNormal_eq_finiteFactors`
in the sibling `Factorization` module. Its actual coefficients and fixed masks
must still be supplied by that construction; this module proves the quantitative
interpolation implication, with no commutator estimate assumed.

The primitive producers `ContinuumRow.ImageGeometry.exists_reference_imageChannel`
and `ContinuumRow.HistoryImage.exists_imageChannel` give global coefficient jets
bounded by `C m * (1 + cNorm K (m + 2) F)`. The parent must take common finite
budgets for those same coefficients, deriving the fixed first-derivative budget
from its low map bounds and retaining map order `s + 3` for the high budget here.
-/

public noncomputable section

open scoped ContDiff
namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open PeriodicSobolevSpace

private theorem coefficient_exponents_le {s p q r : ℕ} (hr : r ≤ s)
    (hcount : p + q + r ≤ s + 1) :
    ((p - 1 : ℕ) : ℝ) / s + ((q - 1 : ℕ) : ℝ) / s ≤ 1 - (r : ℝ) / s := by
  by_cases hs : s = 0
  · simp [hs]
  have hspos : 0 < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hnat : (p - 1) + (q - 1) + r ≤ s := by omega
  have hreal : ((p - 1 : ℕ) : ℝ) + ((q - 1 : ℕ) : ℝ) + r ≤ s := by
    exact_mod_cast hnat
  rw [← add_div]
  calc
    _ ≤ ((s : ℝ) - r) / s := div_le_div_of_nonneg_right (by linarith) hspos.le
    _ = _ := by rw [sub_div, div_self hspos.ne']

/-- `app:ch_background:eq:bg-commutator` and
`app:lem:elementary-interpolation-jets`: two varying scalar coefficient-jet
factors times a lower periodic Sobolev norm cost only one high coefficient
budget times L². The positive constant depends only on `n`, `s`, and the fixed
low budget `M`, and precedes `a`, `b`, `H`, the derivative orders and the datum.
The statement includes `s = 0`, `n = 0`, and `H = 0`.

The image-normal assembly must instantiate the primitive jets on its same
coefficients; neither coefficient interpolation nor datum interpolation is a
premise. Source and measurement masks are fixed inputs to that assembly. -/
theorem exists_two_coefficient_jet_sobolev_bound (n s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : Torus n → ℝ),
      IsSmoothPeriodic a → IsSmoothPeriodic b → ∀ H : ℝ, 0 ≤ H →
      (∀ j ≤ 1, ∀ x, ‖iteratedFDeriv ℝ j (periodicLift a) x‖ ≤ M) →
      (∀ j ≤ 1, ∀ x, ‖iteratedFDeriv ℝ j (periodicLift b) x‖ ≤ M) →
      (∀ j ≤ s + 1, ∀ x, ‖iteratedFDeriv ℝ j (periodicLift a) x‖ ≤ H) →
      (∀ j ≤ s + 1, ∀ x, ‖iteratedFDeriv ℝ j (periodicLift b) x‖ ≤ H) →
      ∀ p q r : ℕ, r ≤ s → p + q + r ≤ s + 1 →
      ∀ u : PeriodicSobolevSpace n (EuclideanSpace ℝ (Fin n)) s,
        cNorm (fundamentalCell n) p (periodicLift a) *
          cNorm (fundamentalCell n) q (periodicLift b) *
          (periodicSobolevScale n (EuclideanSpace ℝ (Fin n))).gradeNorm r (toL2 s u) ≤
            C * (‖u‖ + (1 + H) * ‖toL2 s u‖) := by
  obtain ⟨K, hK, hprofile⟩ := exists_coefficient_jet_profile n s hM
  refine ⟨K ^ 2, by positivity, ?_⟩
  intro a b ha hb H hH haM hbM haH hbH p q r hr hcount u
  have hap := hprofile a ha H hH haM haH p (by omega)
  have hbq := hprofile b hb H hH hbM hbH q (by omega)
  have hproduct : cNorm (fundamentalCell n) p (periodicLift a) *
      cNorm (fundamentalCell n) q (periodicLift b) ≤
        K ^ 2 * (1 + H) ^ (1 - (r : ℝ) / s) := by
    calc
      _ ≤ (K * (1 + H) ^ (((p - 1 : ℕ) : ℝ) / s)) *
          (K * (1 + H) ^ (((q - 1 : ℕ) : ℝ) / s)) :=
        mul_le_mul hap hbq (cNorm_nonneg _ _ _) (by positivity)
      _ = K ^ 2 * (1 + H) ^
          (((p - 1 : ℕ) : ℝ) / s + ((q - 1 : ℕ) : ℝ) / s) := by
        rw [Real.rpow_add (by positivity)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith)
          (coefficient_exponents_le hr hcount)) (sq_nonneg K)
  calc
    _ ≤ (K ^ 2 * (1 + H) ^ (1 - (r : ℝ) / s)) *
        (periodicSobolevScale n (EuclideanSpace ℝ (Fin n))).gradeNorm r (toL2 s u) :=
      mul_le_mul_of_nonneg_right hproduct (GradedScale.gradeNorm_nonneg _ _ _)
    _ = K ^ 2 * ((1 + H) ^ (1 - (r : ℝ) / s) *
        (periodicSobolevScale n (EuclideanSpace ℝ (Fin n))).gradeNorm r (toL2 s u)) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (periodic_gradeNorm_weighted_interpolate hr (by positivity) u) (sq_nonneg K)

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
