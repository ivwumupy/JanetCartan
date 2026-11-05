module

public import JanetCartan.Analysis.Operator.GradedInverse
public import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smoothing of the remaining inverse

The functional analytic argument of `app:ch_regular:lem:finite-propagation-inverse`.
The one-gain bounds for the actual residual and its literal adjoint, the coefficient
profile, and the negative Sobolev pairing inequality remain explicit inputs.
We prove the power bounds and dualize the whole adjoint power. Identifying the
graded levels and dual pairing with the supported/restriction Sobolev spaces is
required before applying these results to the manuscript's operators.
-/

@[expose] public noncomputable section

namespace JanetCartan.ArbitraryAccuracy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Constants in the additive one-gain induction of
`app:ch_regular:lem:finite-propagation-inverse`, independent of `L`. -/
def powerGainConstant (C D : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => C (j + 1) * (powerGainConstant C D j + D (j + 1))

/-- Nonnegative power constants in `app:ch_regular:lem:finite-propagation-inverse`. -/
theorem powerGainConstant_nonneg {C D : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j) (j : ℕ) :
    0 ≤ powerGainConstant C D j := by
  induction j with
  | zero => simp [powerGainConstant]
  | succ j ih => exact mul_nonneg (hC _) (add_nonneg ih (hD _))

/-- The complete `j`th power gains `j` derivatives with only `L^j`, from the
additive one-gain estimate (`app:ch_regular:lem:finite-propagation-inverse`). -/
theorem power_gain (G : GradedScale E) (K : E →L[ℝ] E)
    {C D a : ℕ → ℝ} {b : ℕ} {L : ℝ}
    (hK : ‖K‖ ≤ 1) (hL : 1 ≤ L)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    (hprofile : ∀ j, 1 + a (j + b) ≤ D j * L ^ j)
    (hgain : G.HasOneGain K C a b) (j : ℕ) (v : E) :
    (K ^ j) v ∈ G.level j ∧
    G.gradeNorm j ((K ^ j) v) ≤ powerGainConstant C D j * L ^ j * ‖v‖ := by
  have hbase : ∀ j, ‖(K ^ j) v‖ ≤ ‖v‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ']
      change ‖K ((K ^ j) v)‖ ≤ _
      exact ((K.le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right hK (norm_nonneg _)).trans (by simpa using ih)))
  induction j with
  | zero => simpa [powerGainConstant] using And.intro (G.mem_zero v) (le_refl ‖v‖)
  | succ j ih =>
    rw [pow_succ']
    change K ((K ^ j) v) ∈ G.level (j + 1) ∧ _
    refine ⟨hgain.regularity j _ ih.1, ?_⟩
    change G.gradeNorm (j + 1) (K ((K ^ j) v)) ≤ _
    have hpow : L ^ j ≤ L ^ (j + 1) := by
      simpa only [pow_succ, mul_one] using
        mul_le_mul_of_nonneg_left hL (pow_nonneg (by linarith) j)
    calc
      G.gradeNorm (j + 1) (K ((K ^ j) v))
          ≤ C (j + 1) * (G.gradeNorm j ((K ^ j) v) +
              (1 + a (j + 1 + b)) * ‖(K ^ j) v‖) := hgain.bound j _ ih.1
      _ ≤ C (j + 1) * (powerGainConstant C D j * L ^ (j + 1) * ‖v‖ +
              (D (j + 1) * L ^ (j + 1)) * ‖v‖) := by
        apply mul_le_mul_of_nonneg_left _ (hC _)
        apply add_le_add
        · exact ih.2.trans (by gcongr; exact powerGainConstant_nonneg hC hD j)
        · exact (mul_le_mul_of_nonneg_right (hprofile _) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (hbase j)
              (mul_nonneg (hD _) (pow_nonneg (by linarith) _)))
      _ = powerGainConstant C D (j + 1) * L ^ (j + 1) * ‖v‖ := by
        simp only [powerGainConstant]
        ring

/-- The remaining inverse estimate `app:ch_regular:eq:inverse-remainder`, once
duality has bounded `K^N h` in the base norm. The output regularity is proved by
the same one-gain induction and the same base-space Neumann inverse. -/
theorem inverse_remainder_of_base_power [CompleteSpace E]
    (G : GradedScale E) (K : E →L[ℝ] E)
    {C D a : ℕ → ℝ} {b : ℕ} {θ L ρ A CN : ℝ}
    (hK : ‖K‖ ≤ θ) (hθ : θ < 1) (hL : 1 ≤ L)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    (ha : ∀ j, 0 ≤ a j) (ham : Monotone a)
    (hprofile : ∀ j, 1 + a (j + b) ≤ D j * L ^ j)
    (hgain : G.HasOneGain K C a b) (N s : ℕ) (h : E)
    (hbase : ‖(K ^ N) h‖ ≤ CN * A * (L / ρ) ^ N) :
    neumannInverse K ((K ^ (N + s)) h) ∈ G.level s ∧
    G.gradeNorm s (neumannInverse K ((K ^ (N + s)) h)) ≤
      (inverseTameConstant θ C s * (powerGainConstant C D s + D s) * CN) *
        A * L ^ s * (L / ρ) ^ N := by
  have hpow := power_gain G K (hK.trans hθ.le) hL hC hD hprofile hgain s ((K ^ N) h)
  have heq : (K ^ (N + s)) h = (K ^ s) ((K ^ N) h) := by
    rw [Nat.add_comm, pow_add]
    rfl
  rw [heq]
  refine ⟨G.neumannInverse_mem K (hK.trans_lt hθ) hgain.regularity s hpow.1, ?_⟩
  have hnorm : ‖(K ^ s) ((K ^ N) h)‖ ≤ ‖(K ^ N) h‖ := by
    clear hpow heq
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ']
      change ‖K ((K ^ s) ((K ^ N) h))‖ ≤ _
      calc
        _ ≤ ‖K‖ * ‖(K ^ s) ((K ^ N) h)‖ := K.le_opNorm _
        _ ≤ 1 * ‖(K ^ s) ((K ^ N) h)‖ :=
          mul_le_mul_of_nonneg_right (hK.trans hθ.le) (norm_nonneg _)
        _ ≤ _ := by simpa using ih
  have hInv := (inverseTameConstant_pos hθ hC s).le
  have hP := powerGainConstant_nonneg hC hD s
  have hLp : 0 ≤ L ^ s := pow_nonneg (by linarith) s
  calc
    G.gradeNorm s (neumannInverse K ((K ^ s) ((K ^ N) h))) ≤
        inverseTameConstant θ C s * (G.gradeNorm s ((K ^ s) ((K ^ N) h)) +
          (1 + a (s + b)) * ‖(K ^ s) ((K ^ N) h)‖) :=
      G.neumannInverse_gradeNorm_le K hK hθ hC ha ham hgain s hpow.1
    _ ≤ inverseTameConstant θ C s *
        (powerGainConstant C D s * L ^ s * ‖(K ^ N) h‖ +
          (D s * L ^ s) * ‖(K ^ N) h‖) := by
      apply mul_le_mul_of_nonneg_left _ hInv
      apply add_le_add hpow.2
      exact (mul_le_mul_of_nonneg_right (hprofile s) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hnorm (mul_nonneg (hD s) hLp))
    _ = (inverseTameConstant θ C s * (powerGainConstant C D s + D s) * L ^ s) *
        ‖(K ^ N) h‖ := by ring
    _ ≤ (inverseTameConstant θ C s * (powerGainConstant C D s + D s) * L ^ s) *
        (CN * A * (L / ρ) ^ N) :=
      mul_le_mul_of_nonneg_left hbase (mul_nonneg (mul_nonneg hInv (add_nonneg hP (hD s))) hLp)
    _ = _ := by ring

section Hilbert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Dualize the entire adjoint power, retaining the test-space membership
(`app:ch_regular:lem:finite-propagation-inverse`). The pairing bound is the
negative Sobolev input, not a bound on the desired output. -/
theorem norm_power_le_of_dual_bound (H : GradedScale F) (K : F →L[ℝ] F)
    (N : ℕ) (h : F) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hdual : ∀ v, v ∈ H.level N → |inner ℝ h v| ≤ A * H.gradeNorm N v)
    (hmem : ∀ v, ((K ^ N).adjoint) v ∈ H.level N)
    (hbound : ∀ v, H.gradeNorm N (((K ^ N).adjoint) v) ≤ D * ‖v‖) :
    ‖(K ^ N) h‖ ≤ A * D := by
  have htest := hdual (((K ^ N).adjoint) ((K ^ N) h)) (hmem _)
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
    abs_of_nonneg (sq_nonneg _)] at htest
  have hsq : ‖(K ^ N) h‖ ^ 2 ≤ A * D * ‖(K ^ N) h‖ := by
    calc
      _ ≤ A * H.gradeNorm N (((K ^ N).adjoint) ((K ^ N) h)) := htest
      _ ≤ A * (D * ‖(K ^ N) h‖) := mul_le_mul_of_nonneg_left (hbound _) hA
      _ = _ := by ring
  by_cases hz : ‖(K ^ N) h‖ = 0
  · rw [hz]
    exact mul_nonneg hA hD
  · nlinarith [norm_pos_iff.mpr (show (K ^ N) h ≠ 0 from fun h ↦ hz (by simp [h]))]

/-- `app:ch_regular:eq:inverse-remainder` from one-gain estimates for `K` and
its literal Hilbert adjoint and the source's negative Sobolev pairing bound.
The two scales may differ: the adjoint scale represents the reversed
supported/restriction pair. The coefficient profile and source pairing must
still be established for the concrete spaces and complete residual. -/
theorem inverse_remainder_of_one_gain_and_duality
    (G H : GradedScale F) (K : F →L[ℝ] F)
    {C C' D a : ℕ → ℝ} {b : ℕ} {θ L ρ A CN : ℝ}
    (hK : ‖K‖ ≤ θ) (hθ : θ < 1) (hL : 1 ≤ L) (hρ : 0 < ρ)
    (hA : 0 ≤ A) (hCN : 0 ≤ CN)
    (hC : ∀ j, 0 ≤ C j) (hC' : ∀ j, 0 ≤ C' j) (hD : ∀ j, 0 ≤ D j)
    (ha : ∀ j, 0 ≤ a j) (ham : Monotone a)
    (hprofile : ∀ j, 1 + a (j + b) ≤ D j * L ^ j)
    (hgain : G.HasOneGain K C a b) (hgain' : H.HasOneGain K.adjoint C' a b)
    (N s : ℕ) (h : F)
    (hsource : ∀ v, v ∈ H.level N →
      |inner ℝ h v| ≤ (CN * A / ρ ^ N) * H.gradeNorm N v) :
    neumannInverse K ((K ^ (N + s)) h) ∈ G.level s ∧
    G.gradeNorm s (neumannInverse K ((K ^ (N + s)) h)) ≤
      (inverseTameConstant θ C s * (powerGainConstant C D s + D s) *
        (CN * powerGainConstant C' D N)) * A * L ^ s * (L / ρ) ^ N := by
  have hadj : (K ^ N).adjoint = K.adjoint ^ N := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_pow]
  have hadjNorm : ‖K.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hK.trans hθ.le
  have hp (v : F) := power_gain H K.adjoint hadjNorm hL hC' hD hprofile hgain' N v
  have hlow := norm_power_le_of_dual_bound H K N h
    (A := CN * A / ρ ^ N) (D := powerGainConstant C' D N * L ^ N)
    (div_nonneg (mul_nonneg hCN hA) (pow_nonneg hρ.le N))
    (mul_nonneg (powerGainConstant_nonneg hC' hD N) (pow_nonneg (by linarith) N))
    hsource (fun v ↦ by rw [hadj]; exact (hp v).1)
    (fun v ↦ by rw [hadj]; exact (hp v).2)
  have hlow' : ‖(K ^ N) h‖ ≤ (CN * powerGainConstant C' D N) * A * (L / ρ) ^ N := by
    convert hlow using 1
    rw [div_pow]
    ring
  exact inverse_remainder_of_base_power G K hK hθ hL hC hD ha ham hprofile hgain N s h hlow'

end Hilbert

end JanetCartan.ArbitraryAccuracy
