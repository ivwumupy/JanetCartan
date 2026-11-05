module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.WeakTransfer
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Fourier.IntegerDerivatives
public import JanetCartan.Analysis.Fourier.Periodic.Cutoff.Scalar

/-!
# Finite Sobolev energy of the actual row coefficients

For `app:ch_osc:eq:amplitude-row`, weak derivatives transfer through the fixed
quotient chart and Parseval controls the weighted coefficients.  All derivatives
in this leaf are genuine L² distributional derivatives.  The same argument at
the combined-position order serves part (ii) of
`app:ch_osc:lem:osc-amplitude`.
-/

@[expose] public noncomputable section

open MeasureTheory LineDeriv
open scoped SchwartzMap
open JanetCartan.Pseudodifferential JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.AmplitudeBound.RowCoefficients

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)

private def pairEnergy (s : ℕ) (u : PeriodicL2 d ℂ) (k : Fin d → ℤ) : ℝ :=
  (1 + frequencyNorm k ^ 2) ^ s *
    (‖(periodicFourierCoeff u k).1‖ ^ 2 + ‖(periodicFourierCoeff u k).2‖ ^ 2)

private theorem weak_derivative_energy (s : ℕ) (u : PeriodicL2 d ℂ)
    (B : ℝ)
    (h : ∀ is : List (Fin d), is.length ≤ s →
      ∃ v : PeriodicL2 d ℂ, HasPeriodicWeakDerivativeList is u v ∧ ‖v‖ ≤ B) :
    ∃ b : ℝ, HasSum (pairEnergy s u) b ∧ b ≤ (d + 1 : ℝ) ^ s * B ^ 2 := by
  classical
  induction s generalizing u with
  | zero =>
    obtain ⟨v, hv, hnv⟩ := h [] (by simp)
    have he : v = u := (hasPeriodicWeakDerivativeList_nil _ _).mp hv
    have hn : ‖u‖ ≤ B := he ▸ hnv
    refine ⟨‖u‖ ^ 2, ?_, ?_⟩
    · have hh := hasSum_sq_periodicFourierCoeff (Lp.memLp u)
      rw [periodicL2Norm_coe] at hh
      exact hh.congr_fun (fun k ↦ by simp [pairEnergy])
    · simpa only [pow_zero, one_mul] using pow_le_pow_left₀ (norm_nonneg u) hn 2
  | succ s ih =>
    obtain ⟨b, hb, hnb⟩ := ih u (fun is his ↦ h is (his.trans (Nat.le_succ s)))
    choose v hv hnv using fun i : Fin d ↦ h [i] (by simp)
    have hd (i : Fin d) : HasPeriodicWeakDerivative i u (v i) :=
      (hasPeriodicWeakDerivativeList_singleton _ _ _).mp (hv i)
    have hh (i : Fin d) (is : List (Fin d)) (his : is.length ≤ s) :
        ∃ w : PeriodicL2 d ℂ, HasPeriodicWeakDerivativeList is (v i) w ∧ ‖w‖ ≤ B := by
      obtain ⟨w, hw, hnw⟩ := h (is ++ [i]) (by simpa using Nat.succ_le_succ his)
      exact ⟨w, hw.of_append_singleton (hd i), hnw⟩
    choose c hc hnc using fun i : Fin d ↦ ih (v i) (hh i)
    refine ⟨b + ∑ i, c i, ?_, ?_⟩
    · apply (hb.add (hasSum_sum (s := Finset.univ) (fun i _ ↦ hc i))).congr_fun
      intro k
      simp only [pairEnergy, (hd _).sq_periodicFourierCoeff]
      rw [pow_succ, ← Finset.mul_sum, ← Finset.sum_mul, ← frequencyNorm_sq_eq_sum]
      ring
    · calc
        b + ∑ i, c i ≤ (d + 1 : ℝ) ^ s * B ^ 2 +
            ∑ _i : Fin d, (d + 1 : ℝ) ^ s * B ^ 2 :=
          add_le_add hnb (Finset.sum_le_sum (fun i _ ↦ hnc i))
        _ = (d + 1 : ℝ) ^ (s + 1) * B ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [pow_succ]
          ring

private theorem exists_ordered_derivative (s : ℕ) (is : List (Fin d))
    (u : L²) (hu : MemFourierSobolev ((s + is.length : ℕ) : ℝ) u) :
    ∃ v : L², MemFourierSobolev (s : ℝ) v ∧
      orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E))
        is (u : 𝓢'(E, ℂ)) = (v : 𝓢'(E, ℂ)) ∧
      fourierSobolevNorm (s : ℝ) v ≤
        (2 * Real.pi) ^ is.length * fourierSobolevNorm ((s + is.length : ℕ) : ℝ) u := by
  induction is generalizing s u with
  | nil =>
    refine ⟨u, by simpa using hu, rfl, ?_⟩
    simp
  | cons i is ih =>
    have hu' : MemFourierSobolev (((s + 1) + is.length : ℕ) : ℝ) u := by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hu
    obtain ⟨v, hv, he, hn⟩ := ih (s + 1) u hu'
    have hv' : MemFourierSobolev ((s : ℝ) + 1) v := by
      simpa only [Nat.cast_add, Nat.cast_one] using hv
    obtain ⟨w, hw⟩ := hv'.exists_coordinateDerivatives (by positivity)
    refine ⟨w i, (hw i).2, ?_, ?_⟩
    · simp only [orderedTransferAction, he]
      simpa only [HasEuclideanL2CoordinateDerivative, euclideanCoordinateDerivative,
        EuclideanSpace.basisFun_apply] using (hw i).1
    · have hb := (hw i).1.fourierSobolevNorm_le (by positivity) hv'
      have hn' : fourierSobolevNorm ((s : ℝ) + 1) v ≤
          (2 * Real.pi) ^ is.length *
            fourierSobolevNorm (((s + 1) + is.length : ℕ) : ℝ) u := by
        simpa only [Nat.cast_add, Nat.cast_one] using hn
      refine (hb.trans (mul_le_mul_of_nonneg_left hn' (by positivity))).trans_eq ?_
      have ho : s + 1 + is.length = s + (i :: is).length := by
        simp only [List.length_cons]
        omega
      rw [ho, List.length_cons, pow_succ]
      ring

/-- A supported finite-Sobolev row has all periodic weak derivatives through
the original order, with a constant independent of the row.  These are the
actual chart representatives used in `app:ch_osc:eq:amplitude-row`. -/
theorem exists_supported_periodic_weak_derivatives {r : ℝ} (hr : r < 1 / 2)
    (s : ℕ) (u : L²)
    (hs : ∀ᵐ x ∂volume, x ∉ chartBox r → u x = 0)
    (hu : MemFourierSobolev (s : ℝ) u) :
    ∀ is : List (Fin d), is.length ≤ s →
      ∃ v : PeriodicL2 d ℂ,
        HasPeriodicWeakDerivativeList is (toTorus (𝕜 := ℂ) u) v ∧
        ‖v‖ ≤ (1 + 2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ) u := by
  obtain ⟨χ⟩ := nonempty_sourceCutoff (d := d) hr
  intro is his
  have hu' : MemFourierSobolev ((0 + is.length : ℕ) : ℝ) u :=
    hu.mono (by exact_mod_cast (show 0 + is.length ≤ s by simpa using his))
  obtain ⟨v, _, he, hn⟩ := exists_ordered_derivative 0 is u hu'
  refine ⟨toTorus (𝕜 := ℂ) (χ.localize v),
    hasPeriodicWeakDerivativeList_of_chart hr χ is u v hs he, ?_⟩
  have hp : (2 * Real.pi) ^ is.length ≤ (1 + 2 * Real.pi) ^ s :=
    (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith [Real.pi_pos]) his)
  calc
    ‖toTorus (𝕜 := ℂ) (χ.localize v)‖ ≤ ‖v‖ :=
      (norm_toTorusFun_le _).trans (χ.norm_localize_le _)
    _ ≤ (2 * Real.pi) ^ is.length * fourierSobolevNorm (is.length : ℝ) u := by
      simpa only [Nat.zero_add, Nat.cast_zero, fourierSobolevNorm_zero] using hn
    _ ≤ (1 + 2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ) u :=
      mul_le_mul hp (fourierSobolevNorm_mono hu (by exact_mod_cast his))
        (fourierSobolevNorm_nonneg _ _) (by positivity)

/-- Parseval bounds the actual torus row energy by the original integer
Euclidean Sobolev norm.  No classical source derivatives are hypotheses
(`app:ch_osc:eq:amplitude-row`). -/
theorem supported_periodic_pair_energy {r : ℝ} (hr : r < 1 / 2)
    (s : ℕ) (u : L²)
    (hs : ∀ᵐ x ∂volume, x ∉ chartBox r → u x = 0)
    (hu : MemFourierSobolev (s : ℝ) u) :
    Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ s *
      (‖(periodicFourierCoeff (toTorus (𝕜 := ℂ) u) k).1‖ ^ 2 +
       ‖(periodicFourierCoeff (toTorus (𝕜 := ℂ) u) k).2‖ ^ 2)) ∧
    (∑' k, (1 + frequencyNorm k ^ 2) ^ s *
      (‖(periodicFourierCoeff (toTorus (𝕜 := ℂ) u) k).1‖ ^ 2 +
       ‖(periodicFourierCoeff (toTorus (𝕜 := ℂ) u) k).2‖ ^ 2)) ≤
      (d + 1 : ℝ) ^ s *
        ((1 + 2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ) u) ^ 2 := by
  obtain ⟨b, hb, hn⟩ := weak_derivative_energy s (toTorus (𝕜 := ℂ) u)
    ((1 + 2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ) u)
    (exists_supported_periodic_weak_derivatives hr s u hs hu)
  exact ⟨hb.summable, hb.tsum_eq.trans_le hn⟩

private theorem coefficient_eq_pair (u : PeriodicL2 d ℂ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff u k =
      (periodicFourierCoeff u k).1 + Complex.I * (periodicFourierCoeff u k).2 := by
  have hr : Integrable (fun x ↦ (UnitAddTorus.mFourier (-k) x).re • u x) :=
    ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
      ((Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous
        ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)
  have hi : Integrable (fun x ↦ (UnitAddTorus.mFourier (-k) x).im • u x) :=
    ((Lp.memLp u).integrable (by norm_num)).smul_of_top_right
      ((Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous
        ).memLp_top_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) volume)
  rw [mFourierCoeff_eq_volume_integral]
  calc
    _ = ∫ x, (UnitAddTorus.mFourier (-k) x).re • u x +
        Complex.I * ((UnitAddTorus.mFourier (-k) x).im • u x) := by
      congr 1
      funext x
      rw [Complex.real_smul, Complex.real_smul]
      have he := Complex.re_add_im (UnitAddTorus.mFourier (-k) x)
      linear_combination -he * u x
    _ = _ := by rw [integral_add hr (hi.const_mul Complex.I), integral_const_mul]; rfl

private theorem coefficient_sq_le_pair (u : PeriodicL2 d ℂ) (k : Fin d → ℤ) :
    ‖UnitAddTorus.mFourierCoeff u k‖ ^ 2 ≤
      2 * (‖(periodicFourierCoeff u k).1‖ ^ 2 +
        ‖(periodicFourierCoeff u k).2‖ ^ 2) := by
  rw [coefficient_eq_pair]
  have h := norm_add_le (periodicFourierCoeff u k).1
    (Complex.I * (periodicFourierCoeff u k).2)
  rw [_root_.norm_mul, Complex.norm_I, one_mul] at h
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖(periodicFourierCoeff u k).1‖ - ‖(periodicFourierCoeff u k).2‖)]

/-- The actual complex coefficients satisfy the finite-order energy estimate.
The real-pair Parseval convention is converted without a regularity loss
(`app:ch_osc:eq:amplitude-row`). -/
theorem supported_periodic_coefficient_energy {r : ℝ} (hr : r < 1 / 2)
    (s : ℕ) (u : L²)
    (hs : ∀ᵐ x ∂volume, x ∉ chartBox r → u x = 0)
    (hu : MemFourierSobolev (s : ℝ) u) :
    Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ s *
      ‖UnitAddTorus.mFourierCoeff (toTorus (𝕜 := ℂ) u) k‖ ^ 2) ∧
    (∑' k, (1 + frequencyNorm k ^ 2) ^ s *
      ‖UnitAddTorus.mFourierCoeff (toTorus (𝕜 := ℂ) u) k‖ ^ 2) ≤
      2 * ((d + 1 : ℝ) ^ s *
        ((1 + 2 * Real.pi) ^ s * fourierSobolevNorm (s : ℝ) u) ^ 2) := by
  obtain ⟨hp, hn⟩ := supported_periodic_pair_energy hr s u hs hu
  let a := fun k : Fin d → ℤ ↦ (1 + frequencyNorm k ^ 2) ^ s *
    ‖UnitAddTorus.mFourierCoeff (toTorus (𝕜 := ℂ) u) k‖ ^ 2
  have hle (k : Fin d → ℤ) : a k ≤ 2 * pairEnergy s (toTorus (𝕜 := ℂ) u) k := by
    have hh := mul_le_mul_of_nonneg_left
      (coefficient_sq_le_pair (toTorus (𝕜 := ℂ) u) k)
      (show 0 ≤ (1 + frequencyNorm k ^ 2) ^ s by positivity)
    convert hh using 1
    dsimp [a, pairEnergy]
    ring
  have hsum : Summable a := (hp.mul_left 2).of_nonneg_of_le (fun k ↦ by dsimp [a]; positivity) hle
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' k, 2 * pairEnergy s (toTorus (𝕜 := ℂ) u) k :=
      hsum.tsum_le_tsum hle (hp.mul_left 2)
    _ = 2 * ∑' k, pairEnergy s (toTorus (𝕜 := ℂ) u) k := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by norm_num)

end JanetCartan.AmplitudeBound.RowCoefficients
