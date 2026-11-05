module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.PaperEstimates.FiniteLegacy.Periodization
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.SourceEstimates
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Iterated

/-!
# Actual coefficient energy from the finite physical derivative budget

Part (ii) of `app:ch_osc:lem:osc-amplitude` uses the original `C^(2ell)`
amplitude in the combined physical positions.  The estimate here works at any
natural order `N` and uses exactly that finite regularity.  Finite integration
by parts and Parseval prove energy summability; no higher regularity or separate
Sobolev-membership premise is imposed on the amplitude.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.AmplitudeBound.PaperEstimates.TwoPositionCoefficients

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem hasSum_sq_coeff_of_continuous {f : Torus n → ℂ} (hf : Continuous f) :
    HasSum (fun k ↦ ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) (∫ x, ‖f x‖ ^ 2) := by
  let μ := Measure.pi (fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
  have hμ : MemLp f 2 μ := by
    change MemLp f 2 (Measure.pi
      (fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle)))
    rw [← torus_volume_eq_pi_haarAddCircle]
    exact hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (hμ.toLp f)
  rw [torus_volume_eq_pi_haarAddCircle]
  convert h using 1
  · funext k
    congr 2
    unfold UnitAddTorus.mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hμ.coeFn_toLp] with x hx
    exact congrArg (fun z : ℂ ↦ UnitAddTorus.mFourier (-k) x • z) hx.symm
  · apply integral_congr_ae
    filter_upwards [hμ.coeFn_toLp] with x hx
    exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx.symm

private theorem coefficient_coordinate_sq {f : Torus n → ℂ}
    (hf : ContDiff ℝ 1 (periodicLift f)) (i : Fin n) (k : Fin n → ℤ) :
    ‖UnitAddTorus.mFourierCoeff (periodicCoordinateDeriv i f) k‖ ^ 2 =
      (2 * Real.pi * (k i : ℝ)) ^ 2 * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by
  have h := congrArg (fun z : ℂ ↦ ‖z‖ ^ 2)
    (FiniteLegacy.mFourierCoeff_coordinateDerivList_of_finite [i] (by simpa using hf) k)
  simpa [periodicCoordinateDerivList, norm_mul, mul_pow, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast, Int.cast_abs,
    sq_abs] using h

private theorem periodic_finite_energy (N : ℕ) (f : Torus n → ℂ)
    (hf : ContDiff ℝ N (periodicLift f)) (B : ℝ)
    (hjet : ∀ is : List (Fin n), is.length ≤ N → ∀ x,
      ‖periodicCoordinateDerivList is f x‖ ≤ B) :
    ∃ b : ℝ,
      HasSum (fun k ↦ (1 + frequencyNorm k ^ 2) ^ N *
        ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) b ∧
      b ≤ (n + 1 : ℝ) ^ N * B ^ 2 := by
  classical
  induction N generalizing f with
  | zero =>
    have hc : Continuous f := by
      simpa only [periodicCoordinateDerivList] using
        FiniteLegacy.continuous_periodicCoordinateDerivList [] hf
    refine ⟨∫ x, ‖f x‖ ^ 2, ?_, ?_⟩
    · simpa only [pow_zero, one_mul] using hasSum_sq_coeff_of_continuous hc
    · simpa only [pow_zero, one_mul] using
        (calc
          (∫ x, ‖f x‖ ^ 2) ≤ ∫ _x : Torus n, B ^ 2 := by
            apply integral_mono
              ((hc.norm.pow 2).integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)) (integrable_const (B ^ 2))
            intro x
            exact pow_le_pow_left₀ (norm_nonneg _) (hjet [] (by simp) x) 2
          _ = B ^ 2 := by rw [torus_volume_eq_pi_haarAddCircle]; simp)
  | succ N ih =>
    have hfN : ContDiff ℝ N (periodicLift f) := hf.of_le (by norm_cast; omega)
    obtain ⟨b, hb, hnb⟩ := ih f hfN (fun is his ↦ hjet is (his.trans (Nat.le_succ N)))
    have hD (i : Fin n) : ContDiff ℝ N (periodicLift (periodicCoordinateDeriv i f)) :=
      FiniteLegacy.contDiff_periodicLift_coordinateDeriv hf i
    have hDJ (i : Fin n) (is : List (Fin n)) (his : is.length ≤ N) (x : Torus n) :
        ‖periodicCoordinateDerivList is (periodicCoordinateDeriv i f) x‖ ≤ B := by
      have hh := hjet (is ++ [i]) (by simpa using Nat.succ_le_succ his) x
      simpa only [periodicCoordinateDerivList_append, periodicCoordinateDerivList] using hh
    choose c hc hnc using fun i : Fin n ↦ ih (periodicCoordinateDeriv i f) (hD i) (hDJ i)
    have hcoeff (i : Fin n) (k : Fin n → ℤ) :=
      coefficient_coordinate_sq (hf.of_le (by norm_cast; omega)) i k
    refine ⟨b + ∑ i, c i, ?_, ?_⟩
    · apply (hb.add (hasSum_sum (s := Finset.univ) (fun i _ ↦ hc i))).congr_fun
      intro k
      simp only [hcoeff]
      rw [pow_succ, ← Finset.mul_sum, ← Finset.sum_mul, ← frequencyNorm_sq_eq_sum]
      ring
    · calc
        b + ∑ i, c i ≤ (n + 1 : ℝ) ^ N * B ^ 2 +
            ∑ _i : Fin n, (n + 1 : ℝ) ^ N * B ^ 2 :=
          add_le_add hnb (Finset.sum_le_sum (fun i _ ↦ hnc i))
        _ = (n + 1 : ℝ) ^ (N + 1) * B ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [pow_succ]
          ring

/-- The fixed constant for actual periodic energy of a `C^N` physical amplitude,
for part (ii) of `app:ch_osc:lem:osc-amplitude`. -/
def finiteRowCoefficientEnergyConstant (n N : ℕ) (R : ℝ) : ℝ :=
  (n + 1 : ℝ) ^ N * ((amplitudeBoxScale R) ^ N) ^ 2

/-- The constant is positive even at order or dimension zero, and is selected
solely from the original box and order (`app:ch_osc:lem:osc-amplitude`). -/
theorem finiteRowCoefficientEnergyConstant_pos (n N : ℕ) (R : ℝ) :
    0 < finiteRowCoefficientEnergyConstant n N R := by
  have := amplitudeBoxScale_pos R
  unfold finiteRowCoefficientEnergyConstant
  positivity

/-- The literal coefficients of the original box periodization have summable
weighted energy from the stated finite derivative budget.  The consumer takes
`n = 2*d` and `N = 2*(d/2+1)` in part (ii) of
`app:ch_osc:lem:osc-amplitude`. -/
theorem finite_row_coefficient_energy (N : ℕ) (R : ℝ) (f : E → ℂ)
    (hf : ContDiff ℝ N f) (hs : SupportedInCenteredBox R f)
    (A : ℝ) (hA : 0 ≤ A)
    (hjet : ∀ is : List (Fin n), is.length ≤ N → ∀ x,
      ‖euclideanCoordinateDerivList is f x‖ ≤ A) :
    Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ N *
      ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f) k‖ ^ 2) ∧
    (∑' k, (1 + frequencyNorm k ^ 2) ^ N *
      ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f) k‖ ^ 2) ≤
      finiteRowCoefficientEnergyConstant n N R * A ^ 2 := by
  let L := amplitudeBoxScale R
  have hL0 : 0 < L := amplitudeBoxScale_pos R
  have hL : 1 ≤ L := by dsimp [L, amplitudeBoxScale]; linarith [abs_nonneg R]
  have hF := (FiniteLegacy.box_periodization_contDiff hL0
    (div_amplitudeBoxScale_lt R) hs hf).2
  have hFJ (is : List (Fin n)) (his : is.length ≤ N) (x : Torus n) :
      ‖periodicCoordinateDerivList is (boxAmplitudePeriodization L f) x‖ ≤ L ^ N * A := by
    have hh := FiniteLegacy.norm_coordinateDerivList_box_of_finite hL0
      (div_amplitudeBoxScale_lt R) hs is (hf.of_le (by exact_mod_cast his)) (hjet is his) x
    rw [abs_of_pos hL0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL his) hA)
  obtain ⟨b, hb, hnb⟩ := periodic_finite_energy N (boxAmplitudePeriodization L f)
    hF (L ^ N * A) hFJ
  refine ⟨hb.summable, hb.tsum_eq.trans_le (hnb.trans_eq ?_)⟩
  dsimp [finiteRowCoefficientEnergyConstant, L]
  ring

/-- Uniform quantifier order for the sharp combined-position source: the
constant precedes both the original amplitude and its finite derivative bound
(`app:ch_osc:lem:osc-amplitude`, part (ii)). -/
theorem exists_finite_row_coefficient_energy_constant (n N : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℂ,
      ContDiff ℝ N f → SupportedInCenteredBox R f → ∀ A : ℝ, 0 ≤ A →
      (∀ is : List (Fin n), is.length ≤ N → ∀ x,
        ‖euclideanCoordinateDerivList is f x‖ ≤ A) →
      Summable (fun k ↦ (1 + frequencyNorm k ^ 2) ^ N *
        ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f) k‖ ^ 2) ∧
      (∑' k, (1 + frequencyNorm k ^ 2) ^ N *
        ‖UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization (amplitudeBoxScale R) f) k‖ ^ 2) ≤
        C * A ^ 2 :=
  ⟨finiteRowCoefficientEnergyConstant n N R, finiteRowCoefficientEnergyConstant_pos n N R,
    finite_row_coefficient_energy N R⟩

end JanetCartan.AmplitudeBound.PaperEstimates.TwoPositionCoefficients
