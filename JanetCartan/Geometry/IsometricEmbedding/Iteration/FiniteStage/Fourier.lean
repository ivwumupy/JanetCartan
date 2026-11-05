module

public import JanetCartan.Analysis.Fourier.Periodic.BernsteinL2
public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Sobolev
public import JanetCartan.Geometry.IsometricEmbedding.Scales

/-!
# The single Fourier-truncated stage increment

The real increment in `main:thm:step` is the fixed cutoff of the sum of the
primary and secondary fields. Its L², support, and Cʳ estimates below use the
component L² profiles, Parseval, and the sharp Bernstein theorem.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.FiniteStage

variable {n N : ℕ}

/-- The real final increment of `main:thm:step`, with the same fixed real-even
cutoff at every stage. Its support constant is exactly 2, independent of accuracy. -/
def increment (R : ℝ) (P W : Torus n → EuclideanSpace ℝ (Fin N)) :
    Torus n → EuclideanSpace ℝ (Fin N) :=
  periodicCutoff (R ^ bandExponent) (P + W)

private theorem l2_add_le {P W : Torus n → EuclideanSpace ℝ (Fin N)}
    (hP : Continuous P) (hW : Continuous W) {M : ℝ} (hM : 0 ≤ M)
    (hPM : periodicL2Norm P ≤ M) (hWM : periodicL2Norm W ≤ M) :
    periodicL2Norm (P + W) ≤ 2 * M := by
  have hPi : Integrable (fun x ↦ ‖P x‖ ^ 2) := (hP.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hWi : Integrable (fun x ↦ ‖W x‖ ^ 2) := (hW.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hsum : Integrable (fun x ↦ ‖(P + W) x‖ ^ 2) := ((hP.add hW).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hi : (∫ x, ‖(P + W) x‖ ^ 2) ≤
      2 * ((∫ x, ‖P x‖ ^ 2) + ∫ x, ‖W x‖ ^ 2) := by
    calc
      _ ≤ ∫ x, 2 * (‖P x‖ ^ 2 + ‖W x‖ ^ 2) := by
        apply integral_mono hsum ((hPi.add hWi).const_mul 2)
        intro x
        have h := norm_add_le (P x) (W x)
        have h' := sq_le_sq₀ (norm_nonneg (P x + W x))
          (add_nonneg (norm_nonneg (P x)) (norm_nonneg (W x)))
        dsimp only [Pi.add_apply]
        nlinarith [h'.2 h, sq_nonneg (‖P x‖ - ‖W x‖)]
      _ = _ := by rw [integral_const_mul, integral_add hPi hWi]
  have hPsq : (∫ x, ‖P x‖ ^ 2) ≤ M ^ 2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hM).2 hPM
    simpa only [periodicL2Norm, Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg ‖P x‖))]
      using h
  have hWsq : (∫ x, ‖W x‖ ^ 2) ≤ M ^ 2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hM).2 hWM
    simpa only [periodicL2Norm, Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg ‖W x‖))]
      using h
  exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

private theorem l2_cutoff_le {f : Torus n → EuclideanSpace ℝ (Fin N)}
    (hf : Continuous f) {L : ℝ} (hL : 0 < L) :
    periodicL2Norm (periodicCutoff L f) ≤ periodicL2Norm f := by
  have hz {g : Torus n → EuclideanSpace ℝ (Fin N)} (hg : Continuous g) :
      periodicSobolevNorm 0 g = periodicL2Norm g := by
    have h := hasSum_sq_periodicFourierCoeff_of_continuous hg
    simp only [periodicSobolevNorm, Real.rpow_zero, one_mul, h.tsum_eq,
      Real.sqrt_sq (show 0 ≤ periodicL2Norm g from Real.sqrt_nonneg _)]
  rw [← hz (isSmoothPeriodic_periodicCutoff L f).1, ← hz hf]
  apply periodicSobolevNorm_periodicCutoff_le hf hL
  simpa only [Real.rpow_zero, one_mul] using
    (hasSum_sq_periodicFourierCoeff_of_continuous hf).summable

/-- `main:eq:step-L2`: the actual final cutoff inherits the two component L²
profiles; δ² is absorbed by δ. The harmless factor 2 is independent of accuracy. -/
theorem increment_l2_le {P W : Torus n → EuclideanSpace ℝ (Fin N)}
    (hP : Continuous P) (hW : Continuous W) {C δ R : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hPL2 : periodicL2Norm P ≤ C * δ * R ^ displacementLoss n)
    (hWL2 : periodicL2Norm W ≤ C * δ ^ 2 * R ^ displacementLoss n) :
    periodicL2Norm (increment R P W) ≤ 2 * C * δ * R ^ displacementLoss n := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hW' : periodicL2Norm W ≤ C * δ * R ^ displacementLoss n := by
    apply hWL2.trans
    gcongr
    nlinarith
  exact (l2_cutoff_le (hP.add hW) (Real.rpow_pos_of_pos hR0 _)).trans
    ((l2_add_le hP hW (by positivity) hPL2 hW').trans_eq (by ring))

/-- `main:eq:step-band`: exact physical-frequency support of the same increment. -/
theorem increment_support {P W : Torus n → EuclideanSpace ℝ (Fin N)}
    (hP : Continuous P) (hW : Continuous W) {R : ℝ} (hR : 0 < R) :
    HasFourierSupport (2 * R ^ bandExponent) (increment R P W) :=
  hasFourierSupport_periodicCutoff (hP.add hW) (Real.rpow_pos_of_pos hR _)

/-- `main:eq:step-Cr`: the fixed Bernstein constant for the stage support radius. -/
def crConstant (n r : ℕ) (C : ℝ) : ℝ :=
  ((r + 1 : ℝ) * Real.sqrt (2 * 5 ^ n)) * 2 ^ ((r : ℝ) + (n : ℝ) / 2) * (2 * C)

/-- `main:eq:step-Cr`: all derivative orders hold for the very same real increment,
with the exact exponent B₀ + b_* (r + n/2). -/
theorem increment_cNorm_le {P W : Torus n → EuclideanSpace ℝ (Fin N)}
    (hP : Continuous P) (hW : Continuous W) {C δ R : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 1 ≤ R)
    (hPL2 : periodicL2Norm P ≤ C * δ * R ^ displacementLoss n)
    (hWL2 : periodicL2Norm W ≤ C * δ ^ 2 * R ^ displacementLoss n) (r : ℕ) :
    cNorm (fundamentalCell n) r (periodicLift (increment R P W)) ≤
      crConstant n r C * δ *
        R ^ (displacementLoss n + bandExponent * ((r : ℝ) + (n : ℝ) / 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hband : 1 ≤ R ^ bandExponent :=
    Real.one_le_rpow hR (by norm_num [bandExponent])
  calc
    _ ≤ ((r + 1 : ℝ) * Real.sqrt (2 * 5 ^ n)) *
        (2 * R ^ bandExponent) ^ ((r : ℝ) + (n : ℝ) / 2) *
        periodicL2Norm (increment R P W) :=
      cNorm_periodicLift_le_of_hasFourierSupport (isSmoothPeriodic_periodicCutoff _ _)
        (by linarith) (increment_support hP hW hR0) r
    _ ≤ ((r + 1 : ℝ) * Real.sqrt (2 * 5 ^ n)) *
        (2 * R ^ bandExponent) ^ ((r : ℝ) + (n : ℝ) / 2) *
        (2 * C * δ * R ^ displacementLoss n) := by
      exact mul_le_mul_of_nonneg_left (increment_l2_le hP hW hC hδ hδ1 hR hPL2 hWL2)
        (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
        ← Real.rpow_mul hR0.le, Real.rpow_add hR0]
      unfold crConstant
      ring

end JanetCartan.FiniteStage
