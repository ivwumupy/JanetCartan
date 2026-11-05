module

public import JanetCartan.Iteration.PhysicalMean.MomentSource

/-!
# Fixed source-coordinate constants for the original adjoint moment

These constants are chosen from the fixed physical cutoff, source order and
fixed output dimension BEFORE the current map, scalar tester, sample set,
band count, source or inverse. They turn the exact coordinate sum from the
native matrix adjoint into the periodic Sobolev norms of the SAME source
(`app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace JanetCartan.PhysicalMean

open CurrentMean PeriodicLocalL2 Pseudodifferential AmplitudeBound.PaperEstimates

variable {n : ℕ} (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
  (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ halfOpenCell n)

/-- Fixed scalar-coordinate source constant; independent of source and sample. -/
def sourceCoordinateConstant (s : ℕ) : ℝ :=
  (exists_cutSmoothResidual_coordinateSobolev_bound χ hχ hc hs s).choose

theorem sourceCoordinateConstant_nonneg (s : ℕ) :
    0 ≤ sourceCoordinateConstant χ hχ hc hs s :=
  (exists_cutSmoothResidual_coordinateSobolev_bound χ hχ hc hs s).choose_spec.1

/-- Same-order control for the literal scalar Schwartz source coordinates. -/
theorem sourceCoordinateConstant_bound (s : ℕ) (r : SmoothResidual n) (i : Fin n) :
    fourierSobolevNorm s ((cutSmoothResidualCoordinate χ hχ hc r i).toLp 2 volume) ≤
      sourceCoordinateConstant χ hχ hc hs s * periodicSobolevNorm s (fun x ↦ r.val x ()) :=
  (exists_cutSmoothResidual_coordinateSobolev_bound χ hχ hc hs s).choose_spec.2 r i

/-- The finite rank and finite derivative sum are independent of sample count,
band count, cutoff frequency and source. -/
def sourceMomentConstant (q : ℕ) : ℝ :=
  n * ∑ k ∈ Finset.range (q + 1), sourceCoordinateConstant χ hχ hc hs k

theorem sourceMomentConstant_nonneg (q : ℕ) :
    0 ≤ sourceMomentConstant χ hχ hc hs q :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun k _ ↦
    sourceCoordinateConstant_nonneg χ hχ hc hs k))

/-- The actual coordinate Sobolev sum costs only the fixed source constant.
All powers retain their positive parts and the same physical source order. -/
theorem cutSmoothResidualCoordinate_moment_sum_le
    (q r₀ : ℕ) {T : ℝ} (hT : 0 ≤ T) (r : SmoothResidual n) :
    (∑ i : Fin n, ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) *
      fourierSobolevNorm k ((cutSmoothResidualCoordinate χ hχ hc r i).toLp 2 volume)) ≤
      sourceMomentConstant χ hχ hc hs q *
        ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) *
          periodicSobolevNorm k (fun x ↦ r.val x ()) := by
  let C := ∑ k ∈ Finset.range (q + 1), sourceCoordinateConstant χ hχ hc hs k
  have hC (k : ℕ) (hk : k ∈ Finset.range (q + 1)) :
      sourceCoordinateConstant χ hχ hc hs k ≤ C :=
    Finset.single_le_sum (fun j _ ↦ sourceCoordinateConstant_nonneg χ hχ hc hs j) hk
  have hi (i : Fin n) :
      (∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) *
        fourierSobolevNorm k ((cutSmoothResidualCoordinate χ hχ hc r i).toLp 2 volume)) ≤
        C * ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) *
          periodicSobolevNorm k (fun x ↦ r.val x ()) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hh := (sourceCoordinateConstant_bound χ hχ hc hs k r i).trans
      (mul_le_mul_of_nonneg_right (hC k hk) (Real.sqrt_nonneg _))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hh (pow_nonneg hT (q - k - r₀))
  calc
    _ ≤ ∑ i : Fin n, C * ∑ k ∈ Finset.range (q + 1), T ^ (q - k - r₀) *
        periodicSobolevNorm k (fun x ↦ r.val x ()) := Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (n : ℝ) * (C * _) = (n : ℝ) * C * _
      ring

omit χ hχ hc hs in
/-- Positivity of the already constructed fixed radial IBP constant. -/
theorem sampledRadialMomentConstant_nonneg (n : ℕ) (R : ℝ) (B : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k) (q : ℕ) :
    0 ≤ sampledRadialMomentConstant n R B q := by
  unfold sampledRadialMomentConstant
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  unfold sampledMomentConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (finiteRowAmplitudeConstant_nonneg n R)) (momentAmplitudeTestConstant_nonneg B hB _ _))
      (pow_nonneg (by positivity) _)

end JanetCartan.PhysicalMean
