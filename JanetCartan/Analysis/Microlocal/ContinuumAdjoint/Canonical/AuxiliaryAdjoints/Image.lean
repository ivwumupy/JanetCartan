module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.WeightedEstimates

/-!
# Natural-order bounds for the literal image adjoint

The image component of `app:ch_background:prop:bg-adjoint` acts on every
periodic Sobolev datum at its original order. The finite expression retains
the source and measurement masks, reversed adjoint factors, all connection
coefficients, and the normalized torus measure. Its one-high bound follows
from primitive coefficient jets and the allocated multiplier estimate.

The consumer is the augmentation of
`Canonical.exists_finite_projected_common_densityAdjoints` in the concrete
`CarrierSobolev.augmentedInputSobolevScale`. The parent must instantiate the
jets on the SAME arrays supplied by
`ContinuumRow.ImageGeometry.exists_reference_imageChannel`.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace JanetCartan.ContinuumAdjoint.Canonical.AuxiliaryAdjoints

open PeriodicSobolevSpace ContinuumRow
open ContinuumCommutator.ImageChannel.Differential
open ImageFactorExpression

variable {n : ℕ}

private theorem primitive_action_bound {ι : Type*} (e : ImageFactorExpression n ι)
    (he : e.jetOrderLe 1) (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ι → C(Torus n, ℝ)) (hq : ∀ a, IsSmoothPeriodic (q a))
      (H : ℝ), 0 ≤ H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (q a)) x‖ ≤ M) →
      (∀ a j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (q a)) x‖ ≤ H) →
      ∀ u : PeriodicSobolevSpace n (Euclidean n) s,
        ‖e.onSobolev q hq s u‖ ≤ C * (‖u‖ + (1+H) * ‖toL2 s u‖) := by
  obtain ⟨K, hK, hprofile⟩ := exists_coefficient_jet_profile n s hM
  obtain ⟨C, hC, hbound⟩ := e.exists_weighted_action_bound he s
    (show 0 ≤ (s+1) * K by positivity)
  refine ⟨1+C, by positivity, ?_⟩
  intro q hq H hH hlow hhigh u
  let R := ‖u‖ + (1+H) * ‖toL2 s u‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcoeff : ∀ a js, js.length ≤ 1 → ∀ j ≤ s,
      cNorm (fundamentalCell n) j (periodicLift (orderedCoefficient (q a) (hq a) js)) ≤
        ((s+1) * K) * (1+H) ^ ((j : ℝ) / s) := by
    intro a js hjs j hj
    calc
      _ ≤ (j+1) * cNorm (fundamentalCell n) (j+js.length) (periodicLift (q a)) :=
        cNorm_periodicCoordinateDerivList_le (q a) (hq a) js j
      _ ≤ (s+1) * (K * (1+H) ^ ((j : ℝ) / s)) := by
        apply mul_le_mul
        · exact_mod_cast Nat.add_le_add_right hj 1
        · apply (hprofile (q a) (hq a) H hH (hlow a) (hhigh a) _ (by omega)).trans
          apply mul_le_mul_of_nonneg_left _ hK.le
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg s)
          exact_mod_cast (show j + js.length - 1 ≤ j by omega)
        · exact cNorm_nonneg _ _ _
        · positivity
      _ = _ := by ring
  have hu : ∀ r (hr : r ≤ s), ‖inclusion hr u‖ ≤
      (1+H) ^ ((r : ℝ) / s + (-1)) * R := by
    intro r hr
    have hi := periodic_gradeNorm_weighted_interpolate hr (by positivity : 0 ≤ 1+H) u
    rw [← multiplier_norm_inclusion_eq_gradeNorm hr] at hi
    have hp : (1+H) ^ ((r : ℝ) / s + (-1)) * (1+H) ^ (1 - (r : ℝ) / s) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      rw [show (r : ℝ) / s + (-1) + (1 - (r : ℝ) / s) = 0 by ring, Real.rpow_zero]
    calc
      _ = (1+H) ^ ((r : ℝ) / s + (-1)) *
          ((1+H) ^ (1 - (r : ℝ) / s) * ‖inclusion hr u‖) := by
        rw [← mul_assoc, hp, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)
  have hout := hbound q hq (1+H) (by linarith) hcoeff s le_rfl (-1) R hR u hu
  have hexp : (s : ℝ) / s + (-1) ≤ 0 := by
    by_cases hs : s = 0
    · simp [hs]
    · rw [div_self (by exact_mod_cast hs : (s : ℝ) ≠ 0)]
      norm_num
  have hp : (1+H) ^ ((s : ℝ) / s + (-1)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1+H by linarith) hexp
  apply hout.trans
  calc
    _ ≤ C * (1 * R) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hR) hC
    _ ≤ (1+C) * R := by nlinarith

/-- The actual image adjoint on `H^s`, at the natural order, constructed from
its reversed factors (`app:ch_background:prop:bg-adjoint`). -/
def imageAdjointSobolev
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc : C(Torus n, ℝ))
    (hχmeas : IsSmoothPeriodic χmeas) (hχsrc : IsSmoothPeriodic χsrc) (s : ℕ) :
    PeriodicSobolevSpace n (Euclidean n) s →L[ℝ]
      PeriodicSobolevSpace n (Euclidean n) s :=
  (imageAdjointExpression n).onSobolev (imageFactorCoefficients c χmeas χsrc)
    (smooth_imageFactorCoefficients c hc χmeas χsrc hχmeas hχsrc) s

/-- The constructed action is the literal Hilbert adjoint of the same image
channel, including both masks (`app:ch_background:prop:bg-adjoint`). -/
@[simp] theorem toL2_imageAdjointSobolev
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc : C(Torus n, ℝ))
    (hχmeas : IsSmoothPeriodic χmeas) (hχsrc : IsSmoothPeriodic χsrc)
    (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    toL2 s (imageAdjointSobolev c hc χmeas χsrc hχmeas hχsrc s u) =
      (imageChannel c χmeas χsrc).adjoint (toL2 s u) := by
  rw [imageAdjointSobolev, toL2_onSobolev,
    onL2_imageAdjointExpression c hc χmeas χsrc hχmeas hχsrc]

/-- All-data natural-order regularity of the literal image adjoint, including
`s = 0` (`app:ch_background:prop:bg-adjoint`). -/
theorem imageAdjoint_mem
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ a, IsSmoothPeriodic (c a)) (χmeas χsrc : C(Torus n, ℝ))
    (hχmeas : IsSmoothPeriodic χmeas) (hχsrc : IsSmoothPeriodic χsrc)
    (s : ℕ) {v : OutputL2 n} (hv : v ∈ periodicSobolevLevel n (Euclidean n) s) :
    (imageChannel c χmeas χsrc).adjoint v ∈ periodicSobolevLevel n (Euclidean n) s := by
  have h := toL2_mem s (imageAdjointSobolev c hc χmeas χsrc hχmeas hχsrc s (ofL2 s v hv))
  simpa only [toL2_imageAdjointSobolev, toL2_ofL2] using h

private theorem global_jet_le_cNorm {n : ℕ} (q : C(Torus n, ℝ))
    (hq : IsSmoothPeriodic q) {j m : ℕ} (hjm : j ≤ m) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ j (periodicLift q) x‖ ≤
      cNorm (fundamentalCell n) m (periodicLift q) := by
  apply norm_iteratedFDeriv_periodicLift_le q j _ x
  intro y hy
  exact norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
    (hq.2.of_le (by simp)) hy hjm

/-- The fixed masks precede the tame constant. The literal image adjoint has
a single high coefficient budget (`app:ch_background:prop:bg-adjoint`). The low coefficient order is one,
the high coefficient order is `s+1`, and neither depends on accuracy. -/
theorem exists_imageAdjoint_bound {n : ℕ}
    (χmeas χsrc : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (hχsrc : IsSmoothPeriodic χsrc) (s : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℝ), 0 ≤ H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ M) →
      (∀ a j, j ≤ s+1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ H) →
      ∀ u : PeriodicSobolevSpace n (Euclidean n) s,
      ‖imageAdjointSobolev c hc χmeas χsrc hχmeas hχsrc s u‖ ≤
        C * (‖u‖ + (1+H) * ‖toL2 s u‖) := by
  let L := cNorm (fundamentalCell n) 1 (periodicLift χmeas) +
    cNorm (fundamentalCell n) 1 (periodicLift χsrc)
  let Q := cNorm (fundamentalCell n) (s+1) (periodicLift χmeas) +
    cNorm (fundamentalCell n) (s+1) (periodicLift χsrc)
  have hL : 0 ≤ L := add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)
  have hQ : 0 ≤ Q := add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)
  let e := imageAdjointExpression n
  have he : e.jetOrderLe 1 := by simp [e, imageAdjointExpression, jetOrderLe]
  obtain ⟨C, hC, hbound⟩ := primitive_action_bound e he s (add_nonneg hM hL)
  refine ⟨C * (1+Q), by positivity, ?_⟩
  intro c hc H hH hlow hhigh u
  have hlow' : ∀ a j, j ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ M+L := by
    intro a j hj x
    rcases a with a | b
    · exact (hlow a j hj x).trans (le_add_of_nonneg_right hL)
    · cases b
      · apply (global_jet_le_cNorm χmeas hχmeas hj x).trans
        dsimp [L]
        linarith [cNorm_nonneg (fundamentalCell n) 1 (periodicLift χsrc)]
      · apply (global_jet_le_cNorm χsrc hχsrc hj x).trans
        dsimp [L]
        linarith [cNorm_nonneg (fundamentalCell n) 1 (periodicLift χmeas)]
  have hhigh' : ∀ a j, j ≤ s+1 → ∀ x,
      ‖iteratedFDeriv ℝ j (periodicLift (imageFactorCoefficients c χmeas χsrc a)) x‖ ≤ H+Q := by
    intro a j hj x
    rcases a with a | b
    · exact (hhigh a j hj x).trans (le_add_of_nonneg_right hQ)
    · cases b
      · apply (global_jet_le_cNorm χmeas hχmeas hj x).trans
        dsimp [Q]
        linarith [cNorm_nonneg (fundamentalCell n) (s+1) (periodicLift χsrc)]
      · apply (global_jet_le_cNorm χsrc hχsrc hj x).trans
        dsimp [Q]
        linarith [cNorm_nonneg (fundamentalCell n) (s+1) (periodicLift χmeas)]
  have hout := hbound (imageFactorCoefficients c χmeas χsrc)
    (smooth_imageFactorCoefficients c hc χmeas χsrc hχmeas hχsrc)
    (H+Q) (add_nonneg hH hQ) hlow' hhigh' u
  change ‖imageAdjointSobolev c hc χmeas χsrc hχmeas hχsrc s u‖ ≤ _ at hout
  apply hout.trans
  have hscale : ‖u‖ + (1+(H+Q)) * ‖toL2 s u‖ ≤
      (1+Q) * (‖u‖ + (1+H) * ‖toL2 s u‖) := by
    nlinarith [mul_nonneg hQ (norm_nonneg u),
      mul_nonneg (mul_nonneg hQ hH) (norm_nonneg (toL2 s u))]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hC.le


/-- `app:ch_background:prop:bg-adjoint` with the fixed reserve of the actual
geometric coefficient producer. `ImageGeometry.exists_reference_imageChannel`
and `HistoryImage.exists_imageChannel` supply the primitive jets
`P m * (1 + H (m+2))` for their SAME coefficients. The fixed low coefficient
order is one and the fixed map shift is two: the high map norm is `H (s+3)`.
The parent must instantiate these primitive budgets on that same row;
no Sobolev action or operator estimate is an input here. A fixed map budget
through order three suffices for the low coefficient jets through order one.
The constants precede every varying coefficient and profile. -/
theorem exists_imageAdjoint_profile {n : ℕ}
    (χmeas χsrc : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (hχsrc : IsSmoothPeriodic χsrc) {M : ℝ} (hM : 0 ≤ M)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℕ → ℝ),
      (∀ m, 0 ≤ H m) → Monotone H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ M) →
      (∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + H (j+2))) →
      ∀ (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s),
      ‖imageAdjointSobolev c hc χmeas χsrc hχmeas hχsrc s u‖ ≤
        C s * (‖u‖ + (1+H (s+3)) * ‖toL2 s u‖) := by
  have hb (s : ℕ) := exists_imageAdjoint_bound χmeas χsrc hχmeas hχsrc s hM
  choose C hC hbound using hb
  let Q (s : ℕ) := ∑ j ∈ Finset.range (s+2), P j
  have hQ (s : ℕ) : 0 ≤ Q s := Finset.sum_nonneg fun j _ ↦ hP j
  refine ⟨fun s ↦ C s * (1+Q s), fun s ↦ mul_pos (hC s) (add_pos_of_pos_of_nonneg zero_lt_one (hQ s)), ?_⟩
  intro c hc H hH hmono hlow hhigh s u
  have hQs := hQ s
  have hHs := hH (s+3)
  have hjets : ∀ a j, j ≤ s+1 → ∀ x,
      ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ Q s * (1+H (s+3)) := by
    intro a j hj x
    apply (hhigh a j x).trans
    apply mul_le_mul
    · exact Finset.single_le_sum (fun k _ ↦ hP k) (Finset.mem_range.mpr (by omega))
    · exact add_le_add (le_refl 1) (hmono (show j+2 ≤ s+3 by omega))
    · exact add_nonneg zero_le_one (hH (j+2))
    · exact hQ s
  have hout := hbound s c hc (Q s * (1+H (s+3))) (by positivity) hlow hjets u
  apply hout.trans
  have hscale : ‖u‖ + (1 + Q s * (1+H (s+3))) * ‖toL2 s u‖ ≤
      (1+Q s) * (‖u‖ + (1+H (s+3)) * ‖toL2 s u‖) := by
    nlinarith [mul_nonneg (hQ s) (norm_nonneg u),
      mul_nonneg (hH (s+3)) (norm_nonneg (toL2 s u))]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale (hC s).le


end JanetCartan.ContinuumAdjoint.Canonical.AuxiliaryAdjoints
