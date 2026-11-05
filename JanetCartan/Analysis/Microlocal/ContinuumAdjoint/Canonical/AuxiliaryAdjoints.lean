module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AuxiliaryAdjoints.Image
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AuxiliaryAdjoints.Exterior
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Defs

/-!
# Uniform natural-order image and exterior adjoint bounds

These are the two auxiliary inputs to the augmentation of
`Canonical.exists_finite_projected_common_densityAdjoints` in
`CarrierSobolev.augmentedInputSobolevScale`, for
`app:ch_background:prop:bg-adjoint` and `app:ch_background:eq:bg-r-inverse`.
Both are literal adjoints on normalized torus measure. Constants precede
varying coefficient arrays, profiles, and arbitrary Sobolev data. The image
bound uses one high budget at `s+3`; the exterior bound uses its fixed smooth
multiplier. No Sobolev or operator estimate is an assumption.

The exact producer `ContinuumRow.ImageGeometry.exists_reference_imageChannel`
supplies smooth arrays with global m-th jets bounded by
`P m * (1 + cNorm (closedBall 0 R) (m+2) F)`. Its separate scalar bound `B`
controls only coefficient values. To obtain the low jets through order one,
use a fixed map budget through order three with the SAME derivative profile
and arrays. The producer's C8 neighborhood of the fixed smooth reference
implies such a budget by the triangle inequality and order monotonicity.
The parent retains actual geometric/history instantiation, carrier slots,
and final augmented-row assembly; these auxiliary deductions do not assert
the unconditional source proposition.
-/

public noncomputable section

open scoped ContDiff

namespace JanetCartan.ContinuumAdjoint.Canonical.AuxiliaryAdjoints

open PeriodicSobolevSpace ContinuumRow
open ContinuumCommutator.ImageChannel.Differential

variable {n : ℕ}

/-- The producer's reserve-two profile needs only a third-order map budget
for the fixed first coefficient jets (`app:ch_background:eq:bg-frame-tame`).
This applies to the original arrays, without selecting new coefficients. -/
theorem image_low_jets_of_third_order_budget
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (P H : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) (hH : ∀ m, 0 ≤ H m)
    (hmono : Monotone H) {L : ℝ} (hL : H 3 ≤ L)
    (hjets : ∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
      P j * (1 + H (j+2))) :
    ∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
      (P 0 + P 1) * (1+L) := by
  intro a j hj x
  apply (hjets a j x).trans
  apply mul_le_mul
  · have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl <;> linarith [hP 0, hP 1]
  · exact add_le_add le_rfl ((hmono (by omega : j+2 ≤ 3)).trans hL)
  · exact add_nonneg zero_le_one (hH _)
  · exact add_nonneg (hP 0) (hP 1)

/-- Uniform Sobolev lifts of both literal auxiliary adjoints, including order
zero, and their summed one-high bound (`app:ch_background:prop:bg-adjoint`).
The lifts fill the two periodic slots of `AugmentedInputSobolevSpace`; the
parent supplies the carrier slots from its common-density adjoint theorem. -/
theorem exists_auxiliaryAdjoints_profile
    (χmeas χsrc ψ : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (hχsrc : IsSmoothPeriodic χsrc) (hψ : IsSmoothPeriodic ψ)
    {M : ℝ} (hM : 0 ≤ M) (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℕ → ℝ),
      (∀ m, 0 ≤ H m) → Monotone H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ M) →
      (∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + H (j+2))) →
      ∀ (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s),
        ∃ v w : PeriodicSobolevSpace n (Euclidean n) s,
          toL2 s v = (imageChannel c χmeas χsrc).adjoint (toL2 s u) ∧
          toL2 s w = (exteriorChannel ψ).adjoint (toL2 s u) ∧
          ‖v‖ + ‖w‖ ≤ C s * (‖u‖ + (1+H (s+3)) * ‖toL2 s u‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_imageAdjoint_profile χmeas χsrc hχmeas hχsrc hM P hP
  obtain ⟨D, hD, hext⟩ := exists_exteriorAdjoint_bound ψ hψ
  refine ⟨fun s ↦ C s + D s, fun s ↦ add_pos (hC s) (hD s), ?_⟩
  intro c hc H hH hmono hlow hhigh s u
  refine ⟨imageAdjointSobolev c hc χmeas χsrc hχmeas hχsrc s u,
    exteriorAdjointSobolev ψ hψ s u, toL2_imageAdjointSobolev ..,
    toL2_exteriorAdjointSobolev .., ?_⟩
  calc
    _ ≤ C s * (‖u‖ + (1+H (s+3)) * ‖toL2 s u‖) + D s * ‖u‖ :=
      add_le_add (hbound c hc H hH hmono hlow hhigh s u) (hext s u)
    _ ≤ _ := by
      nlinarith [mul_nonneg (hD s).le
        (mul_nonneg (add_nonneg zero_le_one (hH (s+3))) (norm_nonneg (toL2 s u)))]

private theorem norm_eq_gradeNorm_toL2 (s : ℕ) (u : PeriodicSobolevSpace n (Euclidean n) s) :
    ‖u‖ = (periodicSobolevScale n (Euclidean n)).gradeNorm s (toL2 s u) := by
  have he : inclusion (Nat.le_refl s) u = u := by
    apply toL2_injective s
    exact multiplier_toL2_inclusion _ _
  simpa only [he] using multiplier_norm_inclusion_eq_gradeNorm (Nat.le_refl s) u

/-- All-data level membership and the one-high grade-norm estimate for both
literal auxiliary adjoints (`app:ch_background:eq:bg-r-inverse`). These are
the exact periodic components used by `CarrierSobolev.mem_augmentedInputLevel_iff`
and `CarrierSobolev.augmentedInputSobolevScale_gradeNorm_sq`. -/
theorem exists_auxiliaryAdjoints_gradeNorm_profile
    (χmeas χsrc ψ : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (hχsrc : IsSmoothPeriodic χsrc) (hψ : IsSmoothPeriodic ψ)
    {M : ℝ} (hM : 0 ≤ M) (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)) (H : ℕ → ℝ),
      (∀ m, 0 ≤ H m) → Monotone H →
      (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ M) →
      (∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
        P j * (1 + H (j+2))) →
      ∀ (s : ℕ) (u : OutputL2 n), u ∈ periodicSobolevLevel n (Euclidean n) s →
        (imageChannel c χmeas χsrc).adjoint u ∈ periodicSobolevLevel n (Euclidean n) s ∧
        (exteriorChannel ψ).adjoint u ∈ periodicSobolevLevel n (Euclidean n) s ∧
        (periodicSobolevScale n (Euclidean n)).gradeNorm s
            ((imageChannel c χmeas χsrc).adjoint u) +
          (periodicSobolevScale n (Euclidean n)).gradeNorm s ((exteriorChannel ψ).adjoint u) ≤
          C s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s u +
            (1+H (s+3)) * ‖u‖) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_auxiliaryAdjoints_profile χmeas χsrc ψ hχmeas hχsrc hψ hM P hP
  refine ⟨C, hC, ?_⟩
  intro c hc H hH hmono hlow hhigh s u hu
  obtain ⟨v, w, hv, hw, hb⟩ := hbound c hc H hH hmono hlow hhigh s (ofL2 s u hu)
  simp only [toL2_ofL2] at hv hw
  refine ⟨hv ▸ toL2_mem s v, hw ▸ toL2_mem s w, ?_⟩
  simpa only [norm_eq_gradeNorm_toL2, toL2_ofL2, hv, hw] using hb

/-- The exact derivative signature of
`ContinuumRow.ImageGeometry.exists_reference_imageChannel`, together with
its C8 reference neighborhood, supplies the fixed low coefficient budget.
Only map order three enters that budget; the producer's separate value bound
is not mistaken for a first-jet bound (`app:ch_background:eq:bg-frame-tame`). -/
theorem image_low_jets_of_reference_closeness (G : FlatReference n) (R : ℝ)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) {δ : ℝ}
    (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiff ℝ ∞ F)
    (hclose : cNorm (Metric.closedBall 0 R) 8 (F - G.map) < δ)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hjets : ∀ m a x, ‖iteratedFDeriv ℝ m (periodicLift (c a)) x‖ ≤
      P m * (1 + cNorm (Metric.closedBall 0 R) (m+2) F)) :
    ∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤
      (P 0 + P 1) * (1 + (cNorm (Metric.closedBall 0 R) 3 G.map + δ)) := by
  have hthree : cNorm (Metric.closedBall 0 R) 3 F ≤
      cNorm (Metric.closedBall 0 R) 3 G.map + δ := by
    have hadd := cNorm_add_le (isCompact_closedBall (0 : Euclidean n) R)
      ((hF.sub G.contDiff).of_le (by simp : (3 : WithTop ℕ∞) ≤ ∞))
      (G.contDiff.of_le (by simp : (3 : WithTop ℕ∞) ≤ ∞))
    change cNorm (Metric.closedBall 0 R) 3 ((F - G.map) + G.map) ≤
      cNorm (Metric.closedBall 0 R) 3 (F - G.map) +
        cNorm (Metric.closedBall 0 R) 3 G.map at hadd
    rw [sub_add_cancel] at hadd
    have horder := cNorm_mono_order (f := F - G.map)
      (s := Metric.closedBall 0 R) (by norm_num : 3 ≤ 8)
    linarith
  exact image_low_jets_of_third_order_budget c P
    (fun m ↦ cNorm (Metric.closedBall 0 R) m F) hP (fun _ ↦ cNorm_nonneg ..)
    (fun _ _ h ↦ cNorm_mono_order h) hthree (fun a m x ↦ hjets m a x)

/-- Direct specialization to the SAME arrays returned by
`ContinuumRow.ImageGeometry.exists_reference_imageChannel`. All constants
precede `F`, `c` and the datum, and the only varying hypotheses are exactly
smoothness, the producer's C8 closeness, and its primitive derivative profile.
The low jets are discharged from these inputs. This supplies both periodic
slots for `app:ch_background:eq:bg-r-inverse`; the parent still instantiates
the producer and assembles the carrier slots of the actual augmented row. -/
theorem exists_auxiliaryAdjoints_reference_profile
    (G : FlatReference n) (R : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (χmeas χsrc ψ : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (hχsrc : IsSmoothPeriodic χsrc) (hψ : IsSmoothPeriodic ψ)
    (P : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ F : Euclidean n → Euclidean (embeddingDimension n), ContDiff ℝ ∞ F →
      cNorm (Metric.closedBall 0 R) 8 (F - G.map) < δ →
      ∀ (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
        (_hc : ∀ a, IsSmoothPeriodic (c a)),
      (∀ m a x, ‖iteratedFDeriv ℝ m (periodicLift (c a)) x‖ ≤
        P m * (1 + cNorm (Metric.closedBall 0 R) (m+2) F)) →
      ∀ (s : ℕ) (u : OutputL2 n), u ∈ periodicSobolevLevel n (Euclidean n) s →
        (imageChannel c χmeas χsrc).adjoint u ∈ periodicSobolevLevel n (Euclidean n) s ∧
        (exteriorChannel ψ).adjoint u ∈ periodicSobolevLevel n (Euclidean n) s ∧
        (periodicSobolevScale n (Euclidean n)).gradeNorm s
            ((imageChannel c χmeas χsrc).adjoint u) +
          (periodicSobolevScale n (Euclidean n)).gradeNorm s ((exteriorChannel ψ).adjoint u) ≤
          C s * ((periodicSobolevScale n (Euclidean n)).gradeNorm s u +
            (1 + cNorm (Metric.closedBall 0 R) (s+3) F) * ‖u‖) := by
  let M := (P 0 + P 1) * (1 + (cNorm (Metric.closedBall 0 R) 3 G.map + δ))
  have hM : 0 ≤ M := mul_nonneg (add_nonneg (hP 0) (hP 1))
    (add_nonneg zero_le_one (add_nonneg (cNorm_nonneg ..) hδ))
  obtain ⟨C, hC, hbound⟩ :=
    exists_auxiliaryAdjoints_gradeNorm_profile χmeas χsrc ψ hχmeas hχsrc hψ hM P hP
  refine ⟨C, hC, ?_⟩
  intro F hF hclose c hc hjets s u hu
  exact hbound c hc (fun m ↦ cNorm (Metric.closedBall 0 R) m F)
    (fun _ ↦ cNorm_nonneg ..) (fun _ _ h ↦ cNorm_mono_order h)
    (image_low_jets_of_reference_closeness G R P hP F hF hclose c hjets)
    (fun a m x ↦ hjets m a x) s u hu

end JanetCartan.ContinuumAdjoint.Canonical.AuxiliaryAdjoints
