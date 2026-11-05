module

public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.WeakDerivative.Basic

/-!
# Bounded coordinate derivatives on the periodic Sobolev scale

For `app:not:fourier` and `app:ch_background:prop:bg-inverse`, smooth Fourier
approximations construct a weak derivative in the preceding Sobolev level.
Completeness supplies the limit, and the closed distributional derivative graph
identifies it. No Fourier reconstruction or weak derivative existence is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan
namespace PeriodicSobolevSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem analysis_ofSmooth_sq (s : ℕ) (f : Torus n → F)
    (hf : IsSmoothPeriodic f) (k : Fin n → ℤ) :
    ‖analysis s (ofSmooth s f hf) k‖ ^ 2 =
      (1 + frequencyNorm k ^ 2) ^ s *
        (‖(periodicFourierCoeff f k).1‖ ^ 2 + ‖(periodicFourierCoeff f k).2‖ ^ 2) := by
  change ‖weightedPeriodicL2FourierCoeff s (toL2 s (ofSmooth s f hf)) k‖ ^ 2 = _
  rw [norm_weightedPeriodicL2FourierCoeff_sq,
    periodicFourierCoeff_congr_ae (toL2_ofSmooth_ae s f hf), Real.rpow_natCast]

/-- The smooth coordinate multiplier is a contraction from order `s + 1` to
order `s`, including the physical frequency factor `2π`
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
theorem norm_ofSmooth_coordinateDeriv_le (s : ℕ) (i : Fin n)
    (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    ‖ofSmooth s (periodicCoordinateDeriv i f) (hf.coordinateDeriv i)‖ ≤
      ‖ofSmooth (s + 1) f hf‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply hasSum_le _ (hasSum_sq_analysis s _) (hasSum_sq_analysis (s + 1) _)
  intro k
  rw [analysis_ofSmooth_sq, analysis_ofSmooth_sq,
    sq_periodicFourierCoeff_coordinateDeriv hf, pow_succ _ s, ← mul_assoc]
  have hfreq : (2 * Real.pi * (k i : ℝ)) ^ 2 ≤ frequencyNorm k ^ 2 := by
    rw [frequencyNorm_sq_eq_sum]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (2 * Real.pi * (k j : ℝ)))
      (Finset.mem_univ i)
  gcongr
  linarith

private theorem ofSmooth_sub_eq (s : ℕ) (f g : Torus n → F)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    ofSmooth s (f - g) ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩ =
      ofSmooth s f hf - ofSmooth s g hg := by
  apply toL2_injective s
  rw [map_sub]
  apply Lp.ext
  exact (toL2_ofSmooth_ae s _ _).trans
    (((toL2_ofSmooth_ae s f hf).sub (toL2_ofSmooth_ae s g hg)).symm.trans
      (Lp.coeFn_sub _ _).symm)

omit [FiniteDimensional ℝ F] in
private theorem coordinateDeriv_sub_eq (i : Fin n) (f g : Torus n → F)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    periodicCoordinateDeriv i (f - g) = periodicCoordinateDeriv i f -
      periodicCoordinateDeriv i g := by
  funext x
  simpa only [periodicCoordinateDeriv, Pi.sub_apply, Pi.sub_def, AddCircle.coe_zero,
    Pi.single_zero, add_zero] using ((hf.hasDerivAt_coordinate i x 0).sub
    (hg.hasDerivAt_coordinate i x 0)).deriv

private theorem dist_ofSmooth_coordinateDeriv_le (s : ℕ) (i : Fin n)
    (f g : Torus n → F) (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    dist (ofSmooth s (periodicCoordinateDeriv i f) (hf.coordinateDeriv i))
      (ofSmooth s (periodicCoordinateDeriv i g) (hg.coordinateDeriv i)) ≤
    dist (ofSmooth (s + 1) f hf) (ofSmooth (s + 1) g hg) := by
  have h := norm_ofSmooth_coordinateDeriv_le s i (f - g)
    ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
  simpa only [coordinateDeriv_sub_eq i f g hf hg, dist_eq_norm,
    ofSmooth_sub_eq (s + 1) f g hf hg,
    ofSmooth_sub_eq s _ _ (hf.coordinateDeriv i) (hg.coordinateDeriv i)] using h

/-- Smooth density and completeness construct a weak coordinate derivative with
the sharp Sobolev bound (`app:ch_background:prop:bg-inverse`). -/
theorem exists_weakDerivative_norm_le (s : ℕ) (i : Fin n)
    (u : PeriodicSobolevSpace n F (s + 1)) :
    ∃ v : PeriodicSobolevSpace n F s,
      HasPeriodicWeakDerivative i (toL2 (s + 1) u) (toL2 s v) ∧ ‖v‖ ≤ ‖u‖ := by
  let f (j : ℕ) := periodicCutoff (j + 1) (toL2 (s + 1) u)
  have hf (j : ℕ) : IsSmoothPeriodic (f j) := isSmoothPeriodic_periodicCutoff _ _
  let v (j : ℕ) := ofSmooth s (periodicCoordinateDeriv i (f j)) ((hf j).coordinateDeriv i)
  have hu := tendsto_smoothApproximation (s + 1) u
  have hc : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq ε hε
    refine ⟨N, fun j hj k hk ↦ lt_of_le_of_lt ?_ (hN j hj k hk)⟩
    exact dist_ofSmooth_coordinateDeriv_le s i (f j) (f k) (hf j) (hf k)
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨w, ?_, ?_⟩
  · exact HasPeriodicWeakDerivative.of_tendsto
      (fun j ↦ (hf j).hasPeriodicWeakDerivative i (s + 1) s)
      (((toL2 (s + 1)).continuous.tendsto u).comp hu)
      (((toL2 s).continuous.tendsto w).comp hw)
  · exact le_of_tendsto_of_tendsto' hw.norm hu.norm
      (fun j ↦ norm_ofSmooth_coordinateDeriv_le s i (f j) (hf j))

/-- The continuous real linear coordinate derivative from `H^(s+1)` to `H^s`,
constructed by completion of smooth derivatives
(`app:not:fourier`; `app:ch_background:prop:bg-inverse`). -/
def coordinateDerivative (s : ℕ) (i : Fin n) :
    PeriodicSobolevSpace n F (s + 1) →L[ℝ] PeriodicSobolevSpace n F s := by
  let D : PeriodicSobolevSpace n F (s + 1) →ₗ[ℝ] PeriodicSobolevSpace n F s :=
    { toFun := fun u ↦ (exists_weakDerivative_norm_le s i u).choose
      map_add' := fun u v ↦ by
        apply toL2_injective s
        rw [(toL2 s).map_add]
        apply (exists_weakDerivative_norm_le s i (u + v)).choose_spec.1.unique
        simpa only [(toL2 (s + 1)).map_add] using
          (exists_weakDerivative_norm_le s i u).choose_spec.1.add
            (exists_weakDerivative_norm_le s i v).choose_spec.1
      map_smul' := fun c u ↦ by
        apply toL2_injective s
        rw [(toL2 s).map_smul]
        apply (exists_weakDerivative_norm_le s i (c • u)).choose_spec.1.unique
        simpa only [(toL2 (s + 1)).map_smul, RingHom.id_apply] using
          (exists_weakDerivative_norm_le s i u).choose_spec.1.smul c }
  exact D.mkContinuous 1 (fun u ↦ by
    change ‖(exists_weakDerivative_norm_le s i u).choose‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using (exists_weakDerivative_norm_le s i u).choose_spec.2)

/-- The completed derivative is the actual distributional coordinate derivative
of its input (`app:ch_background:prop:bg-inverse`). -/
theorem hasPeriodicWeakDerivative_coordinateDerivative (s : ℕ) (i : Fin n)
    (u : PeriodicSobolevSpace n F (s + 1)) :
    HasPeriodicWeakDerivative i (toL2 (s + 1) u) (toL2 s (coordinateDerivative s i u)) :=
  (exists_weakDerivative_norm_le s i u).choose_spec.1

/-- The coordinate derivative loses one Sobolev order with constant one
(`app:ch_background:prop:bg-inverse`). -/
theorem norm_coordinateDerivative_le (s : ℕ) (i : Fin n)
    (u : PeriodicSobolevSpace n F (s + 1)) : ‖coordinateDerivative s i u‖ ≤ ‖u‖ :=
  (exists_weakDerivative_norm_le s i u).choose_spec.2

/-- Operator-norm version of the coordinate derivative estimate
(`app:ch_background:prop:bg-inverse`). -/
theorem opNorm_coordinateDerivative_le (s : ℕ) (i : Fin n) :
    ‖coordinateDerivative (F := F) s i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_coordinateDerivative_le s i u

/-- The completed coordinate derivative agrees with classical differentiation on
every smooth periodic field (`app:not:fourier`). -/
@[simp] theorem coordinateDerivative_ofSmooth (s : ℕ) (i : Fin n)
    (f : Torus n → F) (hf : IsSmoothPeriodic f) :
    coordinateDerivative s i (ofSmooth (s + 1) f hf) =
      ofSmooth s (periodicCoordinateDeriv i f) (hf.coordinateDeriv i) := by
  apply toL2_injective s
  exact (hasPeriodicWeakDerivative_coordinateDerivative s i _).unique
    (hf.hasPeriodicWeakDerivative i (s + 1) s)

end PeriodicSobolevSpace

/-- Forward Sobolev membership: every `H^(s+1)` L² class belongs to `H^s`
and has all coordinate weak derivatives in `H^s`
(`app:ch_background:prop:bg-inverse`). -/
theorem exists_periodicWeakDerivatives_of_mem_succ {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (s : ℕ) (u : PeriodicL2 n F) (hu : u ∈ periodicSobolevLevel n F (s + 1)) :
    u ∈ periodicSobolevLevel n F s ∧
      ∀ i : Fin n, ∃ v : PeriodicL2 n F,
        v ∈ periodicSobolevLevel n F s ∧ HasPeriodicWeakDerivative i u v := by
  refine ⟨antitone_periodicSobolevLevel (Nat.le_succ s) hu, ?_⟩
  intro i
  let v := PeriodicSobolevSpace.coordinateDerivative s i (PeriodicSobolevSpace.ofL2 _ u hu)
  exact ⟨PeriodicSobolevSpace.toL2 s v, PeriodicSobolevSpace.toL2_mem s v,
    PeriodicSobolevSpace.hasPeriodicWeakDerivative_coordinateDerivative s i
      (PeriodicSobolevSpace.ofL2 _ u hu)⟩

end JanetCartan
