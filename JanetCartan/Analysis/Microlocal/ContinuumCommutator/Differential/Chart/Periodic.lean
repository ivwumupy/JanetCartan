module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.WeakTransfer

/-!
# Periodic smooth-test commutator

The actual ordered periodic weak identity in `app:ch_background:eq:bg-commutator`
is obtained from the proved compact-test theorem and normalized chart transfer.
The additive bound below still uses the Euclidean Hⁿ norm of the fixed extension.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => EuclideanL2 d ℂ

/-- The chart operator has an actual periodic weak commutator on every smooth
periodic input. All artificial cutoff terms are eliminated on physical support,
and the norm constant is independent of the high budget
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_torusL2Operator_smooth_commutator_bound
    (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) H)
        (χ : SourceCutoff d r) (u : Torus d → ℂ)
        (hu : IsSmoothPeriodic u) (hm : MemLp u 2),
        let du : PeriodicL2 d ℂ :=
          ((hu.coordinateDerivList is).1.memLp_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).toLp (periodicCoordinateDerivList is u)
        let T := torusL2Operator hd r b hb hs M
          (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        ∃ w : PeriodicL2 d ℂ,
          HasPeriodicWeakDerivativeList is (T (hm.toLp u)) (T du + w) ∧
          ‖w‖ ≤ C * (fourierSobolevNorm (n : ℝ) (χ.extendL2 hu) +
            max 1 H * ‖hm.toLp u‖) := by
  obtain ⟨C, hC, he⟩ := exists_chartLift_compact_commutator_bound hd r hr n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM is hlen hH χ u hu hm
  obtain ⟨w, hw, hn⟩ := he b hb hs H hM is hlen hH χ u hu hm
  dsimp only at hw hn ⊢
  let T := torusL2Operator hd r b hb hs M
    (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
  have hsupp (v : PeriodicL2 d ℂ) : ∀ᵐ x ∂volume,
      x ∉ chartBox r → toEuclidean (𝕜 := ℂ) (T v) x = 0 := by
    change ∀ᵐ x ∂volume, x ∉ chartBox r →
      toEuclidean (𝕜 := ℂ) (toTorus (𝕜 := ℂ)
        (twoPositionL2Operator hd r b hb hs M _ (toEuclidean (𝕜 := ℂ) v))) x = 0
    rw [toEuclidean_toTorus _ (by
      filter_upwards [twoPositionL2Operator_supported hd r b hb hs M
        (amplitudeDerivativeBound_of_le hM (Nat.le_succ _)) (toEuclidean (𝕜 := ℂ) v)]
        with x hx hc
      exact hx (fun h ↦ hc (chartBox_subset_cell hr h)))]
    exact twoPositionL2Operator_supported hd r b hb hs M _ _
  obtain ⟨W, hW, hN⟩ := exists_periodic_commutator_of_chart hr χ is _ _ w
    (hsupp _) (hsupp _) hw
  refine ⟨W, ?_, hN.trans hn⟩
  simpa only [toTorus_toEuclidean] using hW

end JanetCartan.Pseudodifferential.DifferentialChart
