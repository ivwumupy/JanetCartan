module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Realization
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Compact

/-!
# The compact-test commutator in the physical chart

For `app:ch_background:eq:bg-commutator`, apply the proved Euclidean commutator
to the actual compact extension of a periodic test. Source locality removes
all artificial extension derivatives from the second operator term. The
identity below is for the Euclidean distribution of the chart lift.
`Chart.WeakTransfer` converts it to the periodic weak identity, and
`Chart.Sobolev` compares the extension Hⁿ norm with the periodic Hⁿ norm.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => EuclideanL2 d ℂ

/-- The derivative of the compact source extension and the compact extension
of the periodic derivative have exactly the same operator image. Only the
artificial extension is removed; the full amplitude is untouched
(`app:ch_background:eq:bg-commutator`). -/
theorem twoPositionL2Operator_derivative_extension
    (hd : 0 < d) (r : ℝ)
    (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
    (χ : SourceCutoff d r) {u : Torus d → ℂ} (hu : IsSmoothPeriodic u)
    (is : List (Fin d)) :
    let df : L² :=
      ((contDiff_euclideanCoordinateDerivList (χ.smooth_extend hu) is).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordinateDerivList (χ.compact_extend u) is)).toLp
          (euclideanCoordinateDerivList is (χ.extend u))
    twoPositionL2Operator hd r b hb hs A hA df =
      twoPositionL2Operator hd r b hb hs A hA (χ.extendL2 (hu.coordinateDerivList is)) := by
  apply twoPositionL2Operator_congr_on_source
  filter_upwards [
    ((contDiff_euclideanCoordinateDerivList (χ.smooth_extend hu) is).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordinateDerivList (χ.compact_extend u) is)).coeFn_toLp,
    χ.extendL2_coe (hu.coordinateDerivList is)] with x hx hx' hbox
  rw [hx, hx', χ.derivative_extend_eq hu is hbox]
  exact (χ.extend_eventuallyEq (periodicCoordinateDerivList is u) hbox).self_of_nhds.symm

/-- The actual unit-torus operator satisfies the compact-test commutator
identity after chart lifting, with the published Euclidean additive estimate.
The remaining Hⁿ input is the norm of the fixed compact extension; this is
not yet the final periodic Hⁿ estimate (`app:ch_background:eq:bg-commutator`). -/
theorem exists_chartLift_compact_commutator_bound
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
        ∃ w : L²,
          orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i 1 : E)) is
            (toEuclidean (𝕜 := ℂ) (T (hm.toLp u)) : 𝓢'(E, ℂ)) -
            (toEuclidean (𝕜 := ℂ) (T du) : 𝓢'(E, ℂ)) = (w : 𝓢'(E, ℂ)) ∧
          ‖w‖ ≤ C * (fourierSobolevNorm (n : ℝ) (χ.extendL2 hu) +
            max 1 H * ‖hm.toLp u‖) := by
  obtain ⟨C, hC, he⟩ := exists_twoPositionL2Operator_compact_commutator_bound hd r n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM is hlen hH χ u hu hm
  obtain ⟨w, hw, hn⟩ := he b hb hs H hM is hlen hH
    (χ.extend u) (χ.smooth_extend hu) (χ.compact_extend u)
  refine ⟨w, ?_, ?_⟩
  · rw [toEuclidean_torusL2Operator_eq_extension hd hr b hb hs M _ χ hu hm,
      toEuclidean_torusL2Operator_eq_extension hd hr b hb hs M _ χ
        (hu.coordinateDerivList is)]
    rw [twoPositionL2Operator_derivative_extension hd r b hb hs M _ χ hu is] at hw
    exact hw
  · apply hn.trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact add_le_add_right
      (mul_le_mul_of_nonneg_left (χ.norm_extendL2_le hu hm) (le_trans zero_le_one (le_max_left 1 H))) _

end JanetCartan.Pseudodifferential.DifferentialChart
