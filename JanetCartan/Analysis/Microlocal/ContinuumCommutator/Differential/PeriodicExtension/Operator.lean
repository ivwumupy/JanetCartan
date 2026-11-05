module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.PeriodicExtension.Completion
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Bounds

/-!
# The scalar chart commutator on the periodic Sobolev space

The primitive full-amplitude budgets supply the smooth estimate; completion
retains its additive bound for `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
open JanetCartan.AmplitudeBound
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.Pseudodifferential.DifferentialChart
open PeriodicSobolevSpace PeriodicExtension
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The scalar all-data extension and its additive bound, with the constant
chosen before the amplitude, high budget, and ordered word
(`app:ch_background:eq:bg-commutator`). -/
theorem exists_torusL2Operator_sobolev_commutator_bound
    (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) H),
        let T := torusL2Operator hd r b hb hs M
          (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        ∃ S : PeriodicSobolevSpace d ℂ n →L[ℝ] PeriodicL2 d ℂ,
          (∀ f : smoothFields d, SmoothCommutator n is (T.restrictScalars ℝ) f
            (S (smoothRealization n f))) ∧
          ∀ u, ‖S u‖ ≤ C * (‖u‖ + max 1 H * ‖toL2 n u‖) := by
  obtain ⟨C, hC, he⟩ := exists_torusL2Operator_periodic_commutator_bound hd r hr n M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM is hlen hH
  apply exists_commutator_extension n is _ C (max 1 H) hC (by positivity)
  intro f
  obtain ⟨w, hw, hn⟩ := he b hb hs H hM is hlen hH f.val f.property
    (f.property.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  refine ⟨w, ?_, ?_⟩
  · unfold SmoothCommutator
    rw [smoothDerivative_apply]
    exact hw
  · have heq : ‖smoothRealization n f‖ = periodicSobolevNorm n f.val := by
      rw [norm_eq]
      simp only [smoothRealization, LinearMap.coe_mk, AddHom.coe_mk,
        periodicSobolevNorm, periodicFourierCoeff_congr_ae (toL2_ofSmooth_ae n f.val f.property)]
    rw [heq]
    exact hn

variable (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (n : ℕ) (M : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (H : ℝ)
  (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
  (is : List (Fin d)) (hlen : is.length = n + 1)
  (hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) H)

/-- The actual scalar commutator extended from the smooth weak identity to Hⁿ
(`app:ch_background:eq:bg-commutator`). -/
def torusSobolevCommutator (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (n : ℕ) (M : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (H : ℝ)
  (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
  (is : List (Fin d)) (hlen : is.length = n + 1)
  (hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) H)
 : PeriodicSobolevSpace d ℂ n →L[ℝ] PeriodicL2 d ℂ :=
  ((exists_torusL2Operator_sobolev_commutator_bound hd r hr n M).choose_spec.2
    b hb hs H hM is hlen hH).choose

/-- Agreement of the completed operator with every smooth weak commutator
(`app:ch_background:eq:bg-commutator`). -/
theorem torusSobolevCommutator_ofSmooth (f : Torus d → ℂ) (hf : IsSmoothPeriodic f) :
    let T := torusL2Operator hd r b hb hs M
      (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
    HasPeriodicWeakDerivativeList is (T (toL2 n (ofSmooth n f hf)))
      (T (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f) (hf.coordinateDerivList is))) +
        torusSobolevCommutator hd r hr n M b hb hs H hM is hlen hH (ofSmooth n f hf)) := by
  have h := ((exists_torusL2Operator_sobolev_commutator_bound hd r hr n M).choose_spec.2
    b hb hs H hM is hlen hH).choose_spec.1 ⟨f, hf⟩
  simpa only [SmoothCommutator, smoothDerivative_apply, smoothRealization,
    LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_restrictScalars',
    torusSobolevCommutator] using h

/-- The additive estimate on every Sobolev input, with a constant depending
only on dimension, the fixed physical box, order, and low budget
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_torusSobolevCommutator_le (u : PeriodicSobolevSpace d ℂ n) :
    ‖torusSobolevCommutator hd r hr n M b hb hs H hM is hlen hH u‖ ≤
      (exists_torusL2Operator_sobolev_commutator_bound hd r hr n M).choose *
        (‖u‖ + max 1 H * ‖toL2 n u‖) :=
  ((exists_torusL2Operator_sobolev_commutator_bound hd r hr n M).choose_spec.2
    b hb hs H hM is hlen hH).choose_spec.2 u

/-- Any Sobolev-convergent smooth approximation gives the same L² commutator
limit. The result is independent of the approximating sequence
(`app:ch_background:eq:bg-commutator`). -/
theorem torusSobolevCommutator_tendsto {ι : Type*} {l : Filter ι}
    (f : ι → Torus d → ℂ) (hf : ∀ j, IsSmoothPeriodic (f j))
    (u : PeriodicSobolevSpace d ℂ n)
    (hu : Tendsto (fun j ↦ ofSmooth n (f j) (hf j)) l (𝓝 u)) :
    Tendsto (fun j ↦ torusSobolevCommutator hd r hr n M b hb hs H hM is hlen hH
      (ofSmooth n (f j) (hf j))) l
      (𝓝 (torusSobolevCommutator hd r hr n M b hb hs H hM is hlen hH u)) :=
  (torusSobolevCommutator hd r hr n M b hb hs H hM is hlen hH).continuous.tendsto u |>.comp hu

/-- Uniqueness among continuous real-linear extensions of the smooth weak
commutator (`app:ch_background:eq:bg-commutator`). -/
theorem torusSobolevCommutator_unique
    (S : PeriodicSobolevSpace d ℂ n →L[ℝ] PeriodicL2 d ℂ)
    (hS : ∀ f : smoothFields d, SmoothCommutator n is
      ((torusL2Operator hd r b hb hs M
        (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))).restrictScalars ℝ) f
        (S (smoothRealization n f))) :
    S = torusSobolevCommutator hd r hr n M b hb hs H hM is hlen hH :=
  commutator_extension_unique n is _ S _ hS
    (((exists_torusL2Operator_sobolev_commutator_bound hd r hr n M).choose_spec.2
      b hb hs H hM is hlen hH).choose_spec.1)

/-- Every smooth weak commutator representative is the value of the constructed
extension (`app:ch_background:eq:bg-commutator`). -/
theorem torusSobolevCommutator_eq_of_weak (f : Torus d → ℂ) (hf : IsSmoothPeriodic f)
    (w : PeriodicL2 d ℂ)
    (hw : HasPeriodicWeakDerivativeList is
      (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        (toL2 n (ofSmooth n f hf)))
      (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f) (hf.coordinateDerivList is))) + w)) :
    w = torusSobolevCommutator hd r hr n M b hb hs H hM is hlen hH (ofSmooth n f hf) :=
  add_left_cancel (hw.unique
    (torusSobolevCommutator_ofSmooth hd r hr n M b hb hs H hM is hlen hH f hf))

/-- Arbitrary smooth weak commutator representatives converge to the same
constructed value for any Sobolev-convergent approximation. Thus the extension
is independent both of representatives and of approximating sequences
(`app:ch_background:eq:bg-commutator`). -/
theorem torusSobolevCommutator_tendsto_of_weak {ι : Type*} {l : Filter ι}
    (f : ι → Torus d → ℂ) (hf : ∀ j, IsSmoothPeriodic (f j)) (w : ι → PeriodicL2 d ℂ)
    (hw : ∀ j, HasPeriodicWeakDerivativeList is
      (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        (toL2 n (ofSmooth n (f j) (hf j))))
      (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is (f j))
          ((hf j).coordinateDerivList is))) + w j))
    (u : PeriodicSobolevSpace d ℂ n)
    (hu : Tendsto (fun j ↦ ofSmooth n (f j) (hf j)) l (𝓝 u)) :
    Tendsto w l (𝓝 (torusSobolevCommutator hd r hr n M b hb hs H hM is hlen hH u)) := by
  have he (j : ι) := torusSobolevCommutator_eq_of_weak hd r hr n M b hb hs H hM is hlen hH
    (f j) (hf j) (w j) (hw j)
  exact (torusSobolevCommutator_tendsto hd r hr n M b hb hs H hM is hlen hH f hf u hu).congr
    (fun j ↦ (he j).symm)

end JanetCartan.Pseudodifferential.DifferentialChart
