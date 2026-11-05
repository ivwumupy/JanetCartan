module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.Sobolev

/-!
# Additive periodic commutator estimates

For `app:ch_background:eq:bg-commutator`, all chart, cutoff and local Sobolev
hypotheses are discharged. The only amplitude hypotheses are the original
smoothness, two-position support, and primitive low and high derivative budgets.
The parent construction remains responsible for producing those amplitudes.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2

namespace JanetCartan.Pseudodifferential.DifferentialChart
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The scalar chart commutator obeys the additive periodic Hⁿ/L² estimate,
with a constant independent of the high amplitude budget. The compact source
extension is constructed internally (`app:ch_background:eq:bg-commutator`). -/
theorem exists_torusL2Operator_periodic_commutator_bound
    (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : HasAmplitudeDerivativeBound b (2 * (d + 1) + is.length) H)
        (u : Torus d → ℂ)
        (hu : IsSmoothPeriodic u) (hm : MemLp u 2),
        let du : PeriodicL2 d ℂ :=
          ((hu.coordinateDerivList is).1.memLp_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).toLp (periodicCoordinateDerivList is u)
        let T := torusL2Operator hd r b hb hs M
          (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        ∃ w : PeriodicL2 d ℂ,
          HasPeriodicWeakDerivativeList is (T (hm.toLp u)) (T du + w) ∧
          ‖w‖ ≤ C * (periodicSobolevNorm n u +
            max 1 H * ‖hm.toLp u‖) := by
  obtain ⟨χ⟩ := nonempty_sourceCutoff (d := d) hr
  obtain ⟨K, hK, hk⟩ := χ.exists_sobolev_extension_bound n
  obtain ⟨C, hC, he⟩ := exists_torusL2Operator_smooth_commutator_bound hd r hr n M
  refine ⟨C * max 1 K, mul_nonneg hC (by positivity), ?_⟩
  intro b hb hs H hM is hlen hH u hu hm
  obtain ⟨w, hw, hn⟩ := he b hb hs H hM is hlen hH χ u hu hm
  refine ⟨w, hw, hn.trans ?_⟩
  calc
    _ ≤ C * (max 1 K * periodicSobolevNorm n u + max 1 H * ‖hm.toLp u‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add _ le_rfl
      exact (hk u hu).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.sqrt_nonneg _))
    _ ≤ C * (max 1 K * periodicSobolevNorm n u +
        max 1 K * (max 1 H * ‖hm.toLp u‖)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add le_rfl
      exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)
    _ = _ := by ring

/-- The finite matrix chart commutator obeys the same additive periodic estimate
on the shared Hilbert row sums. All geometric and Sobolev comparisons are proved;
no commutator estimate is assumed (`app:ch_background:eq:bg-commutator`). -/
theorem exists_matrixTorusL2Operator_periodic_commutator_bound
    (I J : Type*) [Fintype I] [Fintype J]
    (hd : 0 < d) (r : ℝ) (hr : r < 1 / 2) (n : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : I → J → E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (b i j)))
        (hs : ∀ i j ξ, SupportedInCenteredBox r (b i j ξ)) (H : ℝ)
        (hM : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + 1) M)
        (is : List (Fin d)) (_hlen : is.length = n + 1)
        (_hH : ∀ i j, HasAmplitudeDerivativeBound (b i j) (2 * (d + 1) + is.length) H)
        (u : J → Torus d → ℂ)
        (hu : ∀ j, IsSmoothPeriodic (u j)) (hm : ∀ j, MemLp (u j) 2),
        let f : PiLp 2 (fun _ : J ↦ PeriodicL2 d ℂ) :=
          WithLp.toLp 2 (fun j ↦ (hm j).toLp (u j))
        let df : PiLp 2 (fun _ : J ↦ PeriodicL2 d ℂ) := WithLp.toLp 2 (fun j ↦
          (((hu j).coordinateDerivList is).1.memLp_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).toLp (periodicCoordinateDerivList is (u j)))
        let T := matrixOperator (fun i j ↦ torusL2Operator hd r (b i j) (hb i j)
          (hs i j) M (amplitudeDerivativeBound_of_le (hM i j) (Nat.le_succ _)))
        ∃ w : PiLp 2 (fun _ : I ↦ PeriodicL2 d ℂ),
          (∀ i, HasPeriodicWeakDerivativeList is ((T f) i) ((T df) i + w i)) ∧
          ‖w‖ ≤ C * (‖WithLp.toLp 2 (fun j ↦
            periodicSobolevNorm n (u j))‖ + max 1 H * ‖f‖) := by
  obtain ⟨χ⟩ := nonempty_sourceCutoff (d := d) hr
  obtain ⟨K, hK, hk⟩ := χ.exists_matrix_sobolev_extension_bound n
  obtain ⟨C, hC, he⟩ := exists_matrixTorusL2Operator_smooth_commutator_bound I J hd r hr n M
  refine ⟨C * max 1 K, mul_nonneg hC (by positivity), ?_⟩
  intro b hb hs H hM is hlen hH u hu hm
  obtain ⟨w, hw, hn⟩ := he b hb hs H hM is hlen hH χ u hu hm
  refine ⟨w, hw, hn.trans ?_⟩
  dsimp only
  let f : PiLp 2 (fun _ : J ↦ PeriodicL2 d ℂ) := WithLp.toLp 2 (fun j ↦ (hm j).toLp (u j))
  let N : PiLp 2 (fun _ : J ↦ ℝ) := WithLp.toLp 2 (fun j ↦ periodicSobolevNorm n (u j))
  calc
    _ ≤ C * (max 1 K * ‖N‖ + max 1 H * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add _ le_rfl
      exact (hk J u hu).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    _ ≤ C * (max 1 K * ‖N‖ + max 1 K * (max 1 H * ‖f‖)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add le_rfl
      exact le_mul_of_one_le_left (by positivity) (le_max_left _ _)
    _ = _ := by ring

end JanetCartan.Pseudodifferential.DifferentialChart
