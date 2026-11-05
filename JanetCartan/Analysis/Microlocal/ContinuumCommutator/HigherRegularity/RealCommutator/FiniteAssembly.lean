module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Compression
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.HigherRegularity.RealCommutator.Exterior

/-!
# Finite real normal assembly from complex matrix commutators

For `app:ch_background:eq:bg-commutator`, combine the actual real compressions
with their fixed real weights and the literal exterior multiplier `χ²`. The
complex matrix commutators and their primitive amplitude estimates remain the
producer's obligation. The deductions here preserve the carrier factor four
and choose their total constant from the fixed summand constants and cutoff.
-/

@[expose] public noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
open PeriodicSobolevSpace ContinuumRow
variable {n : ℕ} {κ : Type*} [Fintype κ]
local notation "Vℝ" => EuclideanSpace ℝ (Fin n)
local notation "Vℂ" => EuclideanSpace ℂ (Fin n)

/-- The finite weighted sum of actual compressed commutators and the exterior
Leibniz operator. A coefficient four remains exactly four
(`app:ch_background:eq:bg-realification`, `app:ch_background:eq:bg-commutator`). -/
def matrixSumCutoffCommutator (s : ℕ) (is : List (Fin n)) (hlen : is.length = s + 1)
    (c : κ → ℝ) (K : κ → PeriodicSobolevSpace n Vℂ s →L[ℝ] PeriodicL2 n Vℂ)
    (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ) :
    PeriodicSobolevSpace n Vℝ s →L[ℝ] PeriodicL2 n Vℝ :=
  (∑ a, c a • compressedCommutator s (K a)) + cutoffCommutator χ hχ s is hlen

/-- Exact smooth weak identity for the finite real matrix sum and the actual
exterior cutoff. The complex smooth identities are the precise output of the
full-amplitude matrix producer (`app:ch_background:eq:bg-commutator`). -/
theorem matrixSumCutoffCommutator_ofSmooth
    (s : ℕ) (is : List (Fin n)) (hlen : is.length = s + 1)
    (T : κ → PeriodicL2 n Vℂ →L[ℂ] PeriodicL2 n Vℂ)
    (c : κ → ℝ) (K : κ → PeriodicSobolevSpace n Vℂ s →L[ℝ] PeriodicL2 n Vℂ)
    (hK : ∀ a (f : Torus n → Vℂ) (hf : IsSmoothPeriodic f),
      HasPeriodicWeakDerivativeList is (T a (toL2 s (ofSmooth s f hf)))
        (T a (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
          (hf.coordinateDerivList is))) + K a (ofSmooth s f hf)))
    (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (f : Torus n → Vℝ) (hf : IsSmoothPeriodic f) :
    let E := (∑ a, c a • realOutputCompression (T a)) + cutoffMultiplier (χ ^ 2)
    HasPeriodicWeakDerivativeList is (E (toL2 s (ofSmooth s f hf)))
      (E (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f)
        (hf.coordinateDerivList is))) +
        matrixSumCutoffCommutator s is hlen c K χ hχ (ofSmooth s f hf)) := by
  classical
  dsimp only
  have hm := weakDerivativeList_sum Finset.univ is
    (fun a ↦ c a • realOutputCompression (T a) (toL2 s (ofSmooth s f hf)))
    (fun a ↦ c a • (realOutputCompression (T a)
      (toL2 0 (ofSmooth 0 (periodicCoordinateDerivList is f) (hf.coordinateDerivList is))) +
        compressedCommutator s (K a) (ofSmooth s f hf)))
    (fun a _ ↦ weakDerivativeList_smul
      (compressedCommutator_ofSmooth s is (T a) (K a) (hK a) f hf) (c a))
  have h := weakDerivativeList_add hm (cutoffCommutator_ofSmooth χ hχ s is hlen f hf)
  convert h using 1 <;>
    simp only [matrixSumCutoffCommutator, add_apply, sum_apply, smul_apply,
      smul_add, Finset.sum_add_distrib]; abel

/-- The total additive constant is the weighted sum of the fixed matrix
constants plus the fixed exterior constant. It is chosen without knowing the
amplitudes or their common high budget (`app:ch_background:eq:bg-commutator`). -/
theorem norm_matrixSumCutoffCommutator_le
    (s : ℕ) (is : List (Fin n)) (hlen : is.length = s + 1)
    (c C : κ → ℝ) (hC : ∀ a, 0 ≤ C a)
    (K : κ → PeriodicSobolevSpace n Vℂ s →L[ℝ] PeriodicL2 n Vℂ)
    (H : ℝ) (hK : ∀ a u, ‖K a u‖ ≤ C a * (‖u‖ + max 1 H * ‖toL2 s u‖))
    (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (u : PeriodicSobolevSpace n Vℝ s) :
    ‖matrixSumCutoffCommutator s is hlen c K χ hχ u‖ ≤
      ((∑ a, |c a| * C a) + cutoffCommutatorConstant χ hχ s) *
        (‖u‖ + max 1 H * ‖toL2 s u‖) := by
  classical
  let X := ‖u‖ + max 1 H * ‖toL2 s u‖
  have hsum : ‖∑ a, c a • compressedCommutator s (K a) u‖ ≤
      (∑ a, |c a| * C a) * X := by
    calc
      _ ≤ ∑ a, ‖c a • compressedCommutator s (K a) u‖ := norm_sum_le _ _
      _ ≤ ∑ a, |c a| * (C a * X) := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (norm_compressedCommutator_le s (K a) (C a) (max 1 H) (hC a)
            (by positivity) (hK a) u) (abs_nonneg _)
      _ = _ := by simp only [← mul_assoc, Finset.sum_mul]
  have hq := norm_cutoffCommutator_le χ hχ s is hlen u
  have hq0 := (cutoffCommutatorConstant_pos χ hχ s).le
  change ‖(∑ a, c a • compressedCommutator s (K a)) u +
    cutoffCommutator χ hχ s is hlen u‖ ≤ _
  simp only [sum_apply, smul_apply]
  calc
    _ ≤ ‖∑ a, c a • compressedCommutator s (K a) u‖ +
        ‖cutoffCommutator χ hχ s is hlen u‖ := norm_add_le _ _
    _ ≤ (∑ a, |c a| * C a) * X + cutoffCommutatorConstant χ hχ s * ‖u‖ :=
      add_le_add hsum hq
    _ ≤ _ := by
      have hn : 0 ≤ cutoffCommutatorConstant χ hχ s * (max 1 H * ‖toL2 s u‖) :=
        mul_nonneg hq0 (by positivity)
      dsimp only [X]
      nlinarith

end JanetCartan.ContinuumCommutator.HigherRegularity.RealCommutator
