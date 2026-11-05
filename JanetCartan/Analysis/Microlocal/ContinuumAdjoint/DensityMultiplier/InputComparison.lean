module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputComparison.FiniteComparison
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputComparison.CoordinateFourier

/-!
# Reverse comparison for compact raw carrier inputs

The finite-dimensional and transverse Plancherel steps of
`app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint` are proved in `FiniteComparison`.
Parameter Fourier differentiation controls the raw Sobolev norms of the
concrete `inputCoordinateTest`s by the original input norm.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- The compact raw tests satisfy the reverse mixed-jet estimate required by
`app:ch_background:eq:bg-density-adjoint`. The finite coordinate expansion has
`3^k` terms at carrier order `k`; each term costs exactly `k` raw Sobolev
orders by the parameter Fourier comparison, so the displayed finite sum is a
uniform constant depending only on the total order `s`. -/
theorem exists_mixedCarrierJetNorm_le_rawTestSobolev (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : carrierInitialTestSpace n,
      mixedCarrierJetNorm s f.val ≤ C * ‖rawTestSobolev s f‖ := by
  let C : ℝ := ∑ k ∈ Finset.range (s + 1), (3 : ℝ) ^ k
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro f
  calc
    mixedCarrierJetNorm s f.val ≤
        ∑ k ∈ Finset.range (s + 1),
          ∑ a : Fin k → (Unit ⊕ Fin 2),
            ‖rawTestSobolev (s - k) (inputCoordinateTest k f a)‖ :=
      mixedCarrierJetNorm_le_sum_rawInputCoordinateTest s f
    _ ≤ ∑ k ∈ Finset.range (s + 1),
          ∑ _a : Fin k → (Unit ⊕ Fin 2), ‖rawTestSobolev s f‖ := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro a ha
      have hklt : k < s + 1 := Finset.mem_range.mp hk
      have hk' : k ≤ s := by omega
      calc
        ‖rawTestSobolev (s - k) (inputCoordinateTest k f a)‖ ≤
            ‖rawTestSobolev (k + (s - k)) f‖ :=
          norm_rawTestSobolev_inputCoordinateTest_le k (s - k) f a
        _ = ‖rawTestSobolev s f‖ := by rw [Nat.add_sub_of_le hk']
    _ = C * ‖rawTestSobolev s f‖ := by
      dsimp [C]
      calc
        (∑ k ∈ Finset.range (s + 1),
            ∑ _a : Fin k → (Unit ⊕ Fin 2), ‖rawTestSobolev s f‖) =
            ∑ k ∈ Finset.range (s + 1),
              ((3 : ℝ) ^ k * ‖rawTestSobolev s f‖) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_const]
          simp [Fintype.card_sum]
        _ = (∑ k ∈ Finset.range (s + 1), (3 : ℝ) ^ k) *
              ‖rawTestSobolev s f‖ := by rw [Finset.sum_mul]

end JanetCartan.ContinuumAdjoint.DensityMultiplier
