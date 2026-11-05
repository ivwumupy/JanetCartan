module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.SourceEndpoint.RetainedProfiles

/-!
# The retained endpoint seminorm with its original reserve

The normalized band initializer retains the actual two-time seminorm of
`W₁`, bounded by coefficient derivatives of orders `j+10` and `j+9`.
Substituting the original coefficient profiles preserves every remaining
derivative reserve. This is the primitive producer for the endpoint input of
`app:ch_response:eq:fixed-factor-transfer`, before multiplying by `Q₀`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization

open RegularSector RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.ConicPhase RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)

/-- Recover the unspent reserve from the SAME supplied endpoint amplitude's
retained seminorm certificate. The certificate is the index-one component
of `exists_finite_direct_operator_bounds`; the coefficient profiles are
produced by the original admissible history. No symbol estimate is assumed
(`app:ch_regular:eq:high-amplitude`). -/
theorem exists_selected_endpoint_reserved_amplitude_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (ra rb : f.centers → ℝ) (cost : f.centers → ℕ → ℝ)
    (hcost : ∀ p m, 0 ≤ cost p m) (AQ AB : ℕ → ℝ)
    (hAQ : ∀ j, 0 ≤ AQ j) (hAB : ∀ j, 0 ≤ AB j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (Rreserve Rcoeff : ℕ), Rreserve+10 ≤ Rcoeff → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ AQ j * L ^ (j-Rcoeff)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ AB j * L ^ (j-Rcoeff)) →
      ∀ W : f.centers → TwoTimeAmplitude d (d+1),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      (∀ p m, BoundedTwoTimeOrderSeminorm 1 (J p) m (W p) ∧
        twoTimeOrderSeminorm 1 (J p) m (W p) ≤ cost p m *
          (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p m, BoundedTwoTimeOrderSeminorm 1 (J p) m (W p) ∧
        twoTimeOrderSeminorm 1 (J p) m (W p) ≤ D m * L ^ (m-Rreserve) := by
  classical
  let Dp := fun p m ↦ cost p m * (1+AQ (m+10)+AB (m+9))
  have hDp p m : 0 ≤ Dp p m := mul_nonneg (hcost p m)
    (by linarith [hAQ (m+10), hAB (m+9)])
  refine ⟨fun m ↦ ∑ p, Dp p m, fun m ↦ Finset.sum_nonneg (fun p _ ↦ hDp p m), ?_⟩
  intro Rreserve Rcoeff hR L hL Q B hQ hB W J hbudget p m
  refine ⟨(hbudget p m).1, (hbudget p m).2.trans ?_⟩
  have hQ' : cNorm (closedBall x RQ) (m+10) Q ≤ AQ (m+10) * L ^ (m-Rreserve) :=
    (hQ (m+10)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : m+10-Rcoeff ≤ m-Rreserve)) (hAQ _))
  have hB' : cNorm (closedBall x RQ) (m+9) B ≤ AB (m+9) * L ^ (m-Rreserve) :=
    (hB (m+9)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega : m+9-Rcoeff ≤ m-Rreserve)) (hAB _))
  have hone : 1 ≤ L ^ (m-Rreserve) := one_le_pow₀ hL
  calc
    _ ≤ Dp p m * L ^ (m-Rreserve) := by
      apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hone hQ') hB')
        (hcost p m)).trans_eq
      dsimp [Dp]
      ring
    _ ≤ (∑ p, Dp p m) * L ^ (m-Rreserve) := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun p _ ↦ hDp p m) (Finset.mem_univ p))
      (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
