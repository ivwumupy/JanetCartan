module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.SourceEndpoint.Diagonal
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.Profiles

/-!
# Diagonal profiles of the same retained endpoint amplitude

Apply the original coefficient profile to index one of the SAME selected
conic amplitude. The joint pullback retains both time slots and the scaled
covariable. The shell radius stays independent of the source frequency.
The coefficient multiplying this amplitude and the three fixed masks still
need their product estimate to complete the endpoint PDO grade.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EndpointPdoBounds RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => FiniteChain.Graph.JointVariables E
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- The literal selected `W₁(t,t)` has joint normalized and physical shell
grades of order minus one with zero slow-scale offset. The original reserve
ten in `Q` and nine in `B` is consumed by `exists_selected_amplitude_order_profile`.
The analytic hypotheses are exactly the smoothness and seminorm estimates
retained by `exists_finite_direct_operator_bounds`. The displayed point
inclusions are supplied by the retained diagonal frequency coverage, after
choosing its shell representative. Consumer: the amplitude factor of the
endpoint symbol in `CompleteFactor` (`app:ch_regular:eq:high-amplitude`,
`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_selected_endpoint_diagonal_profile
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (ra rb : f.centers → ℝ) (cost : f.centers → ℕ → ℝ)
    (hcost : ∀ p m, 0 < cost p m) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (Rstar : ℕ), 10 ≤ Rstar → ∀ L : ℝ, 1 ≤ L →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat),
      (∀ j, cNorm (closedBall x RQ) j Q ≤ A j * L ^ (j - Rstar)) →
      (∀ j, cNorm (closedBall x RQ) j B ≤ A j * L ^ (j - Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (C : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      let W := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p 1))) →
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p (R ρ : ℝ), 1 ≤ R →
      (∀ v : V, endpointJointDiagonal (ρ / R) v ∈ J p → ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ (W p 1)
          (w.1.1 0) (w.1.1 0) (spatialPart w.1.1) (spatialPart (ρ • w.2.1))) v‖ ≤
          R⁻¹ * D m * (max 1 |ρ / R|) ^ m * L ^ m) ∧
      (∀ η (z : E × E), diagonalPoint η z.1 ∈ J p → ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ (W p 1)
          (w.1 0) (w.1 0) (spatialPart w.1) (R • η)) z‖ ≤ R⁻¹ * D m * L ^ m) := by
  obtain ⟨D, hD, hprofile⟩ := exists_selected_amplitude_order_profile f ra rb cost hcost A hA
  refine ⟨D, hD, ?_⟩
  intro Rstar hRstar L hL Q B hQ hB Φ C angular J W hW hbudget p R ρ hR
  have hb m : BoundedTwoTimeOrderSeminorm 1 (J p) m (W p 1) ∧
      twoTimeOrderSeminorm 1 (J p) m (W p 1) ≤ D m * L ^ m := by
    simpa only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] using hprofile Rstar hRstar L hL Q B hQ hB Φ C angular hbudget p 1 m
  have hJ : IsCompact (J p) := isCompact_bufferedJetSet _ _ _ _ _
  have hRp : 0 < R := zero_lt_one.trans_le hR
  constructor
  · intro v hv m
    have hn := norm_iteratedFDeriv_endpointJointDiagonal_le hJ (W p 1) (hW p) hR (hb m).1 hv
    simp only [pow_one] at hn
    apply hn.trans
    calc
      _ ≤ R⁻¹ * (D m * L ^ m) * (max 1 |ρ / R|) ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb m).2 (by positivity))
          (by positivity)
      _ = _ := by ring
  · intro η z hz m
    have hn := norm_iteratedFDeriv_endpointPhysicalDiagonal_le hJ (W p 1) (hW p) hR (hb m).1 η hz
    simp only [pow_one] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_left (hb m).2 (inv_nonneg.mpr hRp.le)).trans_eq
      (by ring))

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
