module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailJets.Decay
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Vector
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.PhysicalTailSobolev.Realization

/-!
# Polynomial LOW bound for the actual right proof localizer

The `hlow` input of `finiteChain_observation_rapidDecayAt` concerns `T Mi`,
so the LOW bound of the original factor alone is insufficient. The same
compact right symbol has polynomial L² norm, from its actual uncut kernel
jets and the existing Schur endpoint. No localization estimate or extra
frequency-dependent cutoff is introduced (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open FourierIntegral FiniteChain.Graph Pseudodifferential IdentityDefect
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A fixed smooth compact right proof mask has L² norm at most `C ρ^n`.
The uncut kernel jets are produced by
`exists_rightLocalizerScalarKernel_jet_decay`; the all-data bound is produced
by the existing Schur/weak-derivative endpoint at Sobolev order zero.
The SAME bounded realization is identified on graph tests. This supplies
`hlow` for the complete solver and residual after their primitive LOW
construction (`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_rightLocalizer_polynomial_low_bound
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ Mi : H →L[ℂ] H,
      (∀ u : H, Mi u =ᵐ[volume] fun x ↦ WithLp.toLp 2
        (rightLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ‖Mi‖ ≤ C * ρ ^ n := by
  obtain ⟨B, hB, hb⟩ := exists_rightLocalizerScalarKernel_jet_decay mi hi his 0 (n + 1)
  obtain ⟨K, hK, hSobolev⟩ :=
    PhysicalTailSobolev.exists_physicalTail_vector_fourierSobolev_constant (n := n) (r := r) 0
  let c : ℝ := min 1 (1 / (2 * Real.pi))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨K * (B / c ^ (n + 1)), mul_nonneg hK (div_nonneg hB (pow_nonneg hc.le _)), ?_⟩
  intro ρ hρ Mi hMi
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hkernel : ∀ j ≤ 0, ∀ x y : E,
      (1 + ‖x - y‖) ^ (n + 1) *
        ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖ ≤
          (B / c ^ (n + 1)) * ρ ^ n := by
    intro j hj x y
    have hcρ : c ≤ ρ / (2 * Real.pi) :=
      (min_le_right _ _).trans (div_le_div_of_nonneg_right hρ (by positivity))
    have hspace : c * (1 + ‖x - y‖) ≤ 1 + ρ / (2 * Real.pi) * ‖x - y‖ := by
      calc
        _ = c + c * ‖x - y‖ := by ring
        _ ≤ _ := add_le_add (min_le_left _ _)
          (mul_le_mul_of_nonneg_right hcρ (norm_nonneg _))
    have hh : c ^ (n + 1) * ((1 + ‖x - y‖) ^ (n + 1) *
        ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖) ≤
          B * ρ ^ n := by
      calc
        _ = (c * (1 + ‖x - y‖)) ^ (n + 1) *
            ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖ := by
          rw [mul_pow]; ring
        _ ≤ (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ (n + 1) *
            ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖ := by gcongr
        _ ≤ _ := by simpa only [Nat.add_zero] using hb ρ hρ j hj x y
    have hdiv : (1 + ‖x - y‖) ^ (n + 1) *
        ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖ ≤
          (B * ρ ^ n) / c ^ (n + 1) :=
      (le_div_iff₀ (pow_pos hc (n + 1))).mpr (by simpa only [mul_comm] using hh)
    exact hdiv.trans_eq (by ring)
  have haction (u : graphTestSpace n r) : Mi (graphTestToLp u) =ᵐ[volume]
      fun x ↦ ∫ y, rightLocalizerScalarKernel ρ mi x y • u.val y := by
    refine (rightLocalizer_graphTest_action_of_ae ρ mi Mi hMi u).trans (.of_forall fun x ↦ ?_)
    dsimp only
    rw [rightLocalizer_eq_integral_scalarKernel hρpos.ne' mi hi.continuous his
      (fun y ↦ (u.val y).ofLp)
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).continuous.comp
        u.property.1.continuous)]
    exact ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)).symm.integral_comp_comm
      (μ := volume) (fun y ↦ rightLocalizerScalarKernel ρ mi x y • (u.val y).ofLp)).symm
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have h := hSobolev (rightLocalizerScalarKernel ρ mi)
    (contDiff_rightLocalizerScalarKernel hρpos.ne' mi hi his)
    ((B / c ^ (n + 1)) * ρ ^ n) (by positivity) hkernel Mi haction u
  simpa only [Nat.cast_zero, vectorFourierSobolevNorm_zero, mul_assoc] using h.2

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
