module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.PhysicalAmplitude.Recovery
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Geometry.Domains

/-!
# Physical covectors in the original retained radial band

The physical domain of `exists_selected_elapsed_physical_carriers` maps into
the original `bufferedJetSet`, with a dilation of size order minus one.
Consumer: the physical residual profile (`app:ch_regular:eq:high-amplitude`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization.PhysicalAmplitude
open RegularSector RegularSector.Characteristic ConicPhase EvolutionIntegral
variable {d : ℕ}
local notation "J" => SymbolBudgets.TwoTimePoint d

/-- Dilation from the explicit physical domain into the original seminorm
carrier. Both times and position stay fixed, and the dilation supplies the
full negative-order weight (`app:ch_regular:eq:high-amplitude`). -/
theorem physical_covector_dilation_bounds
    (ℓ : Euclidean d →L[ℝ] ℝ) (z : RootState (Euclidean d))
    {ε b ra rb : ℝ} (hε : 0 < ε) (hεb : ε ≤ b)
    (hra : 0 < ra) (hab : ra ≤ rb) {w : J}
    (hw : w ∈ bufferedBase z ε ×ˢ angularCone ℓ z.2.2 ε)
    (hn : (1/2 : ℝ) < ‖w.2‖) :
    let t := ra / ℓ w.2
    let C := 3 * ra * (1 + ‖z.2.2‖ + ε)
    0 < t ∧ 0 ≤ C ∧ t ≤ C ∧ t * (1 + ‖w.2‖) ≤ C ∧
      covectorDilation t w ∈ bufferedJetSet ℓ z b ra rb := by
  intro t C
  have hp : 0 < ℓ w.2 := hw.2.1
  have ht : 0 < t := div_pos hra hp
  have hθ : (ℓ w.2)⁻¹ • w.2 ∈ ball z.2.2 ε := hw.2.2
  have hθnorm : ‖(ℓ w.2)⁻¹ • w.2‖ ≤ ‖z.2.2‖ + ε := by
    have hh := dist_triangle ((ℓ w.2)⁻¹ • w.2) z.2.2 0
    rw [dist_zero_right, dist_zero_right] at hh
    have hd : dist ((ℓ w.2)⁻¹ • w.2) z.2.2 < ε := hθ
    linarith
  have htn : t * ‖w.2‖ ≤ ra * (‖z.2.2‖ + ε) := by
    have hh := mul_le_mul_of_nonneg_left hθnorm hra.le
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)] at hh
    simpa only [t, div_eq_mul_inv, mul_assoc] using hh
  have htC : t * (1 + ‖w.2‖) ≤ C := by
    dsimp only [C]
    nlinarith [mul_pos ht (by linarith : 0 < 2 * ‖w.2‖ - 1)]
  refine ⟨ht, by dsimp only [C]; positivity, ?_, htC, ?_⟩
  · exact (le_mul_of_one_le_right ht.le (by linarith [norm_nonneg w.2])).trans htC
  · have hb : dist w.1.1 z.1 < 2*ε ∧ dist w.1.2.1 z.1 < 2*ε ∧
        dist w.1.2.2 z.2.1 < 2*ε := by
      simpa only [bufferedBase, mem_ball, Prod.dist_eq, max_lt_iff] using hw.1
    refine ⟨⟨hb.1.le.trans (by linarith), hb.2.1.le.trans (by linarith),
      hb.2.2.le.trans (by linarith)⟩, ?_⟩
    refine ⟨(ra, (ℓ w.2)⁻¹ • w.2),
      ⟨⟨le_rfl, hab⟩, (ball_subset_closedBall.trans (closedBall_subset_closedBall hεb)) hθ,
        by simp only [mem_ofPred_eq, map_smul, smul_eq_mul, inv_mul_cancel₀ hp.ne']⟩, ?_⟩
    change ra • ((ℓ w.2)⁻¹ • w.2) = t • w.2
    rw [smul_smul]
    rfl

end JanetCartan.ArbitraryAccuracy.SelectedLocalization.PhysicalAmplitude
