module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ResidualSmoothEnvelopes.ComponentTests
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.SobolevRealization.Fourier
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms

/-!
# Spatial jets of the same smooth residual realization

The measured-word smooth envelope construction for
`app:ch_regular:lem:finite-chain` requires finite source Sobolev norms to
control ordinary spatial jets. Both comparisons below use existing Fourier
and local embedding estimates on the unchanged Euclidean Lebesgue space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter Metric
open scoped ContDiff Topology
namespace JanetCartan.FixedDomainInverse.ResidualSmoothEnvelopes
open RetardedSobolev.Spaces FourierIntegral Pseudodifferential
open RegularSector.FiniteAssembly ResponseSmoothParameters
open FiniteChain.Graph.KernelLimits
open ArbitraryAccuracy.EvolutionLocalization.SobolevRealization
open LocalSobolev RegularSector.FiniteAssembly.CoefficientNorms
open RegularSector.Characteristic.RetardedLocalization
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The original scalar Lebesgue test norm controls its physical vector
component in the SAME Fourier Sobolev space. This uses the proved completed
zeroth-jet comparison, for `app:ch_regular:eq:chain-tail`. -/
theorem componentGraphTest_fourier_bound
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    {X : Set E} (hX : IsCompact X) (j : Fin r) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests (e ⁻¹' X),
      vectorFourierSobolevNorm (s : ℝ) (graphTestToLp (componentGraphTest e hX j u)) ≤
        C * ‖ofTest s volume u.val‖ := by
  classical
  refine ⟨fourierComparisonConstant e s, (fourierComparisonConstant_pos e s).le, ?_⟩
  intro u
  let v := componentGraphTest e hX j u
  let w := physicalZeroJet e he s (ofTest s volume u.val)
  have hw := physicalZeroJet_ofTest_ae e he s u.val
  have hc (i : Fin r) : finiteL2CoordinateIsometry volume (graphTestToLp v) i =
      if i = j then w else 0 := by
    by_cases hi : i = j
    · subst i
      rw [ite_eq_left rfl]
      apply Lp.ext
      filter_upwards [finiteL2Coordinates_apply_ae volume (graphTestToLp v) j,
        (graphTest_memLp v).coeFn_toLp, hw] with x hc hv hwx
      change (finiteL2CoordinateIsometry volume (graphTestToLp v) j : E → ℂ) x = _ at hc
      change (graphTestToLp v : E → F) x = v.val x at hv
      change w x = u.val.val (e.symm x) at hwx
      rw [hc, hv, hwx]
      simp [v, componentGraphTest]
    · rw [ite_eq_right hi]
      apply Lp.ext
      filter_upwards [finiteL2Coordinates_apply_ae volume (graphTestToLp v) i,
        (graphTest_memLp v).coeFn_toLp, Lp.coeFn_zero ℂ 2 (volume : Measure E)]
        with x hc hv hz
      change (finiteL2CoordinateIsometry volume (graphTestToLp v) i : E → ℂ) x = _ at hc
      change (graphTestToLp v : E → F) x = v.val x at hv
      rw [hc, hv, hz]
      simp [v, componentGraphTest, hi]
  have hz : fourierSobolevNorm (s : ℝ) (0 : Lp ℂ 2 (volume : Measure E)) = 0 := by
    have hwz : weightedL2Fourier (s : ℝ) (0 : Lp ℂ 2 (volume : Measure E)) = 0 := by
      funext x
      simp [weightedL2Fourier]
    simp only [fourierSobolevNorm, hwz, eLpNorm_zero, ENNReal.toReal_zero]
  apply (matrixFourierSobolevNorm_le_sum (s : ℝ)
    (finiteL2CoordinateIsometry volume (graphTestToLp v))).trans
  simpa only [hc, apply_ite, hz, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    (physicalZeroJet_fourier_bound e he s (ofTest s volume u.val)).2

/-- All-order Sobolev bounds of the fixed measured residual imply finite
spatial jet bounds for its single smooth realization. The source order and
constant precede every source and point, as required by the existing joint
response theorem (`app:ch_regular:lem:finite-chain`). -/
theorem smooth_graph_component_jet_bounds
    (e : (ℝ × (Fin d → ℝ)) ≃L[ℝ] E)
    (he : MeasurePreserving (graphInputCoordinates e) volume volume)
    {X : Set E} (hX : IsCompact X)
    (A : H →L[ℂ] H)
    (R : graphTestSpace (d + 1) r →ₗ[ℂ] (E → F))
    (hR : ∀ u, ContDiff ℝ ∞ (R u) ∧ R u =ᵐ[volume] A (graphTestToLp u))
    (hA : ∀ s : ℕ, ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : graphTestSpace (d + 1) r,
        MemVectorFourierSobolev (s : ℝ) (A (graphTestToLp u)) ∧
        vectorFourierSobolevNorm (s : ℝ) (A (graphTestToLp u)) ≤
          C * vectorFourierSobolevNorm (t : ℝ) (graphTestToLp u))
    (i : Fin r) (j : ℕ) :
    ∃ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' X), ∀ x : E,
        ‖iteratedFDeriv ℝ j (R (componentGraphTest e hX i u)) x‖ ≤
          C * ‖ofTest t volume u.val‖ := by
  obtain ⟨t, C₀, hC₀, hbound⟩ := hA (j + (d + 2))
  obtain ⟨D, hD, hsource⟩ := componentGraphTest_fourier_bound e he hX i t
  obtain ⟨Cf, hCf, hfourier⟩ := vector_restrictionSobolev_nat_bounds (d + 1) r (j + (d + 2))
  obtain ⟨Ce, hCe, hemb⟩ := @exists_cNorm_le_restrictionSobolevNorm (d + 1) j F _ _ _
  let C := Ce * Cf * C₀ * D
  have hCe0 : 0 ≤ Ce := zero_le_one.trans hCe
  refine ⟨t, C, mul_nonneg (mul_nonneg (mul_nonneg hCe0 hCf.le) hC₀) hD, ?_⟩
  intro u x
  let v := componentGraphTest e hX i u
  let w := A (graphTestToLp v)
  let vlocal := restrictL2 (ball x 2) w
  have hr := hfourier w (hbound v).1 (ball x 2) vlocal (restrictL2_coeFn _ w).symm
  have hrv : R v =ᵐ[volume.restrict (ball x 2)] w := ae_restrict_of_ae (hR v).2
  have heq : R v =ᵐ[volume.restrict (ball x 2)] vlocal :=
    hrv.trans (restrictL2_coeFn _ w).symm
  have hc := hemb x 1 2 (by norm_num) (by norm_num) (R v) (hR v).1.contDiffOn
    vlocal heq hr.1
  have hjet := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall x 1)
    ((hR v).1.of_le (by simp)) (mem_closedBall_self (by norm_num)) (le_refl j)
  apply hjet.trans (hc.trans _)
  exact (mul_le_mul_of_nonneg_left (hr.2.trans
    (mul_le_mul_of_nonneg_left ((hbound v).2.trans
      (mul_le_mul_of_nonneg_left (hsource u) hC₀)) hCf.le)) hCe0).trans_eq
    (by dsimp only [C]; ring)


end JanetCartan.FixedDomainInverse.ResidualSmoothEnvelopes
