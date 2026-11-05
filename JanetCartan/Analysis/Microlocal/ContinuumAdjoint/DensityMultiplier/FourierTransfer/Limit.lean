module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.GraphClosure
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.PartialFourier.Realization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.Hilbert.Space

/-!
# Passage from mixed test estimates to physical Sobolev limits

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, an estimate on compact smooth tests
passes to the exact strong limits supplied by `GraphClosure`. Completeness of
the shared physical Sobolev space supplies membership of the limit; continuity
of its inclusion into L² identifies that limit with the actual partial unitary
inverse. No new Sobolev scale is introduced.

The test-function mixed-jet/partial-Plancherel estimate is an explicit premise
here. Its producer is `FourierTransfer.TestEstimate`, and `FourierTransfer`
instantiates it to obtain the all-orders strong-limit transfer consumed by
`jc-continuum-density-multiplier`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- A uniform mixed-jet estimate on compact smooth tests passes to strong
limits of the tests and all their mixed jets. The constant is unchanged.
Membership follows from completeness, and the norm bound follows from norm
convergence in the existing physical Sobolev space
(`app:ch_background:eq:bg-density-adjoint`).

The explicit `htest` premise must be proved by the separate test-function
partial-Plancherel estimate; `GraphClosure.exists_densitySymbol_weakGraph_bound`
supplies `hu` and `hJ` for the density symbol. This conditional lemma is consumed
by the final Fourier-transfer assembly and is not the unconditional estimate. -/
theorem memPhysicalSobolev_partialUnitaryInverse_of_test_bound (s : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ f : carrierInitialTestSpace n,
      MemPhysicalSobolev s (partialUnitaryInverse n (carrierInitialTestToLp f)) ∧
      physicalSobolevNorm s (partialUnitaryInverse n (carrierInitialTestToLp f)) ≤
        C * mixedCarrierJetNorm s f.val)
    (u : ℕ → carrierInitialTestSpace n) (v : CarrierL2 n)
    (J : (k : Fin (s + 1)) →
      Lp (CarrierParameter [×(k : ℕ)]→L[ℝ] ℂ) 2 (carrierMeasure n))
    (hu : Tendsto (fun j ↦ carrierInitialTestToLp (u j)) atTop (𝓝 v))
    (hJ : ∀ k : Fin (s + 1),
      Tendsto (fun j ↦ testWeightedCarrierJet k (s - k) (u j)) atTop (𝓝 (J k))) :
    MemPhysicalSobolev s (partialUnitaryInverse n v) ∧
      physicalSobolevNorm s (partialUnitaryInverse n v) ≤ C * ∑ k, ‖J k‖ := by
  let w (j : ℕ) : PhysicalSobolevSpace n s :=
    PhysicalSobolevSpace.ofL2 s (partialUnitaryInverse n (carrierInitialTestToLp (u j)))
      (htest (u j)).1
  have hw (j : ℕ) : PhysicalSobolevSpace.toL2 s (w j) =
      partialUnitaryInverse n (carrierInitialTestToLp (u j)) := rfl
  have hd (p q : ℕ) : dist (w p) (w q) ≤
      C * mixedCarrierJetNorm s ((u p).val - (u q).val) := by
    rw [dist_eq_norm, PhysicalSobolevSpace.norm_eq, map_sub, hw, hw]
    simpa only [map_sub, Submodule.coe_sub] using (htest (u p - u q)).2
  have hc : CauchySeq w := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := mixedCarrierJet_cauchy_of_tendsto s u J hJ
      (ε / (C + 1)) (by positivity)
    refine ⟨N, fun p hp q hq ↦ (hd p q).trans_lt ?_⟩
    calc
      C * mixedCarrierJetNorm s ((u p).val - (u q).val) ≤
          (C + 1) * mixedCarrierJetNorm s ((u p).val - (u q).val) :=
        mul_le_mul_of_nonneg_right (by linarith) (mixedCarrierJetNorm_nonneg _ _)
      _ < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_left (hN p hp q hq) (by positivity)
      _ = ε := by field_simp
  obtain ⟨wlim, hlim⟩ := cauchySeq_tendsto_of_complete hc
  have he : PhysicalSobolevSpace.toL2 s wlim = partialUnitaryInverse n v :=
    tendsto_nhds_unique (((PhysicalSobolevSpace.toL2 s).continuous.tendsto wlim).comp hlim)
      (((partialUnitaryInverse n).continuous.tendsto v).comp hu)
  refine ⟨he ▸ PhysicalSobolevSpace.toL2_mem s wlim, ?_⟩
  have hn : ‖wlim‖ ≤ C * ∑ k, ‖J k‖ := by
    apply le_of_tendsto_of_tendsto hlim.norm
      ((tendsto_mixedCarrierJetNorm s u J hJ).const_mul C)
    apply Eventually.of_forall
    intro j
    dsimp only
    rw [PhysicalSobolevSpace.norm_eq, hw]
    exact (htest (u j)).2
  simpa only [PhysicalSobolevSpace.norm_eq, he] using hn

end JanetCartan.ContinuumAdjoint.DensityMultiplier
