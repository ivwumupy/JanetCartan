module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputTests

/-!
# From raw test density to the input mixed graph approximation

For the density estimate `app:ch_background:eq:bg-density-adjoint`, two
independent input results suffice: density of the actual raw tests in the
shared raw Hilbert norm, and domination of their mixed jets by that norm.
This file proves the deduction immediately, without waiting for either
producer. Completeness constructs all jet limits and their numerical norm;
the conclusion supplies exactly the input to `SobolevAssembly`.

The final assembly must instantiate both hypotheses. Neither density nor
the reverse mixed-jet norm comparison is asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- The reverse test norm comparison transports raw Hilbert convergence to
each mixed jet. This finite-family argument supplies the input graph closure
in `app:ch_background:eq:bg-density-adjoint`. The test comparison itself is
a separate partial-Plancherel obligation. -/
theorem cauchySeq_testWeightedCarrierJet_of_rawTestSobolev_tendsto (s : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : carrierInitialTestSpace n,
      mixedCarrierJetNorm s f.val ≤ C * ‖rawTestSobolev s f‖)
    (f : ℕ → carrierInitialTestSpace n) (u : RawSobolevSpace n s)
    (hu : Tendsto (fun j ↦ rawTestSobolev s (f j)) atTop (𝓝 u)) (k : Fin (s + 1)) :
    CauchySeq (fun j ↦ testWeightedCarrierJet k (s - k) (f j)) := by
  have hd p q : dist (testWeightedCarrierJet k (s - k) (f p))
      (testWeightedCarrierJet k (s - k) (f q)) ≤
      C * ‖rawTestSobolev s (f p) - rawTestSobolev s (f q)‖ := by
    rw [dist_eq_norm, norm_testWeightedCarrierJet_sub]
    calc
      _ ≤ mixedCarrierJetNorm s ((f p).val - (f q).val) :=
        lpNorm_weightedCarrierJet_le_mixedCarrierJetNorm (by omega)
          (memLp_weightedCarrierJet_of_compactSupport k (s - k)
            ((f p).property.1.sub (f q).property.1)
            ((f p).property.2.sub (f q).property.2))
      _ ≤ _ := by simpa only [map_sub, Submodule.coe_sub] using hb (f p - f q)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq (ε / (C + 1)) (by positivity)
  refine ⟨N, fun p hp q hq ↦ (hd p q).trans_lt ?_⟩
  calc
    _ ≤ (C + 1) * ‖rawTestSobolev s (f p) - rawTestSobolev s (f q)‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left
      (by simpa only [dist_eq_norm] using hN p hp q hq) (by positivity)
    _ = ε := by field_simp

/-- Raw test density and the reverse norm comparison produce the precise
input approximation consumed by the density multiplier. The jet limits and
their limiting norm are constructed, and the latter is bounded by the full
raw Hilbert norm. These two explicit input hypotheses must still be proved
for `rawTestSobolev` (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_mixedCarrierJet_approximation_of_denseRange (s : ℕ)
    (hdense : DenseRange (rawTestSobolev (n := n) s))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : carrierInitialTestSpace n,
      mixedCarrierJetNorm s f.val ≤ C * ‖rawTestSobolev s f‖)
    (u : RawSobolevSpace n s) :
    ∃ (f : ℕ → carrierInitialTestSpace n) (A : ℝ),
      (∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
        mixedCarrierJetNorm s ((f p).val - (f q).val) < ε) ∧
      Tendsto (fun j ↦ carrierInitialTestToLp (f j)) atTop
        (𝓝 (RawSobolevSpace.toRawL2 s u)) ∧
      Tendsto (fun j ↦ mixedCarrierJetNorm s (f j).val) atTop (𝓝 A) ∧ A ≤ C * ‖u‖ := by
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp (hdense u)
  choose f hf using hv
  have hlim : Tendsto (fun j ↦ rawTestSobolev s (f j)) atTop (𝓝 u) := by
    simpa only [hf] using hvlim
  have hj (k : Fin (s + 1)) := cauchySeq_tendsto_of_complete
    (cauchySeq_testWeightedCarrierJet_of_rawTestSobolev_tendsto s hC hb f u hlim k)
  choose J hJ using hj
  have hA := tendsto_mixedCarrierJetNorm s f J hJ
  refine ⟨f, ∑ k, ‖J k‖, mixedCarrierJet_cauchy_of_tendsto s f J hJ, ?_, hA, ?_⟩
  · have h := ((RawSobolevSpace.toRawL2 s).continuous.tendsto u).comp hlim
    change Tendsto (fun j ↦ RawSobolevSpace.toRawL2 s (rawTestSobolev s (f j)))
      atTop (𝓝 (RawSobolevSpace.toRawL2 s u)) at h
    simpa only [toRawL2_rawTestSobolev] using h
  · exact le_of_tendsto_of_tendsto hA (hlim.norm.const_mul C)
      (Eventually.of_forall fun j ↦ hb (f j))

end JanetCartan.ContinuumAdjoint.DensityMultiplier
