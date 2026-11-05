module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.WeakGraph

/-!
# Quantitative closure of the density symbol's weak graph

For `app:ch_background:eq:bg-density-adjoint`, the smooth estimate passes to
the actual weak carrier jets of the literal unbounded multiplier. The input is
a compact smooth approximation converging in the mixed graph, together with
convergence of its numerical norm. The shared raw scale construction must
supply this approximation and compare that norm with `X^(s+1)`. No output
membership, output estimate, or Fourier transfer is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow
variable {n : ℕ}

/-- The L² norm of a realized test jet is its numerical jet energy, for
the limit estimate in `app:ch_background:eq:bg-density-adjoint`. -/
theorem norm_testWeightedCarrierJet (k t : ℕ) (f : carrierInitialTestSpace n) :
    ‖testWeightedCarrierJet k t f‖ =
      lpNorm (weightedCarrierJet k t f.val) 2 (carrierMeasure n) := by
  simp only [testWeightedCarrierJet, Lp.norm_toLp, toReal_eLpNorm]

/-- Strong convergence of the finitely many mixed jets passes their total
norm to the limit (`app:ch_background:eq:bg-density-adjoint`). -/
theorem tendsto_mixedCarrierJetNorm (s : ℕ) (f : ℕ → carrierInitialTestSpace n)
    (J : (k : Fin (s + 1)) →
      Lp (CarrierParameter [×(k : ℕ)]→L[ℝ] ℂ) 2 (carrierMeasure n))
    (hJ : ∀ k : Fin (s + 1), Tendsto (fun j ↦ testWeightedCarrierJet k (s - k) (f j))
      atTop (𝓝 (J k))) :
    Tendsto (fun j ↦ mixedCarrierJetNorm s (f j).val) atTop
      (𝓝 (∑ k, ‖J k‖)) := by
  have h := tendsto_finsetSum Finset.univ (fun k _ ↦ (hJ k).norm)
  have he (j : ℕ) : (∑ k : Fin (s + 1),
      ‖testWeightedCarrierJet k (s - k) (f j)‖) = mixedCarrierJetNorm s (f j).val := by
    simp only [norm_testWeightedCarrierJet]
    exact Fin.sum_univ_eq_sum_range
      (fun k ↦ lpNorm (weightedCarrierJet k (s - k) (f j).val) 2 (carrierMeasure n)) (s + 1)
  simpa only [he] using h

/-- Convergence of each input jet supplies the graph-Cauchy premise of the
multiplier closure. This is a finite-family deduction, independent of the
producer of graph-dense approximations (`app:ch_background:eq:bg-density-adjoint`). -/
theorem mixedCarrierJet_cauchy_of_tendsto (s : ℕ) (f : ℕ → carrierInitialTestSpace n)
    (J : (k : Fin (s + 1)) →
      Lp (CarrierParameter [×(k : ℕ)]→L[ℝ] ℂ) 2 (carrierMeasure n))
    (hJ : ∀ k : Fin (s + 1), Tendsto (fun j ↦ testWeightedCarrierJet k (s - k) (f j))
      atTop (𝓝 (J k))) :
    ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      mixedCarrierJetNorm s ((f p).val - (f q).val) < ε := by
  intro ε hε
  let δ := ε / (s + 2 : ℕ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hc (k : Fin (s + 1)) :=
    Metric.cauchySeq_iff.mp (hJ k).cauchySeq δ hδ
  choose N hN using hc
  refine ⟨Finset.univ.sup N, fun p hp q hq ↦ ?_⟩
  have hnk (k : Fin (s + 1)) : N k ≤ Finset.univ.sup N :=
    Finset.le_sup (f := N) (Finset.mem_univ k)
  have he : mixedCarrierJetNorm s ((f p).val - (f q).val) =
      ∑ k : Fin (s + 1), ‖testWeightedCarrierJet k (s - k) (f p) -
        testWeightedCarrierJet k (s - k) (f q)‖ := by
    simp only [norm_testWeightedCarrierJet_sub]
    exact (Fin.sum_univ_eq_sum_range
      (fun k ↦ lpNorm (weightedCarrierJet k (s - k) ((f p).val - (f q).val))
        2 (carrierMeasure n)) (s + 1)).symm
  calc
    _ = _ := he
    _ ≤ ∑ _k : Fin (s + 1), δ := Finset.sum_le_sum (fun k _ ↦ by
      simpa only [dist_eq_norm] using
        (hN k p ((hnk k).trans hp) q ((hnk k).trans hq)).le)
    _ = (s + 1 : ℕ) * δ := by simp
    _ < (s + 2 : ℕ) * δ := mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self (s + 1)) hδ
    _ = ε := by dsimp [δ]; field_simp

/-- The actual unbounded symbol has weighted weak carrier jets satisfying
the same uniform total-order estimate as on tests. This closes the analytic
graph estimate in `app:ch_background:eq:bg-density-adjoint`. The only analytic
input is approximation of the input, supplied by the separate shared raw-scale
graph-density construction; the parent still has to instantiate it and apply
partial Fourier Sobolev transfer. -/
theorem exists_densitySymbol_weakGraph_bound (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (f : ℕ → carrierInitialTestSpace n) (u : CarrierL2 n) (A : ℝ),
      (∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
        mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) < ε) →
      Tendsto (fun j ↦ carrierInitialTestToLp (f j)) atTop (𝓝 u) →
      Tendsto (fun j ↦ mixedCarrierJetNorm (s + 1) (f j).val) atTop (𝓝 A) →
      ∃ (v : CarrierL2 n)
        (J : (k : Fin (s + 1)) →
          Lp (CarrierParameter [×(k : ℕ)]→L[ℝ] ℂ) 2 (carrierMeasure n)),
        v =ᵐ[carrierMeasure n] (fun x ↦ densityFrequencySymbol ρ χ x * u x) ∧
        Tendsto (fun j ↦ carrierInitialTestToLp
          (densitySymbolTestMap hρ hχsmooth hlow (f j))) atTop (𝓝 v) ∧
        (∀ k : Fin (s + 1), Tendsto (fun j ↦ testWeightedCarrierJet k (s - k)
          (densitySymbolTestMap hρ hχsmooth hlow (f j))) atTop (𝓝 (J k))) ∧
        (∀ (k : Fin (s + 1)) (φ : CarrierVariable n → ℂ),
          ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : Fin k → CarrierParameter,
          (∫ x, φ x * J k x w ∂carrierMeasure n) = (-1 : ℂ)^(k : ℕ) *
            ∫ x, (etaBesselWeight (s - k) x : ℂ) * v x *
              iteratedFDeriv ℝ k (fun z ↦ φ (z, x.2)) x.1 w ∂carrierMeasure n) ∧
        (∑ k, ‖J k‖) ≤ L * A := by
  obtain ⟨L, hL, hb⟩ := exists_densitySymbol_mixedJet_test_bound s hρ hcρ hχsmooth hlow hχ
  refine ⟨L, hL, fun f u A hf hu hA ↦ ?_⟩
  obtain ⟨v, hv, he⟩ := exists_densitySymbolTestL2_limit s hρ hcρ hχsmooth hlow hχ f hf u hu
  have hj (k : Fin (s + 1)) := exists_densitySymbolTestJet_limit s hρ hcρ hχsmooth
    hlow hχ f hf k (by omega)
  choose J hJ using hj
  refine ⟨v, J, he, hv, hJ, ?_, ?_⟩
  · intro k φ hφ hcφ w
    exact weightedCarrierJet_weak_identity_of_tendsto k (s - k)
      (fun j ↦ densitySymbolTestMap hρ hχsmooth hlow (f j)) v (J k) hv (hJ k) hφ hcφ w
  · apply le_of_tendsto_of_tendsto
      (tendsto_mixedCarrierJetNorm s
        (fun j ↦ densitySymbolTestMap hρ hχsmooth hlow (f j)) J hJ)
      (hA.const_mul L)
    exact Eventually.of_forall (fun j ↦ hb (f j).val (f j).property.1 (f j).property.2)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
