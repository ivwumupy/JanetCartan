module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.MixedJetBound
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.Closure
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierExtension.Tests

/-!
# Convergence of the mixed output jets

The test domain here is the shared `carrierInitialTestSpace` on literal product
Lebesgue measure. The total mixed estimate proves that a sequence Cauchy in the
input jet aggregate has strongly convergent output jets of every permitted
order. This is the analytic continuity step for
`app:ch_background:eq:bg-density-adjoint`.

The zero-order limit is identified with the literal unbounded multiplier.
Identifying the higher limits as the weak derivatives of this multiplier,
and transporting their norm through the partial inverse Fourier equivalence,
remain obligations of the parent assembly. No graph density or Fourier
identification is asserted by this leaf.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow
variable {n : ℕ}

/-- The exact symbol defines a linear endomorphism of the existing compact
smooth test domain (`app:ch_background:eq:bg-density-adjoint`). -/
def densitySymbolTestMap {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hχ : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0) :
    carrierInitialTestSpace n →ₗ[ℂ] carrierInitialTestSpace n where
  toFun f := ⟨fun x ↦ densityFrequencySymbol ρ χ x * f.val x,
    densitySymbol_mul_preserves_tests hρ hχ hlow f.property.1 f.property.2⟩
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' c f := by ext x; exact mul_left_comm _ _ _

/-- Actual L² realization of a weighted jet of a shared compact smooth test
(`app:ch_background:eq:bg-density-adjoint`). -/
def testWeightedCarrierJet (k t : ℕ) (f : carrierInitialTestSpace n) :
    Lp (CarrierParameter [×k]→L[ℝ] ℂ) 2 (carrierMeasure n) :=
  (memLp_weightedCarrierJet_of_compactSupport k t f.property.1 f.property.2).toLp _

/-- Weighted carrier differentiation commutes with subtraction on the smooth
test domain (`app:ch_background:eq:bg-density-adjoint`). -/
theorem weightedCarrierJet_sub (k t : ℕ) {f g : CarrierVariable n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    weightedCarrierJet k t (f - g) = weightedCarrierJet k t f - weightedCarrierJet k t g := by
  funext x
  have hf' : ContDiff ℝ k (fun z ↦ f (z, x.2)) :=
    (hf.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hg' : ContDiff ℝ k (fun z ↦ g (z, x.2)) :=
    (hg.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  change etaBesselWeight t x •
    iteratedFDeriv ℝ k ((fun z ↦ f (z, x.2)) - (fun z ↦ g (z, x.2))) x.1 = _
  rw [iteratedFDeriv_sub hf' hg']
  simp only [Pi.sub_apply, smul_sub, weightedCarrierJet]

/-- The distance of the actual jet classes is exactly the numerical jet norm
of the difference; there is no choice of representative in the estimate
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_testWeightedCarrierJet_sub (k t : ℕ) (f g : carrierInitialTestSpace n) :
    ‖testWeightedCarrierJet k t f - testWeightedCarrierJet k t g‖ =
      lpNorm (weightedCarrierJet k t (f.val - g.val)) 2 (carrierMeasure n) := by
  rw [Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (testWeightedCarrierJet k t f) (testWeightedCarrierJet k t g),
    (memLp_weightedCarrierJet_of_compactSupport k t f.property.1 f.property.2).coeFn_toLp,
    (memLp_weightedCarrierJet_of_compactSupport k t g.property.1 g.property.2).coeFn_toLp]
    with x hsub hf hg
  rw [hsub, Pi.sub_apply]
  change (memLp_weightedCarrierJet_of_compactSupport k t f.property.1 f.property.2).toLp _ x -
    (memLp_weightedCarrierJet_of_compactSupport k t g.property.1 g.property.2).toLp _ x = _
  rw [hf, hg, weightedCarrierJet_sub k t f.property.1 g.property.1]
  rfl

/-- Cauchy approximation in the input's total mixed jet aggregate produces
Cauchy output jets, using the proved one-derivative multiplier bound.
The shared graph-density theorem must supply the input approximation
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem cauchySeq_densitySymbolTestJet (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) (f : ℕ → carrierInitialTestSpace n)
    (hf : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) < ε)
    (k : ℕ) (hk : k ≤ s) :
    CauchySeq (fun j ↦ testWeightedCarrierJet k (s - k)
      (densitySymbolTestMap hρ hχsmooth hlow (f j))) := by
  obtain ⟨L, hL, hb⟩ :=
    exists_densitySymbol_mixedJet_difference_bound s hρ hcρ hχsmooth hlow hχ
  let v j := densitySymbolTestMap hρ hχsmooth hlow (f j)
  have hd p q : dist (testWeightedCarrierJet k (s - k) (v p))
      (testWeightedCarrierJet k (s - k) (v q)) ≤
      L * mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) := by
    rw [dist_eq_norm, norm_testWeightedCarrierJet_sub]
    refine (lpNorm_weightedCarrierJet_le_mixedCarrierJetNorm (by omega : k + (s - k) ≤ s)
      (memLp_weightedCarrierJet_of_compactSupport k (s - k)
        ((v p).property.1.sub (v q).property.1)
        ((v p).property.2.sub (v q).property.2))).trans ?_
    exact hb (f p).val (f q).val (f p).property.1 (f p).property.2
      (f q).property.1 (f q).property.2
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hf (ε / (L + 1)) (by positivity)
  refine ⟨N, fun p hp q hq ↦ (hd p q).trans_lt ?_⟩
  calc
    L * mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) ≤
        (L + 1) * mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) :=
      mul_le_mul_of_nonneg_right (by linarith) (mixedCarrierJetNorm_nonneg _ _)
    _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left (hN p hp q hq) (by positivity)
    _ = ε := by field_simp

/-- Every output jet has an actual strong L² limit, not merely a bounded
formal jet. Identifying these limits with the weak graph of the multiplier is
the remaining closure obligation (`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densitySymbolTestJet_limit (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) (f : ℕ → carrierInitialTestSpace n)
    (hf : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) < ε)
    (k : ℕ) (hk : k ≤ s) :
    ∃ v : Lp (CarrierParameter [×k]→L[ℝ] ℂ) 2 (carrierMeasure n),
      Tendsto (fun j ↦ testWeightedCarrierJet k (s - k)
        (densitySymbolTestMap hρ hχsmooth hlow (f j))) atTop (𝓝 v) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_densitySymbolTestJet s hρ hcρ hχsmooth hlow hχ f hf k hk)

/-- Forgetting the transverse weight on the zero carrier jet is a contraction
on the shared compact smooth test classes. This retains the original carrier
L² limit in the graph closure (`app:ch_background:eq:bg-density-adjoint`). -/
theorem norm_carrierInitialTestToLp_sub_le_zeroJet (s : ℕ)
    (f g : carrierInitialTestSpace n) :
    ‖carrierInitialTestToLp f - carrierInitialTestToLp g‖ ≤
      ‖testWeightedCarrierJet 0 s f - testWeightedCarrierJet 0 s g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (carrierInitialTestToLp f) (carrierInitialTestToLp g),
    Lp.coeFn_sub (testWeightedCarrierJet 0 s f) (testWeightedCarrierJet 0 s g),
    (carrierInitialTest_memLp f).coeFn_toLp, (carrierInitialTest_memLp g).coeFn_toLp,
    (memLp_weightedCarrierJet_of_compactSupport 0 s f.property.1 f.property.2).coeFn_toLp,
    (memLp_weightedCarrierJet_of_compactSupport 0 s g.property.1 g.property.2).coeFn_toLp]
    with x hsub hjet hf hg hf' hg'
  change (carrierInitialTestToLp f : CarrierVariable n → ℂ) x = f.val x at hf
  change (carrierInitialTestToLp g : CarrierVariable n → ℂ) x = g.val x at hg
  change testWeightedCarrierJet 0 s f x = _ at hf'
  change testWeightedCarrierJet 0 s g x = _ at hg'
  rw [hsub, hjet, Pi.sub_apply, Pi.sub_apply, hf, hg, hf', hg']
  change ‖(f.val - g.val) x‖ ≤
    ‖(weightedCarrierJet 0 s f.val - weightedCarrierJet 0 s g.val) x‖
  rw [← weightedCarrierJet_sub 0 s f.property.1 g.property.1, norm_weightedCarrierJet_zero]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (etaBesselWeight_nonneg _ _)]
  apply le_mul_of_one_le_left (norm_nonneg _)
  simpa [etaBesselWeight] using etaBesselWeight_mono (n := n) (Nat.zero_le s) x

/-- The graph-Cauchy hypothesis alone gives a strong L² limit of the actual
untruncated frequency outputs (`app:ch_background:eq:bg-density-adjoint`). -/
theorem cauchySeq_densitySymbolTestL2 (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) (f : ℕ → carrierInitialTestSpace n)
    (hf : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) < ε) :
    CauchySeq (fun j ↦ carrierInitialTestToLp (densitySymbolTestMap hρ hχsmooth hlow (f j))) := by
  have hc := Metric.cauchySeq_iff.mp
    (cauchySeq_densitySymbolTestJet s hρ hcρ hχsmooth hlow hχ f hf 0 (Nat.zero_le _))
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := hc ε hε
  refine ⟨N, fun p hp q hq ↦ ?_⟩
  simp only [dist_eq_norm, Nat.sub_zero] at hN ⊢
  exact (norm_carrierInitialTestToLp_sub_le_zeroJet s _ _).trans_lt (hN p hp q hq)

/-- Closure constructs an actual L² output and identifies it almost everywhere
with the exact density symbol times the given input. Only an input test
approximation is assumed, never output membership or a multiplier bound
(`app:ch_background:eq:bg-density-adjoint`). -/
theorem exists_densitySymbolTestL2_limit (s : ℕ)
    {ρ : CarrierVariable n → ℂ} {χ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχsmooth : ContDiff ℝ ∞ χ) (hlow : ∀ r ≤ 1, χ r = 0)
    (hχ : ∀ r, |χ r| ≤ 1) (f : ℕ → carrierInitialTestSpace n)
    (hf : ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      mixedCarrierJetNorm (s + 1) ((f p).val - (f q).val) < ε)
    (u : CarrierL2 n) (hu : Tendsto (fun j ↦ carrierInitialTestToLp (f j)) atTop (𝓝 u)) :
    ∃ v : CarrierL2 n,
      Tendsto (fun j ↦ carrierInitialTestToLp (densitySymbolTestMap hρ hχsmooth hlow (f j)))
        atTop (𝓝 v) ∧
      v =ᵐ[carrierMeasure n] fun x ↦ densityFrequencySymbol ρ χ x * u x := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_densitySymbolTestL2 s hρ hcρ hχsmooth hlow hχ f hf)
  refine ⟨v, hv, carrierMultiplier_relation_of_tendsto _ hu hv ?_⟩
  intro j
  filter_upwards [(carrierInitialTest_memLp
    (densitySymbolTestMap hρ hχsmooth hlow (f j))).coeFn_toLp,
    (carrierInitialTest_memLp (f j)).coeFn_toLp] with x hx hy
  change carrierInitialTestToLp (densitySymbolTestMap hρ hχsmooth hlow (f j)) x = _ at hx
  change carrierInitialTestToLp (f j) x = _ at hy
  rw [hx, hy]
  rfl

end JanetCartan.ContinuumAdjoint.DensityMultiplier
