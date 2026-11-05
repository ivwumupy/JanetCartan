module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Integrand
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Integral

/-!
# One-high bound for the literal integral quotient

The actual covector integral in `app:ch_seed:eq:seed-quotient-integral`
introduces no further derivative loss, including at epsilon zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A primitive one-high bound for the exact quotient, joint in the carrier,
physical and epsilon variables on an open extension. The constant precedes all
varying maps. Source: `app:ch_seed:eq:seed-quotient-integral`. -/
theorem exists_cNorm_carrierQuotient_le_oneHigh
    (a : (P × ℝ) × X) (b : (P × X) × E) {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    {V : Set P} {I W : Set ℝ} {U : Set X} {C : Set E}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U) (hC : IsOpen C)
    (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (ha : Metric.closedBall a ρ ⊆ (V ×ˢ I) ×ˢ U)
    (hp : Metric.closedBall a.1.1 ρ ⊆ V)
    (hb : Metric.closedBall b σ ⊆ (V ×ˢ U) ×ˢ C)
    {n : ℕ} (hn : 2 ≤ n) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ D > (0 : ℝ), ∀ (S : (P × X) → E → ℝ) (z v : P → E),
      ContDiffOn ℝ ∞ (Function.uncurry S) ((V ×ˢ U) ×ˢ C) →
      ContDiffOn ℝ ∞ z V → ContDiffOn ℝ ∞ v V →
      cNorm (Metric.closedBall b σ) 3 (Function.uncurry S) ≤ N →
      cNorm (Metric.closedBall a.1.1 ρ) 2 z ≤ M →
      cNorm (Metric.closedBall a.1.1 ρ) 2 v ≤ M →
      (∀ p ∈ V, ∀ ε ∈ I, ∀ t ∈ W, z p + (t * ε) • v p ∈ C) →
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (carrierSubstitution z v t)
        (Metric.closedBall a ρ) (Metric.closedBall b σ)) →
      cNorm (Metric.closedBall a ρ) n (fun q : (P × ℝ) × X ↦
        phaseShiftQuotient S (q.1.1, q.2) (z q.1.1) (v q.1.1) q.1.2) ≤
        D * (1 + cNorm (Metric.closedBall b σ) (n + 1) (Function.uncurry S) +
          cNorm (Metric.closedBall a.1.1 ρ) n z + cNorm (Metric.closedBall a.1.1 ρ) n v) := by
  obtain ⟨D, hD, hd⟩ := exists_cNorm_carrierIntegrand_le_oneHigh
    a b hρ hσ hV hI hU hC ha hp hb hn hM hN
  refine ⟨(n + 1) * D, mul_pos (by positivity) hD, ?_⟩
  intro S z v hS hz hv hSN hzM hvM hshift hmap
  let K := Metric.closedBall a ρ
  let H := 1 + cNorm (Metric.closedBall b σ) (n + 1) (Function.uncurry S) +
    cNorm (Metric.closedBall a.1.1 ρ) n z + cNorm (Metric.closedBall a.1.1 ρ) n v
  have hH : 0 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (Metric.closedBall b σ) (n + 1) (Function.uncurry S),
      cNorm_nonneg (Metric.closedBall a.1.1 ρ) n z,
      cNorm_nonneg (Metric.closedBall a.1.1 ρ) n v]
  let f : ℝ → ((P × ℝ) × X) → ℝ := fun t q ↦
    inner ℝ (gradient (S (q.1.1, q.2))
      (z q.1.1 + (t * q.1.2) • v q.1.1)) (v q.1.1)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffOn ℝ ∞ (f t) ((V ×ˢ I) ×ˢ U) := by
    have hg := (contDiffOn_phaseGradient (hV.prod hU) hC hS).comp
      (contDiffOn_carrierSubstitution hz hv t)
      (fun q hq ↦ ⟨⟨hq.1.1, hq.2⟩, hshift q.1.1 hq.1.1 q.1.2 hq.1.2 t (hIW ht)⟩)
    exact hg.inner ℝ (hv.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1))
  have hj : ∀ j ≤ n, ∀ q ∈ K,
      ‖iteratedFDeriv ℝ j (fun q : (P × ℝ) × X ↦
        phaseShiftQuotient S (q.1.1, q.2) (z q.1.1) (v q.1.1) q.1.2) q‖ ≤ D * H := by
    intro j hj q hq
    rw [iteratedFDeriv_carrierQuotient hV hU hC hI hW hIW hS hz hv hshift (ha hq) j]
    apply (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := D * H) ?_).trans_eq
    · simp
    · intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using uIoc_subset_uIcc ht
      exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
        (fun y hy ↦ ((hf t ht').contDiffAt (((hV.prod hI).prod hU).mem_nhds (ha hy))).of_le
          (by simp)) hq hj).trans
        (hd S z v hS hz hv hSN hzM hvM t ht'
          (fun p hp ε hε ↦ hshift p hp ε hε t (hIW ht')) (hmap t ht'))
  have h := cNorm_le_sum_of_bounds (fun _ _ ↦ mul_nonneg hD.le hH) hj
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one, mul_assoc] using h

end JanetCartan.FullPhaseCharts.InverseEstimates
