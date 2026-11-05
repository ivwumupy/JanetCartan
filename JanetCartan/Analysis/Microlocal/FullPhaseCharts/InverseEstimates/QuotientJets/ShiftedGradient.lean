module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Carrier

/-!
# One-high shifted covector gradient

The inner composition in `app:ch_seed:eq:seed-quotient-integral` is bounded
from primitive joint phase and carrier jets. The derivative of the phase costs
one order. No high carrier norm is hidden in the uniform constant.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The shifted gradient has an additive one-high joint bound from phase jets
through `n+1` and carrier jets through `n`. The fixed low inputs are phase `C²`
and carrier `C¹`. The consumer is the covector integrand estimate in
`app:ch_seed:eq:seed-quotient-integral`. -/
theorem exists_cNorm_shiftedGradient_le_oneHigh
    (a : (P × ℝ) × X) (b : (P × X) × E) {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    {V : Set P} {I : Set ℝ} {U : Set X} {C : Set E}
    (hV : IsOpen V) (hI : IsOpen I) (hU : IsOpen U) (hC : IsOpen C)
    (ha : Metric.closedBall a ρ ⊆ (V ×ˢ I) ×ˢ U)
    (hp : Metric.closedBall a.1.1 ρ ⊆ V)
    (hb : Metric.closedBall b σ ⊆ (V ×ˢ U) ×ˢ C)
    {n : ℕ} (hn : 2 ≤ n) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ D > (0 : ℝ), ∀ (S : (P × X) → E → ℝ) (z v : P → E),
      ContDiffOn ℝ ∞ (Function.uncurry S) ((V ×ˢ U) ×ˢ C) →
      ContDiffOn ℝ ∞ z V → ContDiffOn ℝ ∞ v V →
      cNorm (Metric.closedBall b σ) 2 (Function.uncurry S) ≤ N →
      cNorm (Metric.closedBall a.1.1 ρ) 1 z ≤ M →
      cNorm (Metric.closedBall a.1.1 ρ) 1 v ≤ M →
      ∀ t ∈ Icc (0 : ℝ) 1,
      MapsTo (carrierSubstitution z v t) (Metric.closedBall a ρ) (Metric.closedBall b σ) →
      cNorm (Metric.closedBall a ρ) n (fun q : (P × ℝ) × X ↦
        gradient (S (q.1.1, q.2)) (z q.1.1 + (t * q.1.2) • v q.1.1)) ≤
        D * (1 + cNorm (Metric.closedBall b σ) (n + 1) (Function.uncurry S) +
          cNorm (Metric.closedBall a.1.1 ρ) n z + cNorm (Metric.closedBall a.1.1 ρ) n v) := by
  let K := Metric.closedBall a ρ
  let J := Metric.closedBall a.1.1 ρ
  let L := Metric.closedBall b σ
  obtain ⟨D₁, hD₁, hd₁⟩ := exists_cNorm_carrierSubstitution_le (E := E) a ρ hV hI hU ha hp 1
  obtain ⟨Dₙ, hDₙ, hdₙ⟩ := exists_cNorm_carrierSubstitution_le (E := E) a ρ hV hI hU ha hp n
  obtain ⟨A, hA, hcomp⟩ := exists_cNorm_comp_le_additive_oneHigh (F := E)
    a b hρ hσ ((hV.prod hI).prod hU) ((hV.prod hU).prod hC) ha hb hn
    (mul_nonneg hD₁.le (by positivity : 0 ≤ 1 + M + M)) hN
  refine ⟨A * (1 + Dₙ), by positivity, ?_⟩
  intro S z v hS hz hv hSN hzM hvM t ht hmap
  let G : ((P × X) × E) → E := fun w ↦ gradient (S w.1) w.2
  have hG : ContDiffOn ℝ ∞ G ((V ×ˢ U) ×ˢ C) :=
    contDiffOn_phaseGradient (hV.prod hU) hC hS
  have hg j := cNorm_jointPhaseGradient_le (hV.prod hU) hC hS
    (isCompact_closedBall b σ) hb j
  have hf₁ : cNorm K 1 (carrierSubstitution z v t) ≤ D₁ * (1 + M + M) :=
    (hd₁ z v hz hv t ht).trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add le_rfl hzM) hvM) hD₁.le)
  have h := hcomp (carrierSubstitution z v t) G
    (contDiffOn_carrierSubstitution hz hv t) hG hmap hf₁ ((hg 1).trans hSN)
  apply h.trans
  have hf := hdₙ z v hz hv t ht
  have hgg := hg n
  have hs0 := cNorm_nonneg L (n + 1) (Function.uncurry S)
  have hz0 := cNorm_nonneg J n z
  have hv0 := cNorm_nonneg J n v
  change A * (1 + cNorm K n (carrierSubstitution z v t) + cNorm L n G) ≤
    A * (1 + Dₙ) * (1 + cNorm L (n + 1) (Function.uncurry S) + cNorm J n z + cNorm J n v)
  apply (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hf) hgg) hA.le).trans
  change A * (1 + Dₙ * (1 + cNorm J n z + cNorm J n v) +
    cNorm L (n + 1) (Function.uncurry S)) ≤ _
  nlinarith [mul_nonneg hDₙ.le hs0]

end JanetCartan.FullPhaseCharts.InverseEstimates
