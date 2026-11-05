module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Averaging
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Integral
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.Quotient

/-!
# Quantitative ingredients for the exact forward quotient chart

For `app:ch_seed:eq:seed-quotient-integral` and the final paragraph of
`app:ch_seed:prop:seed-phase-charts`, this module provides:

* exact all-order joint differentiation under the literal quotient integral;
* one-derivative physical averaging, on fixed buffered domains;
* additive one-high composition from proved interpolation on closed balls.

The final theorem assembles both actual integrals into an additive one-high
bound from primitive joint phase and carrier jets. The phase/carrier construction
and its bounds in terms of the original coefficient remain parent obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.InverseEstimates

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- The actual physical averaging operator has a joint `C^k` bound from
phase `C^(k+1)` on any fixed compact set containing the integration segments.
Only smoothness, rather than a quantitative bound, is required on the open
enlargements. This supplies the outer integration step for the quotient phase
in `app:ch_seed:prop:seed-phase-charts`. -/
theorem cNorm_averagedPhaseGradient_joint_le
    {S : P → X → ℝ} {V : Set P} {U B : Set X} {T : Set ℝ}
    {K : Set (P × X × X)} {L : Set (P × X)}
    (hV : IsOpen V) (hU : IsOpen U) (hB : IsOpen B)
    (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (V ×ˢ U))
    (hphysical : ∀ x ∈ B, ∀ y ∈ B, ∀ t ∈ T, y + t • (x - y) ∈ U)
    (hK : K ⊆ V ×ˢ B ×ˢ B) (hL : IsCompact L) (hLU : L ⊆ V ×ˢ U)
    (hsegments : ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, jointPhysicalSegment t q ∈ L)
    (k : ℕ) :
    cNorm K k (fun q : P × X × X ↦ averagedPhaseGradient S q.1 q.2.1 q.2.2) ≤
      (∑ j ∈ Finset.range (k + 1), (3 : ℝ) ^ j) *
        cNorm L (k + 1) (Function.uncurry S) := by
  let H : (P × X × X) × ℝ → X := fun w ↦
    gradient (S w.1.1) (w.1.2.2 + w.2 • (w.1.2.1 - w.1.2.2))
  have hH : ContDiffOn ℝ ∞ H ((V ×ˢ B ×ˢ B) ×ˢ T) :=
    contDiffOn_averagedPhaseIntegrand hV hU hS contDiffOn_fst
      contDiffOn_snd.fst contDiffOn_snd.snd
      (fun q hq t ht ↦ ⟨hq.1, hphysical _ hq.2.1 _ hq.2.2 t ht⟩)
  have hlocal (q) (hq : q ∈ L) : ContDiffAt ℝ (k + 1) (Function.uncurry S) q :=
    (hS.contDiffAt ((hV.prod hU).mem_nhds (hLU hq))).of_le (by simp)
  have hb : ∀ j ≤ k, ∀ q ∈ K,
      ‖iteratedFDeriv ℝ j (fun q : P × X × X ↦
        averagedPhaseGradient S q.1 q.2.1 q.2.2) q‖ ≤
        3 ^ j * cNorm L (k + 1) (Function.uncurry S) := by
    intro j hj q hq
    apply norm_iteratedFDeriv_unitIntervalParameterIntegral_le
      (g := H) (hV.prod (hB.prod hB)) hT hIT hH (hK hq) j
    intro t ht
    have hm := hsegments q hq t ht
    exact (norm_iteratedFDeriv_physicalSegmentGradient_le hV hU hS ht (hLU hm) j).trans
      (mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (r := k + 1) hL hlocal hm
          (Nat.add_le_add_right hj 1))
        (by positivity))
  simpa only [Finset.sum_mul] using
    cNorm_le_sum_of_bounds
      (fun j _ ↦ mul_nonneg (by positivity) (cNorm_nonneg L (k + 1) (Function.uncurry S))) hb

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Joint one-high forward-chart estimate for the literal quotient and physical
average of `app:ch_seed:eq:seed-quotient-integral` and the final paragraph of
`app:ch_seed:prop:seed-phase-charts`.

The constant is chosen before the phase and both carriers. Fixed low inputs are
phase `C³` and carrier `C²`; the high part contains only phase and carrier norms
through `k+2`. Both integration segments have explicit buffered containment.
Epsilon is a joint variable on the open set `I`, which contains zero. The
arbitrary parameter space `P` retains time and `z₁` for transverse charts.
No inverse estimate or high quotient estimate is a hypothesis. -/
theorem exists_cNorm_carrierQuotient_average_le_oneHigh
    (a : (P × ℝ) × X) (b : (P × X) × E) (d : (P × ℝ) × X × X)
    {ρ σ τ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (_hτ : 0 < τ)
    {V : Set P} {I W T : Set ℝ} {U B : Set X} {C : Set E}
    (hV : IsOpen V) (hI : IsOpen I) (_hzero : (0 : ℝ) ∈ I)
    (hU : IsOpen U) (hC : IsOpen C) (hB : IsOpen B)
    (hW : IsOpen W) (hIW : Icc (0 : ℝ) 1 ⊆ W)
    (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (ha : Metric.closedBall a ρ ⊆ (V ×ˢ I) ×ˢ U)
    (hp : Metric.closedBall a.1.1 ρ ⊆ V)
    (hb : Metric.closedBall b σ ⊆ (V ×ˢ U) ×ˢ C)
    (hd : Metric.closedBall d τ ⊆ (V ×ˢ I) ×ˢ B ×ˢ B)
    (hphysical : ∀ x ∈ B, ∀ y ∈ B, ∀ t ∈ T, y + t • (x - y) ∈ U)
    (hsegments : ∀ q ∈ Metric.closedBall d τ, ∀ t ∈ Icc (0 : ℝ) 1,
      jointPhysicalSegment t q ∈ Metric.closedBall a ρ)
    (k : ℕ) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ D > (0 : ℝ), ∀ (S : (P × X) → E → ℝ) (z v : P → E),
      ContDiffOn ℝ ∞ (Function.uncurry S) ((V ×ˢ U) ×ˢ C) →
      ContDiffOn ℝ ∞ z V → ContDiffOn ℝ ∞ v V →
      cNorm (Metric.closedBall b σ) 3 (Function.uncurry S) ≤ N →
      cNorm (Metric.closedBall a.1.1 ρ) 2 z ≤ M →
      cNorm (Metric.closedBall a.1.1 ρ) 2 v ≤ M →
      (∀ p ∈ V, ∀ ε ∈ I, ∀ t ∈ W, z p + (t * ε) • v p ∈ C) →
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (carrierSubstitution z v t)
        (Metric.closedBall a ρ) (Metric.closedBall b σ)) →
      cNorm (Metric.closedBall d τ) k (fun q : (P × ℝ) × X × X ↦
        averagedPhaseGradient (fun p x ↦
          phaseShiftQuotient S (p.1, x) (z p.1) (v p.1) p.2) q.1 q.2.1 q.2.2) ≤
        D * (1 + cNorm (Metric.closedBall b σ) (k + 2) (Function.uncurry S) +
          cNorm (Metric.closedBall a.1.1 ρ) (k + 2) z +
          cNorm (Metric.closedBall a.1.1 ρ) (k + 2) v) := by
  let n := max 2 (k + 1)
  have hn : 2 ≤ n := le_max_left _ _
  obtain ⟨D, hD, hquot⟩ := exists_cNorm_carrierQuotient_le_oneHigh
    a b hρ hσ hV hI hU hC hW hIW ha hp hb hn hM hN
  let A := ∑ j ∈ Finset.range (k + 1), (3 : ℝ) ^ j
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ ↦ by positivity)
  refine ⟨(1 + A) * D * (1 + N), by positivity, ?_⟩
  intro S z v hS hz hv hSN hzM hvM hshift hmap
  let Φ : (P × ℝ) → X → ℝ := fun p x ↦
    phaseShiftQuotient S (p.1, x) (z p.1) (v p.1) p.2
  have hΦ : ContDiffOn ℝ ∞ (Function.uncurry Φ) ((V ×ˢ I) ×ˢ U) :=
    contDiffOn_carrierQuotient hV hU hC hI hW hIW hS hz hv hshift
  have haverage := cNorm_averagedPhaseGradient_joint_le (hV.prod hI) hU hB hT hIT
    hΦ hphysical hd (isCompact_closedBall a ρ) ha hsegments k
  have hq := hquot S z v hS hz hv hSN hzM hvM hshift hmap
  let H := 1 + cNorm (Metric.closedBall b σ) (k + 2) (Function.uncurry S) +
    cNorm (Metric.closedBall a.1.1 ρ) (k + 2) z +
    cNorm (Metric.closedBall a.1.1 ρ) (k + 2) v
  have hs0 := cNorm_nonneg (Metric.closedBall b σ) (k + 2) (Function.uncurry S)
  have hz0 := cNorm_nonneg (Metric.closedBall a.1.1 ρ) (k + 2) z
  have hv0 := cNorm_nonneg (Metric.closedBall a.1.1 ρ) (k + 2) v
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hphase : cNorm (Metric.closedBall b σ) (n + 1) (Function.uncurry S) ≤
      N + cNorm (Metric.closedBall b σ) (k + 2) (Function.uncurry S) := by
    by_cases hk : k = 0
    · subst k
      change cNorm (Metric.closedBall b σ) 3 (Function.uncurry S) ≤ _
      linarith
    · have he : n + 1 = k + 2 := by dsimp [n]; omega
      rw [he]
      linarith
  have hn' : n ≤ k + 2 := by dsimp [n]; omega
  have hcarrierz := cNorm_mono_order (f := z) (s := Metric.closedBall a.1.1 ρ) hn'
  have hcarrierv := cNorm_mono_order (f := v) (s := Metric.closedBall a.1.1 ρ) hn'
  have hhigh : 1 + cNorm (Metric.closedBall b σ) (n + 1) (Function.uncurry S) +
      cNorm (Metric.closedBall a.1.1 ρ) n z + cNorm (Metric.closedBall a.1.1 ρ) n v ≤
      (1 + N) * H := by
    dsimp [H]
    nlinarith [mul_nonneg hN hs0, mul_nonneg hN hz0, mul_nonneg hN hv0]
  have hq' : cNorm (Metric.closedBall a ρ) (k + 1) (Function.uncurry Φ) ≤
      D * ((1 + N) * H) :=
    (cNorm_mono_order (le_max_right 2 (k + 1))).trans
      (hq.trans (mul_le_mul_of_nonneg_left hhigh hD.le))
  apply haverage.trans
  apply (mul_le_mul_of_nonneg_left hq' hA).trans
  change A * (D * ((1 + N) * H)) ≤ (1 + A) * D * (1 + N) * H
  have hpos : 0 ≤ D * (1 + N) * H := by positivity
  nlinarith

end JanetCartan.FullPhaseCharts.InverseEstimates
