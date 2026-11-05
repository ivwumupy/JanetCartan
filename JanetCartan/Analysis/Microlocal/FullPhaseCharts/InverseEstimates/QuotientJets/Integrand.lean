module

public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.ShiftedGradient

/-!
# Primitive one-high bound for the actual covector integrand

For `app:ch_seed:eq:seed-quotient-integral`, the varying gradient and direction
are combined using the proved additive tame product. The fixed low inputs are
phase `C³` and carrier `C²`. The consumer is the quotient integration step.
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

/-- The literal quotient integrand has a joint additive one-high bound. The
constant is fixed before `S,z,v,t`; only phase jets through `n+1` and carrier
jets through `n` appear in its high part. This is the quantitative input to the
actual integral in `app:ch_seed:eq:seed-quotient-integral`. -/
theorem exists_cNorm_carrierIntegrand_le_oneHigh
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
      cNorm (Metric.closedBall b σ) 3 (Function.uncurry S) ≤ N →
      cNorm (Metric.closedBall a.1.1 ρ) 2 z ≤ M →
      cNorm (Metric.closedBall a.1.1 ρ) 2 v ≤ M →
      ∀ t ∈ Icc (0 : ℝ) 1,
      (∀ p ∈ V, ∀ ε ∈ I, z p + (t * ε) • v p ∈ C) →
      MapsTo (carrierSubstitution z v t) (Metric.closedBall a ρ) (Metric.closedBall b σ) →
      cNorm (Metric.closedBall a ρ) n (fun q : (P × ℝ) × X ↦
        inner ℝ (gradient (S (q.1.1, q.2))
          (z q.1.1 + (t * q.1.2) • v q.1.1)) (v q.1.1)) ≤
        D * (1 + cNorm (Metric.closedBall b σ) (n + 1) (Function.uncurry S) +
          cNorm (Metric.closedBall a.1.1 ρ) n z + cNorm (Metric.closedBall a.1.1 ρ) n v) := by
  let K := Metric.closedBall a ρ
  let J := Metric.closedBall a.1.1 ρ
  let L := Metric.closedBall b σ
  let Q := (V ×ˢ I) ×ˢ U
  obtain ⟨A₂, hA₂, ha₂⟩ := exists_cNorm_shiftedGradient_le_oneHigh
    a b hρ hσ hV hI hU hC ha hp hb (n := 2) le_rfl hM hN
  obtain ⟨Aₙ, hAₙ, haₙ⟩ := exists_cNorm_shiftedGradient_le_oneHigh
    a b hρ hσ hV hI hU hC ha hp hb hn hM hN
  let R := A₂ * (1 + N + M + M)
  have hR : 0 ≤ R := mul_nonneg hA₂.le (by positivity)
  obtain ⟨B, hB, hbil⟩ := exists_cNorm_bilinear_le_additive_oneHigh
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) a hρ ((hV.prod hI).prod hU) ha hn
    hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
  refine ⟨B * (1 + Aₙ + (n + 1)), by positivity, ?_⟩
  intro S z v hS hz hv hSN hzM hvM t ht hshift hmap
  let g : ((P × ℝ) × X) → E := fun q ↦
    gradient (S (q.1.1, q.2)) (z q.1.1 + (t * q.1.2) • v q.1.1)
  have hg : ContDiffOn ℝ ∞ g Q :=
    (contDiffOn_phaseGradient (hV.prod hU) hC hS).comp
      (contDiffOn_carrierSubstitution hz hv t)
      (fun q hq ↦ ⟨⟨hq.1.1, hq.2⟩, hshift q.1.1 hq.1.1 q.1.2 hq.1.2⟩)
  have hvQ : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × X ↦ v q.1.1) Q :=
    hv.comp contDiffOn_fst.fst (fun _ h ↦ h.1.1)
  have hSN₂ := (cNorm_mono_order (f := Function.uncurry S) (s := L) (by omega : 2 ≤ 3)).trans hSN
  have hzM₁ := (cNorm_mono_order (f := z) (s := J) (by omega : 1 ≤ 2)).trans hzM
  have hvM₁ := (cNorm_mono_order (f := v) (s := J) (by omega : 1 ≤ 2)).trans hvM
  have hg₂ := ha₂ S z v hS hz hv hSN₂ hzM₁ hvM₁ t ht hmap
  have hg₁ : cNorm K 1 g ≤ R :=
    (cNorm_mono_order (by omega : 1 ≤ 2)).trans (hg₂.trans
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add le_rfl hSN) hzM) hvM) hA₂.le))
  have hv₁ : cNorm K 1 (fun q : (P × ℝ) × X ↦ v q.1.1) ≤ 2 * M := by
    have hh := cNorm_carrierLift_le a ρ hV hp hv 1
    norm_num only [Nat.cast_one, one_add_one_eq_two] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hvM₁ (by norm_num))
  have h := hbil g (fun q ↦ v q.1.1) hg hvQ hg₁ hv₁
  apply h.trans
  have hgn := haₙ S z v hS hz hv hSN₂ hzM₁ hvM₁ t ht hmap
  have hvn := cNorm_carrierLift_le a ρ hV hp hv n
  apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hgn) hvn) hB.le).trans
  change B * (1 + Aₙ * (1 + cNorm L (n + 1) (Function.uncurry S) + cNorm J n z + cNorm J n v) +
    (n + 1) * cNorm J n v) ≤
    B * (1 + Aₙ + (n + 1)) *
      (1 + cNorm L (n + 1) (Function.uncurry S) + cNorm J n z + cNorm J n v)
  have hs0 := cNorm_nonneg L (n + 1) (Function.uncurry S)
  have hz0 := cNorm_nonneg J n z
  have hv0 := cNorm_nonneg J n v
  have hn0 : (0 : ℝ) ≤ n + 1 := by positivity
  nlinarith [mul_nonneg hn0 hs0, mul_nonneg hn0 hz0]

end JanetCartan.FullPhaseCharts.InverseEstimates
