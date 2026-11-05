module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Amplitude
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Phase
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.IntegerBounds

/-!
# The actual single-high quantity for elapsed graph operators

The fixed affine pullback and fixed masks incur no derivative loss. The bound
below is linear in the original amplitude and phase seminorms at the same
order `j`. In particular one can take `j=s+(μ₀+2)` with exactly the fixed shift
used by `IntegerBounds`. Constants precede the varying original primitives;
they are uniform over every primitive low-bounded family, and over elapsed
time on the fixed slab. No operator bound is an input.

Source: `app:ch_regular_base:eq:fio-input` applied to
`app:ch_regular_base:eq:fixed-time-representation`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open PrimitiveProfiles GainOneProfiles
variable {d q : ℕ} {ι : Type*} [Fintype ι]

/-- The same-order single-high bound for the actual elapsed objects, for both
orders zero and minus one. The geometric input is only the fixed normalized
buffered chart inclusion. The original spatial symbol supplies the primitive
seminorm finiteness; the elapsed seminorm estimates are conclusions of the
preceding product and pullback proofs. For the integer consumer use
`j=s+(μ₀+2)`; the substitution adds zero to this shift. -/
theorem exists_elapsed_graph_high_constant
    (z : ι → Point (d + 1)) (δ : ι → ℝ)
    {J U V : Set (TwoTimePoint d)} (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hrad : ∀ R : ℝ, 1 ≤ R → ∀ p ∈ U, (p.1, R • p.2) ∈ V)
    {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hmap : ∀ r ∈ Icc 0 Δ, ∀ i, MapsTo (elapsedPoint r) (Metric.closedBall (z i) (δ i)) J)
    (χout χsource β : Euclidean (d + 1) → ℂ)
    (hχout : ContDiff ℝ ∞ χout) (hχsource : ContDiff ℝ ∞ χsource)
    (hβ : ContDiff ℝ ∞ β) (j : ℕ)
    (hβbound : ∀ i, BoundedNormalizedSeminorm (Metric.closedBall (z i) (δ i)) j (jointMultiplier β)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ o : ℕ, o = 0 ∨ o = 1 →
      ∀ (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q),
      ContDiffOn ℝ ∞ (jointPhase Ψ) U → ContDiffOn ℝ ∞ (jointAmplitude b) V →
      BoundedTwoTimeOrderSeminorm o J j b → ∀ r ∈ Icc 0 Δ,
      normalizedGraphOrderHigh o z δ j (elapsedPhase Ψ r) (elapsedAmplitude b χout χsource β r) ≤
        C * (1 + twoTimeOrderSeminorm o J j b + cNorm J j (jointPhase Ψ)) := by
  classical
  let ca : ℝ := ∑ i, amplitudeMaskConstant (Metric.closedBall (z i) (δ i)) j χout χsource β
  let ct : ℝ := ∑ i, phaseTimeConstant (Metric.closedBall (z i) (δ i)) j Δ
  let m : ℝ := Fintype.card ι
  have hca : 0 ≤ ca := Finset.sum_nonneg fun i _ ↦ amplitudeMaskConstant_nonneg _ _ _ _ _
  have hct : 0 ≤ ct := Finset.sum_nonneg fun i _ ↦ phaseTimeConstant_nonneg _ _ hΔ
  have hm : 0 ≤ m := Nat.cast_nonneg _
  let C := 1 + ca + ct + m
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro o ho Ψ b hΨ hb hbbound r hr
  let a := twoTimeOrderSeminorm o J j b
  let p := cNorm J j (jointPhase Ψ)
  have ha : 0 ≤ a := twoTimeOrderSeminorm_nonneg _ _ _ _
  have hp : 0 ≤ p := cNorm_nonneg _ _ _
  have hphase : (∑ i, cNorm (Metric.closedBall (z i) (δ i)) j
      (fun p : Point (d + 1) ↦ elapsedPhase Ψ r p.1.1 p.2)) ≤ ct + m * p := by
    calc
      _ ≤ ∑ i, (phaseTimeConstant (Metric.closedBall (z i) (δ i)) j Δ + p) :=
        Finset.sum_le_sum fun i _ ↦ cNorm_elapsedPhase_le
          (isCompact_closedBall _ _) hJ hU hJU Ψ hΨ hr (hmap r hr i) j
      _ = _ := by simp [ct, m, Finset.sum_add_distrib]
  have hhigh : normalizedGraphOrderHigh o z δ j (elapsedPhase Ψ r)
      (elapsedAmplitude b χout χsource β r) ≤ 1 + ca * a + (ct + m * p) := by
    rcases ho with rfl | rfl
    · have hb0 : BoundedNormalizedSeminorm J j (jointAmplitude b) := by
        simpa only [BoundedTwoTimeOrderSeminorm, twoTimeOrderField, pow_zero, one_smul,
          BoundedNormalizedSeminorm] using hbbound
      have hamp : (∑ i, normalizedSeminorm (Metric.closedBall (z i) (δ i)) j
          (uncurry (elapsedAmplitude b χout χsource β r))) ≤ ca * a := by
        calc
          _ ≤ ∑ i, amplitudeMaskConstant (Metric.closedBall (z i) (δ i)) j χout χsource β *
              normalizedSeminorm J j (jointAmplitude b) :=
            Finset.sum_le_sum fun i _ ↦ (elapsedAmplitude_normalizedSeminorm_le
              (isCompact_closedBall _ _) hJ hU hJU hrad j r b χout χsource β
              hχout hχsource hβ (hβbound i) hb hb0 (hmap r hr i)).2
          _ = _ := by rw [← Finset.sum_mul]; simp only [a, ca, twoTimeOrderSeminorm_zero]
      simp only [normalizedGraphOrderHigh, ↓reduceIte, normalizedGraphHigh]
      linarith
    · have hamp : (∑ i, orderMinusOneSeminorm (Metric.closedBall (z i) (δ i)) j
          (elapsedAmplitude b χout χsource β r)) ≤ ca * a := by
        calc
          _ ≤ ∑ i, amplitudeMaskConstant (Metric.closedBall (z i) (δ i)) j χout χsource β *
              twoTimeOrderSeminorm 1 J j b :=
            Finset.sum_le_sum fun i _ ↦ (elapsedAmplitude_orderMinusOneSeminorm_le
              (isCompact_closedBall _ _) hJ hU hJU hrad j r b χout χsource β
              hχout hχsource hβ (hβbound i) hb hbbound (hmap r hr i)).2
          _ = _ := (Finset.sum_mul ..).symm
      simp only [normalizedGraphOrderHigh, Nat.one_ne_zero, ↓reduceIte, normalizedGainOneHigh]
      linarith
  have hcaC : ca ≤ C := by dsimp [C]; linarith
  have hctC : 1 + ct ≤ C := by dsimp [C]; linarith
  have hmC : m ≤ C := by dsimp [C]; linarith
  have hma := mul_le_mul_of_nonneg_right hcaC ha
  have hmp := mul_le_mul_of_nonneg_right hmC hp
  apply hhigh.trans
  change 1 + ca * a + (ct + m * p) ≤ C * (1 + a + p)
  nlinarith

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
