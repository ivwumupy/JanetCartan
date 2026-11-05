module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Words
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Tests

/-!
# Strong Fourier estimates from the exact finite weak graph expansion

This is the downstream implication from `app:ch_regular_base:eq:graph-derivative-transfer`
to `app:ch_regular_base:eq:fio-input`. The weak identity is produced by
`WeakTransfer`; the quantitative branch bounds are owed by the parent's
primitive-budget and low-L² assembly. Neither is asserted here for a graph.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv JanetCartan.Pseudodifferential
open scoped SchwartzMap
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

private theorem list_norm_sum_le {ι : Type*} (l : List ι) (f : ι → H) (M : ℝ)
    (h : ∀ p ∈ l, ‖f p‖ ≤ M) : ‖(l.map f).sum‖ ≤ (l.length : ℝ) * M := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖f p‖ + ‖(l.map f).sum‖ := norm_add_le _ _
      _ ≤ M + (l.length : ℝ) * M :=
        add_le_add (h p (by simp)) (ih (fun q hq ↦ h q (by simp [hq])))
      _ = _ := by ring

/-- Positive-order assembly of the exact full-amplitude branch list. Output
Sobolev membership is proved from the weak identity. The only analytic inputs
are that identity and the branch operator norms, whose producers are specified
in the module documentation. Source: `app:ch_regular_base:eq:fio-input`. -/
theorem graph_vector_sobolev_of_expansion_pos (s : ℕ) (hs : 0 < s)
    (C : ℝ) (hC : 0 ≤ C)
    (R : Fin n → FullAmplitude n r → FullAmplitude n r)
    (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
    (A : FullAmplitude n r) (T : FullAmplitude n r → H →L[ℂ] H)
    (Hhigh : ℝ) (hH : 0 ≤ Hhigh) (u : graphTestSpace n r) (w : H)
    (hw : ∀ is, is.length ≤ s →
      orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (w : 𝓢'(E, V)) =
      ((fullAmplitudeDerivativeTerms R P A is).map fun p ↦
        (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
          𝓢'(E, V))).sum)
    (hb : ∀ is, is.length ≤ s → ∀ p ∈ fullAmplitudeDerivativeTerms R P A is,
      ‖T p.1‖ ≤ C * Hhigh ^ (((s : ℝ) - p.2.length) / s)) :
    MemVectorFourierSobolev (s : ℝ) w ∧
      vectorFourierSobolevNorm (s : ℝ) w ≤
        ((r : ℝ) * (n + 1 : ℝ) ^ s) *
          ((n + 1 : ℝ) ^ s * C * ((r : ℝ) * (2 * Real.pi) ^ s)) *
            (vectorFourierSobolevNorm (s : ℝ) (graphTestToLp u) +
              Hhigh * ‖graphTestToLp u‖) := by
  let B := vectorFourierSobolevNorm (s : ℝ) (graphTestToLp u) + Hhigh * ‖graphTestToLp u‖
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (mul_nonneg hH (norm_nonneg _))
  let v := fun is ↦ ((fullAmplitudeDerivativeTerms R P A is).map fun p ↦
    T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u))).sum
  have hword (is : List (Fin n)) (hi : is.length ≤ s) :
      ‖v is‖ ≤ ((n + 1 : ℝ) ^ s * C * ((r : ℝ) * (2 * Real.pi) ^ s)) * B := by
    have hterm (p) (hp : p ∈ fullAmplitudeDerivativeTerms R P A is) :
        ‖T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u))‖ ≤
          C * (((r : ℝ) * (2 * Real.pi) ^ s) * B) := by
      have hk := (fullAmplitudeDerivativeTerms_datum_length_le R P A is p hp).trans hi
      have he : ((s : ℝ) - p.2.length) / s = 1 - (p.2.length : ℝ) / s := by
        rw [sub_div, div_self (by exact_mod_cast (Nat.ne_of_gt hs))]
      calc
        _ ≤ ‖T p.1‖ * ‖graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)‖ :=
          (T p.1).le_opNorm _
        _ ≤ (C * Hhigh ^ (1 - (p.2.length : ℝ) / s)) *
            ‖graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)‖ :=
          mul_le_mul_of_nonneg_right (by simpa only [he] using hb is hi p hp) (norm_nonneg _)
        _ ≤ _ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (graphTest_weighted_word_bound s u p.2 hk Hhigh hH) hC
    calc
      _ ≤ ((fullAmplitudeDerivativeTerms R P A is).length : ℝ) *
          (C * (((r : ℝ) * (2 * Real.pi) ^ s) * B)) := list_norm_sum_le _ _ _ hterm
      _ ≤ (n + 1 : ℝ) ^ s * (C * (((r : ℝ) * (2 * Real.pi) ^ s) * B)) := by
        rw [fullAmplitudeDerivativeTerms_length, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) hi)
          (mul_nonneg hC (mul_nonneg (by positivity) hB))
      _ = _ := by ring
  have hweak (is) (hi : is.length ≤ s) :
      orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (w : 𝓢'(E, V)) = (v is : 𝓢'(E, V)) := by
    rw [hw is hi]
    change _ = (Lp.toTemperedDistributionCLM V volume 2) _
    rw [map_list_sum]
    simp only [List.map_map, Function.comp_def, Lp.toTemperedDistributionCLM_apply]
  simpa only [mul_assoc, B] using graph_vector_sobolev_of_weak_words s w v
    (((n + 1 : ℝ) ^ s * C * ((r : ℝ) * (2 * Real.pi) ^ s)) * B) hweak hword

/-- Uniform tame constant, quantified before the high majorant and datum, for
`app:ch_regular_base:eq:fio-input`. The exact branch exponent is `(s-k)/s`;
order zero is handled directly by the low operator bound. This is conditional
Fourier assembly, not the graph theorem or an analytic producer. -/
theorem exists_graph_vector_sobolev_expansion_constant (s : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (R : Fin n → FullAmplitude n r → FullAmplitude n r)
        (P : Fin n → Fin n → FullAmplitude n r → FullAmplitude n r)
        (A : FullAmplitude n r) (T : FullAmplitude n r → H →L[ℂ] H)
        (Hhigh : ℝ), 0 ≤ Hhigh → ∀ (u : graphTestSpace n r) (w : H),
      (∀ is, is.length ≤ s →
        orderedTransferAction (fun i ↦ lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
          (w : 𝓢'(E, V)) =
        ((fullAmplitudeDerivativeTerms R P A is).map fun p ↦
          (T p.1 (graphTestToLp (orderedTransferAction graphTestPartialDeriv p.2 u)) :
            𝓢'(E, V))).sum) →
      (∀ is, is.length ≤ s → ∀ p ∈ fullAmplitudeDerivativeTerms R P A is,
        ‖T p.1‖ ≤ C * Hhigh ^ (((s : ℝ) - p.2.length) / s)) →
      MemVectorFourierSobolev (s : ℝ) w ∧
        vectorFourierSobolevNorm (s : ℝ) w ≤ K *
          (vectorFourierSobolevNorm (s : ℝ) (graphTestToLp u) + Hhigh * ‖graphTestToLp u‖) := by
  by_cases hs : s = 0
  · subst s
    refine ⟨1 + (r : ℝ) * C, by positivity, ?_⟩
    intro R P A T Hhigh hH u w hw hb
    have hTA : ‖T A‖ ≤ C := by
      simpa using hb [] (by simp) (A, []) (by simp [fullAmplitudeDerivativeTerms])
    have hz := graph_vector_sobolev_of_weak_words 0 w (fun _ ↦ T A (graphTestToLp u))
      (C * ‖graphTestToLp u‖)
      (fun is hi ↦ by
        have he : is = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hi)
        subst is
        simpa [fullAmplitudeDerivativeTerms, orderedTransferAction] using hw [] (by simp))
      (fun _ _ ↦ ((T A).le_opNorm _).trans (mul_le_mul_of_nonneg_right hTA (norm_nonneg _)))
    refine ⟨hz.1, ?_⟩
    simp only [Nat.cast_zero, pow_zero, mul_one] at hz ⊢
    simp only [vectorFourierSobolevNorm_zero] at hz ⊢
    nlinarith [norm_nonneg (graphTestToLp u), mul_nonneg hH (norm_nonneg (graphTestToLp u)),
      mul_nonneg (mul_nonneg (Nat.cast_nonneg r) hC) (mul_nonneg hH (norm_nonneg (graphTestToLp u)))]
  · let K := ((r : ℝ) * (n + 1 : ℝ) ^ s) *
        ((n + 1 : ℝ) ^ s * C * ((r : ℝ) * (2 * Real.pi) ^ s))
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨1 + K, by positivity, ?_⟩
    intro R P A T Hhigh hH u w hw hb
    have h := graph_vector_sobolev_of_expansion_pos s (Nat.pos_of_ne_zero hs)
      C hC R P A T Hhigh hH u w hw hb
    refine ⟨h.1, h.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith)
      (add_nonneg (norm_nonneg _) (mul_nonneg hH (norm_nonneg _)))

end JanetCartan.FourierIntegral
