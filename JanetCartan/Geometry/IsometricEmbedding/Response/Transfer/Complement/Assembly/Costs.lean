module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope

import Mathlib.Tactic.Positivity

/-!
# Fixed polynomial costs in complementary estimates

The fixed carrier, demodulation and parameter-jet losses in
`app:ch_response:thm:response-literal-transfer`. These lemmas are consumed by
`completeComplement_observations`; none postulates arbitrary accuracy for an
actual kernel. Finite parameter differentiation is used through its exact
finite Leibniz expansion, with frequency and actual operators held fixed.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer.Complement

open ArbitraryAccuracy Finset

variable {ι E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Compose the fixed Sobolev costs of a carrier and a full factor, or of a full
factor and a demodulator (`app:ch_response:thm:response-literal-transfer`).
In particular the input cost to `completeComplement_rapidDecay` can be derived
from separate estimates of the actual maps. -/
theorem polynomialCost_comp
    (G : GradedScale E) (H : GradedScale F) (J : GradedScale V)
    (T : E →ₗ[ℝ] F) (P : F →ₗ[ℝ] V) (t r s : ℕ) (ρ C D a b : ℝ)
    (hρ : 0 < ρ) (hD : 0 ≤ D)
    (hT : ∀ v, v ∈ G.level t → T v ∈ H.level r ∧
      H.gradeNorm r (T v) ≤ C * ρ ^ a * G.gradeNorm t v)
    (hP : ∀ v, v ∈ H.level r → P v ∈ J.level s ∧
      J.gradeNorm s (P v) ≤ D * ρ ^ b * H.gradeNorm r v) :
    ∀ v, v ∈ G.level t → (P.comp T) v ∈ J.level s ∧
      J.gradeNorm s ((P.comp T) v) ≤ (D * C) * ρ ^ (a + b) * G.gradeNorm t v := by
  intro v hv
  obtain ⟨hm, hb⟩ := hT v hv
  obtain ⟨hpm, hpb⟩ := hP (T v) hm
  refine ⟨hpm, hpb.trans ?_⟩
  calc
    _ ≤ D * ρ ^ b * (C * ρ ^ a * G.gradeNorm t v) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hD (Real.rpow_nonneg hρ.le _))
    _ = _ := by rw [Real.rpow_add hρ]; ring

/-- Absorb a fixed polynomial observation cost by choosing greater internal
precision (`app:ch_response:thm:response-literal-transfer`). Membership is
preserved explicitly. -/
theorem rapidDecayAt_polynomial_observation
    (G : GradedScale E) (H : GradedScale F) (f : ι → E) (g : ι → F)
    (ρ A : ι → ℝ) (t s : ℕ) (D d : ℝ)
    (hρ : ∀ i, 0 < ρ i) (hD : 0 ≤ D)
    (hf : RapidDecayAt G t ρ A f)
    (hg : ∀ i, f i ∈ G.level t → g i ∈ H.level s ∧
      H.gradeNorm s (g i) ≤ D * (ρ i) ^ d * G.gradeNorm t (f i)) :
    RapidDecayAt H s ρ A g := by
  intro Q
  obtain ⟨C, hC, hb⟩ := hf (Q + d)
  refine ⟨D * C, mul_nonneg hD hC, ?_⟩
  intro i
  obtain ⟨hm, hbound⟩ := hg i (hb i).1
  refine ⟨hm, hbound.trans ?_⟩
  calc
    _ ≤ D * (ρ i) ^ d * (C * A i * (ρ i) ^ (-(Q + d))) :=
      mul_le_mul_of_nonneg_left (hb i).2 (mul_nonneg hD (Real.rpow_nonneg (hρ i).le _))
    _ = (D * C) * A i * ((ρ i) ^ d * (ρ i) ^ (-(Q + d))) := by ring
    _ = _ := by rw [← Real.rpow_add (hρ i), show d + -(Q + d) = -Q by ring]

/-- Remove the fixed polynomial cost of a source parameter jet from its
amplitude, by raising internal precision
(`app:ch_response:thm:response-literal-transfer`). -/
theorem rapidDecayAt_remove_amplitude_power
    (G : GradedScale E) (f : ι → E) (ρ A : ι → ℝ) (s : ℕ) (a : ℝ)
    (hρ : ∀ i, 0 < ρ i)
    (hf : RapidDecayAt G s ρ (fun i ↦ A i * (ρ i) ^ a) f) :
    RapidDecayAt G s ρ A f := by
  intro Q
  obtain ⟨C, hC, hb⟩ := hf (Q + a)
  refine ⟨C, hC, fun i ↦ ⟨(hb i).1, (hb i).2.trans_eq ?_⟩⟩
  calc
    C * (A i * (ρ i) ^ a) * (ρ i) ^ (-(Q + a)) =
        C * A i * ((ρ i) ^ a * (ρ i) ^ (-(Q + a))) := by ring
    _ = _ := by rw [← Real.rpow_add (hρ i), show a + -(Q + a) = -Q by ring]

/-- One constant works for a fixed finite set of observations, including the
physical and demodulated outputs and finitely many parameter jets, in
`app:ch_response:thm:response-literal-transfer`. -/
theorem rapidDecayAt_uniform_finite {κ : Type*} [Fintype κ]
    (G : GradedScale E) (f : κ → ι → E) (ρ A : ι → ℝ) (s : ℕ)
    (hρ : ∀ i, 0 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (hf : ∀ j, RapidDecayAt G s ρ A (f j)) :
    ∀ Q : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ j i,
      f j i ∈ G.level s ∧ G.gradeNorm s (f j i) ≤ C * A i * (ρ i) ^ (-Q) := by
  intro Q
  choose C hC hb using fun j ↦ hf j Q
  refine ⟨∑ j, C j, sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro j i
  refine ⟨(hb j i).1, (hb j i).2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (single_le_sum (fun k _ ↦ hC k) (mem_univ j)) (hA i))
    (Real.rpow_nonneg (hρ i) _)

/-- A fixed finite Leibniz expansion preserves complementary precision
(`app:ch_response:thm:response-literal-transfer`). For parameter derivatives,
`hexact` must be proved by differentiating the literal expression with frequency
and actual operators held fixed; the equality is not an estimate. -/
theorem rapidDecayAt_finite_expansion {κ : Type*}
    (G : GradedScale E) (I : Finset κ) (f : κ → ι → E) (g : ι → E)
    (ρ A : ι → ℝ) (s : ℕ)
    (hexact : ∀ i, g i = ∑ j ∈ I, f j i)
    (hf : ∀ j ∈ I, RapidDecayAt G s ρ A (f j)) :
    RapidDecayAt G s ρ A g := by
  classical
  intro Q
  choose C hC hb using fun j : I ↦ hf j j.property Q
  refine ⟨∑ j : I, C j, sum_nonneg (fun j _ ↦ hC j), ?_⟩
  intro i
  have hm : ∀ j ∈ I, f j i ∈ G.level s := fun j hj ↦ (hb ⟨j, hj⟩ i).1
  obtain ⟨hmem, hbound⟩ := ResponseTransfer.gradeNorm_sum_le G I (fun j ↦ f j i) s hm
  rw [hexact i]
  refine ⟨hmem, hbound.trans ?_⟩
  rw [← sum_attach I (fun j ↦ G.gradeNorm s (f j i))]
  calc
    _ ≤ ∑ j : I, C j * A i * (ρ i) ^ (-Q) := sum_le_sum (fun j _ ↦ (hb j i).2)
    _ = _ := by rw [sum_mul, sum_mul]

/-- A polynomial estimate on a bounded frequency interval can be absorbed into
any prescribed precision, by enlarging the constant
(`app:ch_response:thm:response-literal-transfer`). -/
theorem boundedFrequency_polynomial_le {ρ R d Q : ℝ} (hρ : 1 ≤ ρ) (hR : ρ ≤ R) :
    ρ ^ d ≤ (max R 1) ^ (max (d + Q) 0) * ρ ^ (-Q) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  calc
    ρ ^ d = ρ ^ (d + Q) * ρ ^ (-Q) := by
      rw [← Real.rpow_add hρpos, add_neg_cancel_right]
    _ ≤ ρ ^ (max (d + Q) 0) * ρ ^ (-Q) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hρ (le_max_left _ _))
        (Real.rpow_nonneg hρpos.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hρpos.le (hR.trans (le_max_left _ _)) (le_max_right _ _))
      (Real.rpow_nonneg hρpos.le _)

/-- Glue the large-frequency proof to the fixed-order bounded-frequency estimate
in `app:ch_response:thm:response-literal-transfer`. No arbitrary accuracy is
assumed on the bounded piece. -/
theorem rapidDecayAt_of_large_frequency
    (G : GradedScale E) (f : ι → E) (ρ A : ι → ℝ) (s : ℕ) (R B d : ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i) (hB : 0 ≤ B)
    (hlarge : RapidDecayAt G s (fun i : {i // R ≤ ρ i} ↦ ρ i)
      (fun i ↦ A i) (fun i ↦ f i))
    (hsmall : ∀ i, ρ i < R → f i ∈ G.level s ∧
      G.gradeNorm s (f i) ≤ B * A i * (ρ i) ^ d) :
    RapidDecayAt G s ρ A f := by
  intro Q
  obtain ⟨C, hC, hb⟩ := hlarge Q
  let D := B * (max R 1) ^ (max (d + Q) 0)
  have hD : 0 ≤ D := mul_nonneg hB (Real.rpow_nonneg (zero_le_one.trans (le_max_right _ _)) _)
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro i
  have hr : 0 ≤ (ρ i) ^ (-Q) := Real.rpow_nonneg (zero_le_one.trans (hρ i)) _
  by_cases hi : R ≤ ρ i
  · obtain ⟨hm, hh⟩ := hb ⟨i, hi⟩
    exact ⟨hm, hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (hA i)) hr)⟩
  · obtain ⟨hm, hh⟩ := hsmall i (lt_of_not_ge hi)
    refine ⟨hm, hh.trans ?_⟩
    calc
      _ ≤ B * A i * ((max R 1) ^ (max (d + Q) 0) * (ρ i) ^ (-Q)) :=
        mul_le_mul_of_nonneg_left (boundedFrequency_polynomial_le (hρ i) (le_of_not_ge hi))
          (mul_nonneg hB (hA i))
      _ = D * A i * (ρ i) ^ (-Q) := by dsimp [D]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (hA i)) hr

end JanetCartan.ResponseTransfer.Complement
