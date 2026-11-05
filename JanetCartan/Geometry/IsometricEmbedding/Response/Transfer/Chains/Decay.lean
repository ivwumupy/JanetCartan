module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.Assembly

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absorption of the downstream costs of complementary terms

The arbitrary-accuracy step in the final chain paragraphs of
`app:ch_response:thm:response-literal-transfer`. These lemmas consume supplied
Sobolev estimates for the actual full factors; they do not construct the factors.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer

open Finset ArbitraryAccuracy

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed-order polynomial Sobolev cost of an actual downstream factor, as used
in `app:ch_response:thm:response-literal-transfer`. Orders, powers, and constants
are chosen before frequency, coefficients, and data. This is an analytic input. -/
def HasPolynomialSobolevCost (G : GradedScale E) (H : GradedScale F)
    (ρ : ι → ℝ) (T : ι → E →ₗ[ℝ] F) : Prop :=
  ∀ s, ∃ (t : ℕ) (c D : ℝ), 0 ≤ D ∧ ∀ i v, v ∈ G.level t →
    T i v ∈ H.level s ∧
      H.gradeNorm s (T i v) ≤ D * (ρ i) ^ c * G.gradeNorm t v

/-- A complementary error pays a full downstream factor's polynomial cost.
The internal precision `Q + c + 1` is fixed before the family index
(`app:ch_response:thm:response-literal-transfer`). -/
theorem rapidDecayAt_polynomial_factor
    {G : GradedScale E} {H : GradedScale F} {ρ A : ι → ℝ}
    {T : ι → E →ₗ[ℝ] F} {f : ι → E}
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i)
    (hcost : HasPolynomialSobolevCost G H ρ T)
    (hf : ∀ t, RapidDecayAt G t ρ A f) :
    ∀ s, RapidDecayAt H s ρ A (fun i ↦ T i (f i)) := by
  intro s Q
  obtain ⟨t, c, D, hD, hT⟩ := hcost s
  obtain ⟨C, hC, hf⟩ := hf t (Q + c + 1)
  refine ⟨D * C, mul_nonneg hD hC, ?_⟩
  intro i
  obtain ⟨hmem, hbound⟩ := hT i (f i) (hf i).1
  have hρpos : 0 < ρ i := lt_of_lt_of_le zero_lt_one (hρ i)
  refine ⟨hmem, hbound.trans ?_⟩
  calc
    D * (ρ i) ^ c * G.gradeNorm t (f i) ≤
        D * (ρ i) ^ c * (C * A i * (ρ i) ^ (-(Q + c + 1))) :=
      mul_le_mul_of_nonneg_left (hf i).2
        (mul_nonneg hD (Real.rpow_nonneg hρpos.le _))
    _ = (D * C) * A i * (ρ i) ^ (-Q - 1) := by
      rw [show D * (ρ i) ^ c * (C * A i * (ρ i) ^ (-(Q + c + 1))) =
        (D * C) * A i * ((ρ i) ^ c * (ρ i) ^ (-(Q + c + 1))) by ring,
        ← Real.rpow_add hρpos]
      congr 2
      ring
    _ ≤ (D * C) * A i * (ρ i) ^ (-Q) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hρ i) (by linarith))
        (mul_nonneg (mul_nonneg hD hC) (hA i))

/-- Finite complementary sums retain arbitrary precision and all memberships,
using the existing graded finite-sum bound
(`app:ch_response:thm:response-literal-transfer`). -/
theorem rapidDecayAt_chain_sum {κ : Type*} {G : GradedScale E}
    {ρ A : ι → ℝ} {f : κ → ι → E} (I : Finset κ) (s : ℕ)
    (hf : ∀ j ∈ I, RapidDecayAt G s ρ A (f j)) :
    RapidDecayAt G s ρ A (fun i ↦ ∑ j ∈ I, f j i) := by
  classical
  intro Q
  choose C hC using fun j : I ↦ hf j j.property Q
  refine ⟨∑ j : I, C j, sum_nonneg (fun j _ ↦ (hC j).1), ?_⟩
  intro i
  obtain ⟨hm, hb⟩ := gradeNorm_sum_le G I (fun j ↦ f j i) s
    (fun j hj ↦ ((hC ⟨j, hj⟩).2 i).1)
  refine ⟨hm, hb.trans ?_⟩
  rw [← sum_attach I (fun j ↦ G.gradeNorm s (f j i))]
  calc
    ∑ j : I, G.gradeNorm s (f j i) ≤
        ∑ j : I, C j * A i * (ρ i) ^ (-Q) :=
      sum_le_sum (fun j _ ↦ ((hC j).2 i).2)
    _ = _ := by rw [sum_mul, sum_mul]

/-- A rapidly decaying error fits the envelope profile for `K ≥ 1`, as required
when adding leakage to the near chain in `app:ch_response:eq:fixed-factor-transfer`. -/
theorem hasEnvelopeProfile_of_rapidDecayAt {G : GradedScale E}
    {ρ A K : ι → ℝ} {f : ι → E}
    (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (hf : ∀ s, RapidDecayAt G s ρ A f) : HasEnvelopeProfile G f A K := by
  intro s
  obtain ⟨C, hC, hf⟩ := hf s 0
  refine ⟨C, hC, ?_⟩
  intro i
  refine ⟨(hf i).1, ?_⟩
  have hb : G.gradeNorm s (f i) ≤ C * A i := by simpa using (hf i).2
  exact hb.trans (le_mul_of_one_le_right (mul_nonneg hC (hA i)) (one_le_pow₀ (hK i)))

end JanetCartan.ResponseTransfer
