module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope
public import JanetCartan.Analysis.Operator.FiniteNeumann

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Envelope assembly for the same complete inverse

This is the finite-expansion step in `app:ch_response:eq:response-graded-reduced`.
The finite chains and the quantitative smoothing estimate are explicit inputs.
The theorem uses the existing finite Neumann observation theorem, with one inverse
and one family of observations at every depth. It does not prove the graph bounds,
the negative-Sobolev source gain, or the smoothing estimate for the actual residual.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer

open Finset

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Add a small remainder to a signed finite chain sum without changing the field
or inverse (`app:ch_response:eq:response-graded-reduced`). All level memberships
are retained; this is a scale triangle inequality, not a smoothing estimate. -/
theorem signed_sum_remainder_bound (H : GradedScale F) (s d : ℕ)
    (v : ℕ → F) (x : F) (C : ℕ → ℝ) {A K D : ℝ}
    (hA : 0 ≤ A) (hK : 1 ≤ K) (hD : 0 ≤ D)
    (hv : ∀ j < d, v j ∈ H.level s ∧ H.gradeNorm s (v j) ≤ C j * A * K ^ s)
    (hr : x - (∑ j ∈ range d, ((-1 : ℝ) ^ j) • v j) ∈ H.level s)
    (hbound : H.gradeNorm s (x - (∑ j ∈ range d, ((-1 : ℝ) ^ j) • v j)) ≤ D * A) :
    x ∈ H.level s ∧ H.gradeNorm s x ≤ ((∑ j ∈ range d, C j) + D) * A * K ^ s := by
  have hmem : ∀ j ∈ range d, ((-1 : ℝ) ^ j) • v j ∈ H.level s :=
    fun j hj ↦ (H.level s).smul_mem _ (hv j (mem_range.mp hj)).1
  obtain ⟨hsum, hsum_bound⟩ := gradeNorm_sum_le H (range d)
    (fun j ↦ ((-1 : ℝ) ^ j) • v j) s hmem
  have hsum_bound' : H.gradeNorm s (∑ j ∈ range d, ((-1 : ℝ) ^ j) • v j) ≤
      (∑ j ∈ range d, C j) * A * K ^ s := by
    apply hsum_bound.trans
    calc
      _ ≤ ∑ j ∈ range d, C j * A * K ^ s := by
        apply sum_le_sum
        intro j hj
        rw [H.gradeNorm_neg_one_pow_smul s j (hv j (mem_range.mp hj)).1]
        exact (hv j (mem_range.mp hj)).2
      _ = _ := by rw [sum_mul, sum_mul]
  have hx : x ∈ H.level s := by
    simpa only [sub_add_cancel] using (H.level s).add_mem hr hsum
  refine ⟨hx, ?_⟩
  have hadd := gradeNorm_add_le H hr hsum
  simp only [sub_add_cancel] at hadd
  calc
    H.gradeNorm s x ≤ D * A + (∑ j ∈ range d, C j) * A * K ^ s :=
      hadd.trans (add_le_add hbound hsum_bound')
    _ ≤ D * A * K ^ s + (∑ j ∈ range d, C j) * A * K ^ s := by
      exact add_le_add (le_mul_of_one_le_right (mul_nonneg hD hA) (one_le_pow₀ hK)) le_rfl
    _ = _ := by ring

/-- Conditional inverse transfer in `app:ch_response:eq:response-graded-reduced`.
Finite-chain envelope estimates and `app:ch_regular:eq:inverse-remainder` imply
the same envelope profile for the single complete inverse `T`. The observation
may include demodulation and the fixed solver. The frequency window is retained,
with `L ≤ K ≤ ρ^(1-ν)`; the constant at order `s` is uniform in the family index.
The unit envelope scale is retained, as required by
`app:ch_response:cor:finite-jets`: only `1 ≤ K` is used in the finite sum,
and the remainder-depth producer needs only `1 ≤ ρ`. No operator, constant,
cutoff or source changes when the lower scale bound is attained.
No estimate for the actual FIO or reconstruction is asserted by this theorem. -/
theorem inverse_hasEnvelopeProfile_of_smoothing_one_le
    (G : GradedScale E) (H : GradedScale F)
    (R T : ι → E →L[ℝ] E) (B : ι → E →ₗ[ℝ] F) (h : ι → E)
    (ρ L K A : ι → ℝ) (ν : ℝ)
    (hT : ∀ i, T i * (1 + R i) = 1)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i)
    (hK : ∀ i, 1 ≤ K i) (hLK : ∀ i, L i ≤ K i)
    (hν : 0 < ν) (hν1 : ν < 1) (hwindow : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hA : ∀ i, 0 ≤ A i)
    (hchain : ∀ j, HasEnvelopeProfile H (fun i ↦ B i (((R i) ^ j) (h i))) A K)
    (hobs : ∀ s, ∃ (t : ℕ) (c CB : ℝ), 0 ≤ CB ∧
      (∀ i v, v ∈ G.level t → B i v ∈ H.level s) ∧
      (∀ i v, v ∈ G.level t →
        H.gradeNorm s (B i v) ≤ CB * (ρ i) ^ c * G.gradeNorm t v) ∧
      ∃ CP : ℕ → ℝ, (∀ N, 0 ≤ CP N) ∧
        (∀ i N, T i (((R i) ^ (N + t)) (h i)) ∈ G.level t) ∧
        (∀ i N, G.gradeNorm t (T i (((R i) ^ (N + t)) (h i))) ≤
          CP N * A i * (L i) ^ t * (L i / ρ i) ^ N)) :
    HasEnvelopeProfile H (fun i ↦ B i (T i (h i))) A K := by
  have hν' : 0 < ν ∧ ν < 1 := ⟨hν, hν1⟩
  have hscale : ∀ i, L i ≤ (ρ i) ^ (1 - ν) := fun i ↦ (hLK i).trans (hwindow i)
  intro s
  obtain ⟨t, c, CB, hCB, hBmem, hB, CP, hCP, hPmem, hP⟩ := hobs s
  obtain ⟨d, _, D, hD, hrem⟩ := exists_finite_neumann_observation_depth
    G H R T B h ρ L A s t ν c 0 CB CP hT hρ hL hν'.1 hscale hA hCB hCP
    hBmem hB hPmem hP
  choose C hC hterms using fun j ↦ hchain j s
  refine ⟨(∑ j ∈ range d, C j) + D,
    add_nonneg (sum_nonneg (fun j _ ↦ hC j)) hD, ?_⟩
  intro i
  obtain ⟨hrmem, hrbound⟩ := hrem i
  simp only [neg_zero, Real.rpow_zero, mul_one] at hrbound
  exact signed_sum_remainder_bound H s d
    (fun j ↦ B i (((R i) ^ j) (h i))) (B i (T i (h i))) C
    (hA i) (hK i) hD
    (fun j _ ↦ hterms j i) hrmem hrbound

/-- Conditional inverse transfer in `app:ch_response:eq:response-graded-reduced`.
Finite-chain envelope estimates and `app:ch_regular:eq:inverse-remainder` imply
the same envelope profile for the single complete inverse `T`. The observation
may include demodulation and the fixed solver. The frequency window is retained,
with `L ≤ K ≤ ρ^(1-ν)`; the constant at order `s` is uniform in the family index.
No estimate for the actual FIO or reconstruction is asserted by this theorem. -/
theorem inverse_hasEnvelopeProfile_of_smoothing
    (G : GradedScale E) (H : GradedScale F)
    (R T : ι → E →L[ℝ] E) (B : ι → E →ₗ[ℝ] F) (h : ι → E)
    (ρ L K A : ι → ℝ) (ν : ℝ)
    (hT : ∀ i, T i * (1 + R i) = 1)
    (hρ : ∀ i, 2 ≤ ρ i) (hL : ∀ i, 1 ≤ L i)
    (hK : ∀ i, 2 ≤ K i) (hLK : ∀ i, L i ≤ K i)
    (hν : 0 < ν) (hν1 : ν < 1) (hwindow : ∀ i, K i ≤ (ρ i) ^ (1 - ν))
    (hA : ∀ i, 0 ≤ A i)
    (hchain : ∀ j, HasEnvelopeProfile H (fun i ↦ B i (((R i) ^ j) (h i))) A K)
    (hobs : ∀ s, ∃ (t : ℕ) (c CB : ℝ), 0 ≤ CB ∧
      (∀ i v, v ∈ G.level t → B i v ∈ H.level s) ∧
      (∀ i v, v ∈ G.level t →
        H.gradeNorm s (B i v) ≤ CB * (ρ i) ^ c * G.gradeNorm t v) ∧
      ∃ CP : ℕ → ℝ, (∀ N, 0 ≤ CP N) ∧
        (∀ i N, T i (((R i) ^ (N + t)) (h i)) ∈ G.level t) ∧
        (∀ i N, G.gradeNorm t (T i (((R i) ^ (N + t)) (h i))) ≤
          CP N * A i * (L i) ^ t * (L i / ρ i) ^ N)) :
    HasEnvelopeProfile H (fun i ↦ B i (T i (h i))) A K := by
  exact inverse_hasEnvelopeProfile_of_smoothing_one_le G H R T B h ρ L K A ν hT
    (fun i ↦ (by norm_num : (1 : ℝ) ≤ 2).trans (hρ i)) hL
    (fun i ↦ (by norm_num : (1 : ℝ) ≤ 2).trans (hK i)) hLK hν hν1 hwindow hA hchain hobs

/-- Conditional arbitrary-accuracy observation of the same inverse, the second
bound in `app:ch_response:eq:response-graded-reduced`. Every fixed finite chain
must have arbitrary precision, and the original source must supply the stated
smoothing power estimate. These are genuine analytic inputs, not consequences
of the inverse identity. All orders and precisions use the same `T` and `B`. -/
theorem inverse_rapid_decay_of_smoothing
    (G : GradedScale E) (H : GradedScale F)
    (R T : ι → E →L[ℝ] E) (B : ι → E →ₗ[ℝ] F) (h : ι → E)
    (ρ L A : ι → ℝ) (ν : ℝ)
    (hT : ∀ i, T i * (1 + R i) = 1)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i)
    (hν : 0 < ν) (hscale : ∀ i, L i ≤ (ρ i) ^ (1 - ν))
    (hA : ∀ i, 0 ≤ A i)
    (hchain : ∀ j s (Q : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      B i (((R i) ^ j) (h i)) ∈ H.level s ∧
        H.gradeNorm s (B i (((R i) ^ j) (h i))) ≤ C * A i * (ρ i) ^ (-Q))
    (hobs : ∀ s, ∃ (t : ℕ) (c CB : ℝ), 0 ≤ CB ∧
      (∀ i v, v ∈ G.level t → B i v ∈ H.level s) ∧
      (∀ i v, v ∈ G.level t →
        H.gradeNorm s (B i v) ≤ CB * (ρ i) ^ c * G.gradeNorm t v) ∧
      ∃ CP : ℕ → ℝ, (∀ N, 0 ≤ CP N) ∧
        (∀ i N, T i (((R i) ^ (N + t)) (h i)) ∈ G.level t) ∧
        (∀ i N, G.gradeNorm t (T i (((R i) ^ (N + t)) (h i))) ≤
          CP N * A i * (L i) ^ t * (L i / ρ i) ^ N)) :
    ∀ s (Q : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      B i (T i (h i)) ∈ H.level s ∧
        H.gradeNorm s (B i (T i (h i))) ≤ C * A i * (ρ i) ^ (-Q) := by
  intro s Q
  obtain ⟨t, c, CB, hCB, hBmem, hB, CP, hCP, hPmem, hP⟩ := hobs s
  obtain ⟨d, _, D, hD, hrem⟩ := exists_finite_neumann_observation_depth
    G H R T B h ρ L A s t ν c Q CB CP hT hρ hL hν hscale hA hCB hCP
    hBmem hB hPmem hP
  choose C hC hterms using fun j ↦ hchain j s Q
  refine ⟨(∑ j ∈ range d, C j) + D,
    add_nonneg (sum_nonneg (fun j _ ↦ hC j)) hD, ?_⟩
  intro i
  have hAi : 0 ≤ A i * (ρ i) ^ (-Q) :=
    mul_nonneg (hA i) (Real.rpow_nonneg (zero_le_one.trans (hρ i)) _)
  have hterms' : ∀ j < d, B i (((R i) ^ j) (h i)) ∈ H.level s ∧
      H.gradeNorm s (B i (((R i) ^ j) (h i))) ≤ C j * (A i * (ρ i) ^ (-Q)) * 1 ^ s := by
    intro j _
    simpa only [one_pow, mul_one, mul_assoc] using hterms j i
  have hrbound := (hrem i).2
  rw [mul_assoc] at hrbound
  have hout := signed_sum_remainder_bound H s d
    (fun j ↦ B i (((R i) ^ j) (h i))) (B i (T i (h i))) C
    hAi le_rfl hD hterms' (hrem i).1 hrbound
  simpa only [one_pow, mul_one, mul_assoc] using hout

end JanetCartan.ResponseTransfer
