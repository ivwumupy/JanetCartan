module

public import JanetCartan.Analysis.Operator.FiniteNeumann

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Assembly of the resolved angular tail

The last step of `app:ch_regular:thm:quantitative`, conditional on the finite-chain
tails and the quantitative inverse remainder. These inputs concern the same
operators at every proof depth. This module does not assert that the actual
protected sources satisfy them.
-/

@[expose] public noncomputable section

namespace JanetCartan.ArbitraryAccuracy

open Finset

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniform arbitrary decay at one Sobolev level, with domain membership retained
(`app:ch_regular:eq:resolved-angular-tail`). The constant precedes the family index,
which may include frequency, coefficients, and the source. -/
def RapidDecayAt (G : GradedScale E) (s : ℕ) (ρ A : ι → ℝ) (f : ι → E) : Prop :=
  ∀ Q : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
    f i ∈ G.level s ∧ G.gradeNorm s (f i) ≤ C * A i * (ρ i) ^ (-Q)

/-- Triangle inequality on a genuine graded domain, used in the last finite sum
of `app:ch_regular:thm:quantitative`. -/
theorem gradeNorm_add_le (G : GradedScale E) {s : ℕ} {v w : E}
    (hv : v ∈ G.level s) (hw : w ∈ G.level s) :
    G.gradeNorm s (v + w) ≤ G.gradeNorm s v + G.gradeNorm s w := by
  rw [G.gradeNorm_eq ((G.level s).add_mem hv hw), G.gradeNorm_eq hv, G.gradeNorm_eq hw]
  exact map_add_le_add (G.seminorm s) ⟨v, hv⟩ ⟨w, hw⟩

/-- The signed finite Neumann sum preserves a uniform bound, with no infinite
sum or convergence argument (`app:ch_regular:eq:finite-observation`). -/
theorem signed_sum_bound (G : GradedScale E) (s d : ℕ) (f : ℕ → E)
    (C : ℕ → ℝ) (a : ℝ)
    (hmem : ∀ j < d, f j ∈ G.level s)
    (hbound : ∀ j < d, G.gradeNorm s (f j) ≤ C j * a) :
    (∑ j ∈ range d, ((-1 : ℝ) ^ j) • f j) ∈ G.level s ∧
    G.gradeNorm s (∑ j ∈ range d, ((-1 : ℝ) ^ j) • f j) ≤
      (∑ j ∈ range d, C j) * a := by
  induction d with
  | zero =>
    simp only [range_zero, sum_empty, zero_mul]
    refine ⟨(G.level s).zero_mem, ?_⟩
    rw [G.gradeNorm_eq (G.level s).zero_mem]
    exact le_of_eq (map_zero (G.seminorm s))
  | succ d ih =>
    obtain ⟨hm, hb⟩ := ih (fun j hj ↦ hmem j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hbound j (Nat.lt_succ_of_lt hj))
    have hd := hmem d (Nat.lt_succ_self d)
    have hsm := (G.level s).smul_mem ((-1 : ℝ) ^ d) hd
    simp only [sum_range_succ]
    refine ⟨(G.level s).add_mem hm hsm, ?_⟩
    calc
      _ ≤ G.gradeNorm s (∑ j ∈ range d, ((-1 : ℝ) ^ j) • f j) +
          G.gradeNorm s (((-1 : ℝ) ^ d) • f d) := gradeNorm_add_le G hm hsm
      _ ≤ (∑ j ∈ range d, C j) * a + C d * a := by
        rw [G.gradeNorm_neg_one_pow_smul s d hd]
        exact add_le_add hb (hbound d (Nat.lt_succ_self d))
      _ = _ := by ring

/-- Deduce `app:ch_regular:eq:resolved-angular-tail` from the finite-chain tails
and `app:ch_regular:eq:inverse-remainder`, using one fixed inverse `T`.
All analytic estimates are explicit inputs; the finite Neumann depth and the
constant are chosen uniformly before the family index. -/
theorem rapidDecayAt_inverse_of_finite_chains
    (G : GradedScale E) (H : GradedScale F)
    (K T : ι → E →L[ℝ] E) (B : ι → E →ₗ[ℝ] F) (h : ι → E)
    (ρ L A : ι → ℝ) (s t : ℕ) (σ c CB : ℝ) (CP : ℕ → ℝ)
    (hT : ∀ i, T i * (1 + K i) = 1)
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i)
    (hσ : 0 < σ) (hscale : ∀ i, L i ≤ (ρ i) ^ (1 - σ))
    (hA : ∀ i, 0 ≤ A i) (hCB : 0 ≤ CB) (hCP : ∀ N, 0 ≤ CP N)
    (hB_mem : ∀ i v, v ∈ G.level t → B i v ∈ H.level s)
    (hB : ∀ i v, v ∈ G.level t →
      H.gradeNorm s (B i v) ≤ CB * (ρ i) ^ c * G.gradeNorm t v)
    (hpower_mem : ∀ i N, T i (((K i) ^ (N + t)) (h i)) ∈ G.level t)
    (hpower : ∀ i N, G.gradeNorm t (T i (((K i) ^ (N + t)) (h i))) ≤
      CP N * A i * (L i) ^ t * (L i / ρ i) ^ N)
    (hchain : ∀ j, RapidDecayAt H s ρ A (fun i ↦ B i (((K i) ^ j) (h i)))) :
    RapidDecayAt H s ρ A (fun i ↦ B i (T i (h i))) := by
  intro Q
  obtain ⟨d, _, CR, hCR, hrem⟩ := exists_finite_neumann_observation_depth
    G H K T B h ρ L A s t σ c Q CB CP hT hρ hL hσ hscale hA hCB hCP
      hB_mem hB hpower_mem hpower
  choose C hC htail using fun j ↦ hchain j Q
  refine ⟨CR + ∑ j ∈ range d, C j,
    add_nonneg hCR (sum_nonneg fun j _ ↦ hC j), ?_⟩
  intro i
  obtain ⟨hsm, hsb⟩ := signed_sum_bound H s d
    (fun j ↦ B i (((K i) ^ j) (h i))) C (A i * (ρ i) ^ (-Q))
    (fun j _ ↦ (htail j i).1)
    (fun j _ ↦ by simpa only [mul_assoc] using (htail j i).2)
  obtain ⟨hrm, hrb⟩ := hrem i
  have hdecomp : B i (T i (h i)) =
      (B i (T i (h i)) - ∑ j ∈ range d, ((-1 : ℝ) ^ j) • B i (((K i) ^ j) (h i))) +
      ∑ j ∈ range d, ((-1 : ℝ) ^ j) • B i (((K i) ^ j) (h i)) := by abel
  have htotal : B i (T i (h i)) ∈ H.level s := by
    rw [hdecomp]
    exact (H.level s).add_mem hrm hsm
  refine ⟨htotal, ?_⟩
  calc
    H.gradeNorm s (B i (T i (h i))) ≤
        H.gradeNorm s (B i (T i (h i)) -
          ∑ j ∈ range d, ((-1 : ℝ) ^ j) • B i (((K i) ^ j) (h i))) +
        H.gradeNorm s (∑ j ∈ range d, ((-1 : ℝ) ^ j) • B i (((K i) ^ j) (h i))) := by
      conv_lhs => rw [hdecomp]
      exact gradeNorm_add_le H hrm hsm
    _ ≤ CR * A i * (ρ i) ^ (-Q) + (∑ j ∈ range d, C j) * (A i * (ρ i) ^ (-Q)) :=
      add_le_add hrb hsb
    _ = _ := by ring

/-- Transfer the resolved angular tail through the exact physical identity
`app:ch_regular:eq:exact-physical` to `app:ch_regular:eq:pde-arbitrary`.
Here `f` is the source restricted to the fixed core, and `u` is the actual
solver output. This does not construct that solver or its physical identity. -/
theorem rapidDecayAt_physical_error
    {V : Type*} (H : GradedScale F) (s : ℕ) (ρ A : ι → ℝ)
    (P : ι → V → F) (u : ι → V) (f e : ι → F)
    (hphysical : ∀ i, P i (u i) = f i + e i)
    (htail : RapidDecayAt H s ρ A e) :
    RapidDecayAt H s ρ A (fun i ↦ P i (u i) - f i) := by
  simpa only [hphysical, add_sub_cancel_left] using htail

end JanetCartan.ArbitraryAccuracy
