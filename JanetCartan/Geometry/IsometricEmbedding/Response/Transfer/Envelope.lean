module

public import JanetCartan.Analysis.Operator.GradedInverse.Scale

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Uniform envelope profiles

The scale algebra in `app:ch_response:eq:direct-envelope-profile` and
`app:ch_response:eq:fixed-factor-transfer`. The family index may include frequency,
the coefficient field, and the datum; constants are chosen before this index.
Every bound retains membership in the relevant scale, since `gradeNorm` alone
does not assert regularity. Instantiation with the actual demodulated graphs,
their adjoints, and their Sobolev spaces is a separate analytic obligation.
-/

@[expose] public noncomputable section

namespace JanetCartan.ResponseTransfer

open Finset

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniform source profile of `app:ch_response:eq:response-graded-source`.
This is a predicate on a supplied family, not a construction of a response. -/
def HasEnvelopeProfile (G : GradedScale E) (f : ι → E) (A K : ι → ℝ) : Prop :=
  ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
    f i ∈ G.level s ∧ G.gradeNorm s (f i) ≤ C * A i * K i ^ s

/-- Exact same-object identification transports an envelope profile without
changing its constants (`app:ch_response:eq:fixed-factor-transfer`).  This is
used after a literal kernel/operator equality; it does not provide an
estimate for either side. -/
theorem hasEnvelopeProfile_congr
    {G : GradedScale E} {f g : ι → E} {A K : ι → ℝ}
    (hfg : ∀ i, f i = g i) :
    HasEnvelopeProfile G f A K ↔ HasEnvelopeProfile G g A K := by
  constructor
  · intro hf s
    obtain ⟨C, hC, hs⟩ := hf s
    refine ⟨C, hC, ?_⟩
    intro i
    simpa [hfg i] using hs i
  · intro hg s
    obtain ⟨C, hC, hs⟩ := hg s
    refine ⟨C, hC, ?_⟩
    intro i
    simpa [hfg i] using hs i

/-- Triangle inequality with domain membership, used in the fixed finite sums
of `app:ch_response:thm:response-literal-transfer`. -/
theorem gradeNorm_add_le (G : GradedScale E) {s : ℕ} {x y : E}
    (hx : x ∈ G.level s) (hy : y ∈ G.level s) :
    G.gradeNorm s (x + y) ≤ G.gradeNorm s x + G.gradeNorm s y := by
  rw [G.gradeNorm_eq ((G.level s).add_mem hx hy), G.gradeNorm_eq hx, G.gradeNorm_eq hy]
  exact map_add_le_add (G.seminorm s) ⟨x, hx⟩ ⟨y, hy⟩

/-- A finite sum keeps its actual Sobolev domain and the sum of its bounds
(`app:ch_response:thm:response-literal-transfer`). -/
theorem gradeNorm_sum_le {κ : Type*} (G : GradedScale E) (I : Finset κ)
    (v : κ → E) (s : ℕ) (hv : ∀ j ∈ I, v j ∈ G.level s) :
    (∑ j ∈ I, v j) ∈ G.level s ∧
      G.gradeNorm s (∑ j ∈ I, v j) ≤ ∑ j ∈ I, G.gradeNorm s (v j) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    simp only [sum_empty, G.gradeNorm_eq ((G.level s).zero_mem)]
    exact le_of_eq (map_zero (G.seminorm s))
  | @insert j I hj ih =>
    have hmem := hv j (mem_insert_self j I)
    obtain ⟨hImem, hIbound⟩ := ih (fun k hk ↦ hv k (mem_insert_of_mem hk))
    rw [sum_insert hj, sum_insert hj]
    exact ⟨(G.level s).add_mem hmem hImem,
      (gradeNorm_add_le G hmem hImem).trans (add_le_add le_rfl hIbound)⟩

/-- Fixed finite sums preserve uniform envelope profiles
(`app:ch_response:thm:response-literal-transfer`). -/
theorem HasEnvelopeProfile.sum {κ : Type*} {G : GradedScale E}
    {f : κ → ι → E} {A K : ι → ℝ} (I : Finset κ)
    (hf : ∀ j ∈ I, HasEnvelopeProfile G (f j) A K) :
    HasEnvelopeProfile G (fun i ↦ ∑ j ∈ I, f j i) A K := by
  classical
  intro s
  choose C hC using fun j : I ↦ hf j j.property s
  refine ⟨∑ j : I, C j, sum_nonneg (fun j _ ↦ (hC j).1), ?_⟩
  intro i
  have hm : ∀ j ∈ I, f j i ∈ G.level s := fun j hj ↦ (hC ⟨j, hj⟩).2 i |>.1
  obtain ⟨hmem, hbound⟩ := gradeNorm_sum_le G I (fun j ↦ f j i) s hm
  refine ⟨hmem, hbound.trans ?_⟩
  rw [← sum_attach I (fun j ↦ G.gradeNorm s (f j i))]
  calc
    ∑ j : I, G.gradeNorm s (f j i) ≤ ∑ j : I, C j * A i * K i ^ s :=
      sum_le_sum (fun j _ ↦ ((hC j).2 i).2)
    _ = (∑ j : I, C j) * A i * K i ^ s := by rw [sum_mul, sum_mul]

/-- The numerical step from `app:ch_response:eq:direct-envelope-profile` to
`app:ch_response:eq:fixed-factor-transfer`. It has no loss in the power of `K`. -/
theorem direct_envelope_sum_le {L K A : ℝ} {C : ℕ → ℝ} {s : ℕ}
    (hL : 0 ≤ L) (hLK : L ≤ K) (hA : 0 ≤ A) (hC : ∀ r, 0 ≤ C r) :
    (∑ r ∈ range (s + 1), L ^ (s - r) * (C r * A * K ^ r)) ≤
      (∑ r ∈ range (s + 1), C r) * A * K ^ s := by
  have hK := hL.trans hLK
  calc
    _ ≤ ∑ r ∈ range (s + 1), K ^ (s - r) * (C r * A * K ^ r) := by
      apply sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL hLK _)
        (mul_nonneg (mul_nonneg (hC r) hA) (pow_nonneg hK r))
    _ = ∑ r ∈ range (s + 1), C r * A * K ^ s := by
      apply sum_congr rfl
      intro r hr
      have hrs : r ≤ s := Nat.le_of_lt_succ (mem_range.mp hr)
      rw [show K ^ (s - r) * (C r * A * K ^ r) =
        C r * A * (K ^ (s - r) * K ^ r) by ring,
        ← pow_add, Nat.sub_add_cancel hrs]
    _ = _ := by rw [sum_mul, sum_mul]

/-- Conditional scale-level transfer from the exact direct estimate in
`app:ch_response:eq:direct-envelope-profile`. Proving `hbound` for the actual
graph kernels in both directions is not part of this algebraic lemma. -/
theorem HasEnvelopeProfile.of_direct_estimate
    {G : GradedScale E} {H : GradedScale F} {f : ι → E} {g : ι → F}
    {A K L : ι → ℝ} (hf : HasEnvelopeProfile G f A K)
    (hA : ∀ i, 0 ≤ A i) (hL : ∀ i, 0 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hmem : ∀ i s, g i ∈ H.level s)
    (hbound : ∀ s, ∃ D : ℝ, 0 ≤ D ∧ ∀ i,
      H.gradeNorm s (g i) ≤
        D * ∑ r ∈ range (s + 1), L i ^ (s - r) * G.gradeNorm r (f i)) :
    HasEnvelopeProfile H g A K := by
  choose C hC hf using hf
  intro s
  obtain ⟨D, hD, hbound⟩ := hbound s
  refine ⟨D * ∑ r ∈ range (s + 1), C r,
    mul_nonneg hD (sum_nonneg (fun r _ ↦ hC r)), ?_⟩
  intro i
  refine ⟨hmem i s, (hbound i).trans ?_⟩
  calc
    D * (∑ r ∈ range (s + 1), L i ^ (s - r) * G.gradeNorm r (f i))
        ≤ D * (∑ r ∈ range (s + 1), L i ^ (s - r) *
          (C r * A i * K i ^ r)) := by
      apply mul_le_mul_of_nonneg_left _ hD
      exact sum_le_sum (fun r _ ↦ mul_le_mul_of_nonneg_left (hf r i).2
        (pow_nonneg (hL i) _))
    _ ≤ D * ((∑ r ∈ range (s + 1), C r) * A i * K i ^ s) :=
      mul_le_mul_of_nonneg_left (direct_envelope_sum_le (hL i) (hLK i) (hA i) hC) hD
    _ = _ := by ring

end JanetCartan.ResponseTransfer
