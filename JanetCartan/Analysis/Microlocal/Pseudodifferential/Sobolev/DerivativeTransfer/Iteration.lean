module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Amplitude

/-!
# Ordered derivative transfer

Finite combinatorics and physical amplitude budgets for
`app:ch_regular_base:eq:graph-derivative-transfer`. The operator expansion below
is explicitly conditional on an abstract first-derivative recurrence. It does
not assert that the recurrence holds for a pseudodifferential operator.
-/

@[expose] public noncomputable section

open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential

variable {ι B U Y : Type*} {d : ℕ}

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: ordered iteration,
with the first listed operation acting outermost. -/
def orderedTransferAction (F : ι → B → B) : List ι → B → B
  | [], b => b
  | i :: is, b => F i (orderedTransferAction F is b)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: a property stable under
each operation is stable under ordered iteration. -/
theorem orderedTransferAction_preserves (F : ι → B → B) (P : B → Prop)
    (hF : ∀ i b, P b → P (F i b)) (is : List ι) {b : B} (hb : P b) :
    P (orderedTransferAction F is b) := by
  induction is with
  | nil => exact hb
  | cons i is ih => exact hF i _ ih

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: enumerate branches
with multiplicity. The first list records transfers and the second datum
derivatives; each new output derivative chooses exactly one of the two. -/
def orderedTransferTerms : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | i :: is =>
      (orderedTransferTerms is).map (fun p => (i :: p.1, p.2)) ++
      (orderedTransferTerms is).map (fun p => (p.1, i :: p.2))

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: there are exactly
`2 ^ s` branches, counted with multiplicity even for repeated coordinates. -/
theorem orderedTransferTerms_length (is : List ι) :
    (orderedTransferTerms is).length = 2 ^ is.length := by
  induction is with
  | nil => simp [orderedTransferTerms]
  | cons i is ih => simp [orderedTransferTerms, ih, pow_succ, Nat.mul_two]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: both derivative lists
retain their original order, and each output derivative is used exactly once. -/
theorem orderedTransferTerms_spec (is : List ι) (p : List ι × List ι)
    (hp : p ∈ orderedTransferTerms is) :
    p.1.Sublist is ∧ p.2.Sublist is ∧ p.1.length + p.2.length = is.length := by
  induction is generalizing p with
  | nil =>
      simp only [orderedTransferTerms, List.mem_singleton] at hp
      subst p
      simp
  | cons i is ih =>
      simp only [orderedTransferTerms, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · obtain ⟨ha, hb, hc⟩ := ih q hq
        exact ⟨ha.cons_cons i, hb.cons i, by simp only [List.length_cons]; omega⟩
      · obtain ⟨ha, hb, hc⟩ := ih q hq
        exact ⟨ha.cons i, hb.cons_cons i, by simp only [List.length_cons]; omega⟩

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: a branch with `k`
datum derivatives has exactly `s - k` transfer steps. -/
theorem orderedTransferTerms_transfer_count (is : List ι) (p : List ι × List ι)
    (hp : p ∈ orderedTransferTerms is) :
    p.1.length = is.length - p.2.length := by
  have := (orderedTransferTerms_spec is p hp).2.2
  omega

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: finite ordered
expansion under an abstract one-derivative recurrence. `P` and `Q` describe
admissible amplitudes and data, and their stability is required explicitly.
The additive maps `D` allow differentiation of the finite sum. -/
theorem orderedTransferAction_expansion [AddCommMonoid Y]
    (F : ι → B → B) (G : ι → U → U) (D : ι → Y →+ Y) (T : B → U → Y)
    (P : B → Prop) (Q : U → Prop)
    (hF : ∀ i b, P b → P (F i b)) (hG : ∀ i u, Q u → Q (G i u))
    (hrec : ∀ i b u, P b → Q u → D i (T b u) = T (F i b) u + T b (G i u))
    (is : List ι) {b : B} {u : U} (hb : P b) (hu : Q u) :
    orderedTransferAction (fun i => D i) is (T b u) =
      ((orderedTransferTerms is).map fun p =>
        T (orderedTransferAction F p.1 b) (orderedTransferAction G p.2 u)).sum := by
  induction is with
  | nil => simp [orderedTransferAction, orderedTransferTerms]
  | cons i is ih =>
      simp only [orderedTransferAction, ih, orderedTransferTerms,
        List.map_append, List.map_map, List.sum_append, Function.comp_def]
      rw [map_list_sum]
      simp only [List.map_map, Function.comp_def]
      rw [← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p hp
      exact hrec i _ _ (orderedTransferAction_preserves F P hF p.1 hb)
        (orderedTransferAction_preserves G Q hG p.2 hu)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: iterate derivatives
of the full amplitude in the specified order, including both physical masks. -/
def iteratedTransferAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (is : List (Fin d)) :=
  orderedTransferAction (fun i b => transferAmplitude b i) is b

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the abstract ordered
action specializes to the existing ordered coordinate derivative convention. -/
theorem orderedTransferAction_euclideanCoordinateDerivList
    (is : List (Fin d)) (u : EuclideanSpace ℝ (Fin d) → ℂ) :
    orderedTransferAction (fun i => euclideanCoordinateDerivList [i]) is u =
      euclideanCoordinateDerivList is u := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      change euclideanCoordinateDerivList [i]
        (orderedTransferAction (fun i => euclideanCoordinateDerivList [i]) is u) = _
      rw [ih]
      rfl

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the abstract
recurrence expansion specialized to the full scalar amplitudes and ordered
coordinate derivatives of the datum. The actual operator recurrence and the
stability of its admissible classes remain explicit premises. -/
theorem iteratedTransferAmplitude_expansion [AddCommMonoid Y]
    (D : Fin d → Y →+ Y)
    (T : (EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ) →
      (EuclideanSpace ℝ (Fin d) → ℂ) → Y)
    (P : (EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ) → Prop)
    (Q : (EuclideanSpace ℝ (Fin d) → ℂ) → Prop)
    (hP : ∀ i b, P b → P (transferAmplitude b i))
    (hQ : ∀ i u, Q u → Q (euclideanCoordinateDerivList [i] u))
    (hrec : ∀ i b u, P b → Q u → D i (T b u) =
      T (transferAmplitude b i) u + T b (euclideanCoordinateDerivList [i] u))
    (is : List (Fin d))
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    {u : EuclideanSpace ℝ (Fin d) → ℂ} (hb : P b) (hu : Q u) :
    orderedTransferAction (fun i => D i) is (T b u) =
      ((orderedTransferTerms is).map fun p =>
        T (iteratedTransferAmplitude b p.1) (euclideanCoordinateDerivList p.2 u)).sum := by
  simpa only [iteratedTransferAmplitude, orderedTransferAction_euclideanCoordinateDerivList]
    using orderedTransferAction_expansion (fun i b => transferAmplitude b i)
      (fun i => euclideanCoordinateDerivList [i]) D T P Q hP hQ hrec is hb hu

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: all transfer steps
preserve smoothness in the physical positions. -/
theorem contDiff_iteratedTransferAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (is : List (Fin d)) (ξ) :
    ContDiff ℝ ∞ (iteratedTransferAmplitude b is ξ) := by
  exact orderedTransferAction_preserves _ (fun b => ∀ ξ, ContDiff ℝ ∞ (b ξ))
    (fun i b hb ξ => contDiff_transferAmplitude b hb i ξ) is hb ξ

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: transfer iteration
preserves joint frequency and physical smoothness. -/
theorem contDiff_uncurry_iteratedTransferAmplitude
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (is : List (Fin d)) :
    ContDiff ℝ ∞ (Function.uncurry (iteratedTransferAmplitude b is)) := by
  exact orderedTransferAction_preserves _ (fun b => ContDiff ℝ ∞ (Function.uncurry b))
    (fun i _ hb => contDiff_uncurry_transferAmplitude hb i) is hb

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: every iterated
amplitude retains the original physical support box. -/
theorem supportedInCenteredBox_iteratedTransferAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (R : ℝ) (hb : ∀ ξ, SupportedInCenteredBox R (b ξ)) (is : List (Fin d)) (ξ) :
    SupportedInCenteredBox R (iteratedTransferAmplitude b is ξ) := by
  exact orderedTransferAction_preserves _ (fun b => ∀ ξ, SupportedInCenteredBox R (b ξ))
    (fun i b hb ξ => supportedInCenteredBox_transferAmplitude b R hb i ξ) is hb ξ

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: `r` transfers consume
`r` extra primitive physical derivatives and multiply the bound by `2 ^ r`. -/
theorem hasAmplitudeDerivativeBound_iteratedTransferAmplitude
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (is : List (Fin d)) (N : ℕ) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (N + is.length) A) :
    HasAmplitudeDerivativeBound (iteratedTransferAmplitude b is) N (2 ^ is.length * A) := by
  induction is generalizing N with
  | nil => simpa [iteratedTransferAmplitude, orderedTransferAction] using hA
  | cons i is ih =>
      have h := hasAmplitudeDerivativeBound_transferAmplitude (iteratedTransferAmplitude b is)
        (contDiff_iteratedTransferAmplitude b hb is) i N (2 ^ is.length * A)
        (ih (N + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hA))
      convert h using 1 <;>
        simp [iteratedTransferAmplitude, orderedTransferAction, pow_succ, mul_left_comm, mul_comm]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: enumerate the
primitive physical derivatives within a transfer amplitude, choosing output
or source position at each step, without permuting the ordered derivatives. -/
def physicalTransferWords : List (Fin d) → List (List (Fin (2 * d)))
  | [] => [[]]
  | i :: is =>
      (physicalTransferWords is).map (physicalOutputIndex i :: ·) ++
      (physicalTransferWords is).map (physicalSourceIndex i :: ·)

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: an amplitude with
`r` transfer steps is a sum of exactly `2 ^ r` primitive derivative terms. -/
theorem physicalTransferWords_length (is : List (Fin d)) :
    (physicalTransferWords is).length = 2 ^ is.length := by
  induction is with
  | nil => simp [physicalTransferWords]
  | cons i is ih => simp [physicalTransferWords, ih, pow_succ, Nat.mul_two]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: each primitive term
uses exactly one physical derivative per transfer step. -/
theorem physicalTransferWords_word_length (is : List (Fin d))
    (ws : List (Fin (2 * d))) (hws : ws ∈ physicalTransferWords is) :
    ws.length = is.length := by
  induction is generalizing ws with
  | nil => simpa [physicalTransferWords] using hws
  | cons i is ih =>
      simp only [physicalTransferWords, List.mem_append, List.mem_map] at hws
      rcases hws with ⟨vs, hvs, rfl⟩ | ⟨vs, hvs, rfl⟩ <;>
        simp only [List.length_cons, ih vs hvs]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: explicit primitive
expansion, including any additional ordered physical derivatives `js`.
This identity differentiates the full amplitude, including its masks. -/
theorem iteratedTransferAmplitude_primitive_expansion
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (is : List (Fin d))
    (js : List (Fin (2 * d))) (ξ : EuclideanSpace ℝ (Fin d)) :
    euclideanCoordinateDerivList js (iteratedTransferAmplitude b is ξ) =
      fun z => ((physicalTransferWords is).map fun ws =>
        euclideanCoordinateDerivList (js ++ ws) (b ξ) z).sum := by
  induction is generalizing js with
  | nil => simp [iteratedTransferAmplitude, orderedTransferAction, physicalTransferWords]
  | cons i is ih =>
      change euclideanCoordinateDerivList js (fun z =>
        euclideanCoordinateDerivList [physicalOutputIndex i]
            (iteratedTransferAmplitude b is ξ) z +
          euclideanCoordinateDerivList [physicalSourceIndex i]
            (iteratedTransferAmplitude b is ξ) z) = _
      rw [euclideanCoordinateDerivList_add
        (contDiff_euclideanCoordinateDerivList (contDiff_iteratedTransferAmplitude b hb is ξ) _)
        (contDiff_euclideanCoordinateDerivList (contDiff_iteratedTransferAmplitude b hb is ξ) _)]
      simp only [← euclideanCoordinateDerivList_append]
      simp only [ih]
      funext z
      simp [physicalTransferWords, List.map_append, List.map_map, List.sum_append,
        List.append_assoc, Function.comp_def]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the primitive order
of a branch is exactly its number of output derivatives minus its datum order. -/
theorem orderedTransferTerms_primitive_count (is : List (Fin d))
    (p : List (Fin d) × List (Fin d)) (hp : p ∈ orderedTransferTerms is)
    (ws : List (Fin (2 * d))) (hws : ws ∈ physicalTransferWords p.1) :
    ws.length = is.length - p.2.length := by
  rw [physicalTransferWords_word_length p.1 ws hws,
    orderedTransferTerms_transfer_count is p hp]

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: adding at most `N`
low physical derivatives costs at most `N + s - k` primitive derivatives. -/
theorem orderedTransferTerms_primitive_budget (is : List (Fin d))
    (p : List (Fin d) × List (Fin d)) (hp : p ∈ orderedTransferTerms is)
    (ws : List (Fin (2 * d))) (hws : ws ∈ physicalTransferWords p.1)
    (js : List (Fin (2 * d))) (N : ℕ) (hjs : js.length ≤ N) :
    (js ++ ws).length ≤ N + (is.length - p.2.length) := by
  rw [List.length_append, orderedTransferTerms_primitive_count is p hp ws hws]
  exact Nat.add_le_add_right hjs _

/-- `app:ch_regular_base:eq:graph-derivative-transfer`: the quantitative
amplitude bound for each branch with `k` datum derivatives. -/
theorem hasAmplitudeDerivativeBound_orderedTransferTerm
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) (is : List (Fin d))
    (p : List (Fin d) × List (Fin d)) (hp : p ∈ orderedTransferTerms is)
    (N : ℕ) (A : ℝ)
    (hA : HasAmplitudeDerivativeBound b (N + (is.length - p.2.length)) A) :
    HasAmplitudeDerivativeBound (iteratedTransferAmplitude b p.1) N
      (2 ^ (is.length - p.2.length) * A) := by
  rw [← orderedTransferTerms_transfer_count is p hp] at hA ⊢
  exact hasAmplitudeDerivativeBound_iteratedTransferAmplitude b hb p.1 N A hA

end JanetCartan.Pseudodifferential
