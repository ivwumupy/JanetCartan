module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Iteration

/-!
# Surviving differential commutator branches

The cancellation in `app:ch_background:eq:bg-commutator`. Ordered words retain
multiplicities, so repeated coordinate derivatives require no extra convention.
The consumer is the literal full-amplitude commutator in `Differential.Literal`.
-/

@[expose] public noncomputable section

namespace JanetCartan.Pseudodifferential

variable {ι Y : Type*}

/-- `app:ch_background:eq:bg-commutator`: derivative-transfer branches after
removing the unique branch with no physical amplitude derivative. -/
def differentialCommutatorTerms : List ι → List (List ι × List ι)
  | [] => []
  | i :: is =>
      (orderedTransferTerms is).map (fun p => (i :: p.1, p.2)) ++
      (differentialCommutatorTerms is).map (fun p => (p.1, i :: p.2))

/-- `app:ch_background:eq:bg-commutator`: the unique all-datum branch is
the only removed branch, with multiplicities preserved. -/
theorem differentialCommutatorTerms_length (is : List ι) :
    (differentialCommutatorTerms is).length + 1 = 2 ^ is.length := by
  induction is with
  | nil => simp [differentialCommutatorTerms]
  | cons i is ih =>
    simp only [differentialCommutatorTerms, List.length_append, List.length_map,
      orderedTransferTerms_length, List.length_cons, pow_succ]
    omega

/-- `app:ch_background:eq:bg-commutator`: every surviving branch is an actual
branch of the full derivative-transfer expansion. -/
theorem differentialCommutatorTerms_mem_transfer (is : List ι)
    (p : List ι × List ι) (hp : p ∈ differentialCommutatorTerms is) :
    p ∈ orderedTransferTerms is := by
  induction is generalizing p with
  | nil => simp [differentialCommutatorTerms] at hp
  | cons i is ih =>
    simp only [differentialCommutatorTerms, List.mem_append, List.mem_map] at hp
    simp only [orderedTransferTerms, List.mem_append, List.mem_map]
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr ⟨q, ih q hq, rfl⟩

/-- `app:ch_background:eq:bg-commutator`: every surviving term has at least
one physical derivative and at most `s - 1` datum derivatives. -/
theorem differentialCommutatorTerms_spec (is : List ι)
    (p : List ι × List ι) (hp : p ∈ differentialCommutatorTerms is) :
    0 < p.1.length ∧ p.1.length + p.2.length = is.length ∧
      p.2.length ≤ is.length - 1 := by
  have hcount := (orderedTransferTerms_spec is p
    (differentialCommutatorTerms_mem_transfer is p hp)).2.2
  have hpos : 0 < p.1.length := by
    induction is generalizing p with
    | nil => simp [differentialCommutatorTerms] at hp
    | cons i is ih =>
      simp only [differentialCommutatorTerms, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, _, rfl⟩ | ⟨q, hq, rfl⟩
      · simp
      · exact ih q hq (by simp only [List.length_cons] at hcount; omega)
  exact ⟨hpos, hcount, by omega⟩

/-- `app:ch_background:eq:bg-commutator`: cancellation of precisely the
all-datum branch, valid for any additive realization of the branch kernels. -/
theorem orderedTransferTerms_sum_eq_commutator_add [AddCommMonoid Y]
    (is : List ι) (F : List ι × List ι → Y) :
    ((orderedTransferTerms is).map F).sum =
      ((differentialCommutatorTerms is).map F).sum + F ([], is) := by
  induction is generalizing F with
  | nil => simp [orderedTransferTerms, differentialCommutatorTerms]
  | cons i is ih =>
    simp only [orderedTransferTerms, differentialCommutatorTerms, List.map_append,
      List.sum_append, List.map_map, Function.comp_def]
    rw [ih (fun p => F (p.1, i :: p.2))]
    exact (add_assoc _ _ _).symm

/-- `app:ch_background:eq:bg-commutator`: each primitive physical word in a
surviving transferred amplitude is nonempty, including source derivatives. -/
theorem differentialCommutatorTerms_physical_word_pos {d : ℕ}
    (is : List (Fin d)) (p : List (Fin d) × List (Fin d))
    (hp : p ∈ differentialCommutatorTerms is) (ws : List (Fin (2 * d)))
    (hws : ws ∈ physicalTransferWords p.1) : 0 < ws.length := by
  rw [physicalTransferWords_word_length p.1 ws hws]
  exact (differentialCommutatorTerms_spec is p hp).1

end JanetCartan.Pseudodifferential
