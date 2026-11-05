module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.Basic

/-!
# Lower-jet forcing in the higher variational equations

The partition step in `app:ch_regular_base:lem:buffered-interpolation` and
`app:lem:common-hamilton-phase` of `paper.tex`. The Faà di Bruno formula splits
into the single-block term `DV(f) Dʲf` and a sum involving only strictly lower
spatial derivatives of `f`. The parameter space is arbitrary, so it may include
external parameters and variable initial sections.

This file proves the algebraic splitting and its norm bound. Differentiating the
spatial jets with respect to time is a separate smoothness argument.
-/

@[expose] public noncomputable section

open scoped ContDiff
open Set

namespace JanetCartan.ODE

/-- `app:ch_regular_base:lem:buffered-interpolation`: The single-block partition of a positive
order, indexing the top variational term. -/
def singleBlockPartition (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint i _ j _ h := (h (Subsingleton.elim i j)).elim
  cover x := ⟨0, x, rfl⟩

/-- `app:ch_regular_base:lem:buffered-interpolation`: Every length-one partition is the
single-block partition. -/
lemma eq_singleBlockPartition_of_length_eq_one {n : ℕ} (hn : 0 < n)
    (p : OrderedFinpartition n) (hp : p.length = 1) : p = singleBlockPartition n hn := by
  have hs := CompositionBounds.sum_partSize p
  rcases p with ⟨l, sz, hsz, emb, hemb, hord, hdis, hcov⟩
  dsimp at hp hs
  subst l
  have hsz' : sz = fun _ ↦ n := by
    funext i
    simpa [Fin.sum_univ_one, Subsingleton.elim i (0 : Fin 1)] using hs
  subst sz
  have hemb' : emb = fun _ ↦ id := funext fun i ↦ (hemb i).eq_id
  subst emb
  rfl

/-- `app:ch_regular_base:lem:buffered-interpolation`: Every inner derivative order in a
remainder partition is strictly below the total order. -/
lemma partSize_lt_of_two_le_length {n : ℕ} (p : OrderedFinpartition n)
    (hp : 2 ≤ p.length) (i : Fin p.length) : p.partSize i < n := by
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin p.length)
    (by simpa only [Fintype.card_fin] using (show 1 < p.length by omega)) i
  exact (Finset.single_lt_sum hk (Finset.mem_univ _) (Finset.mem_univ _)
    (p.partSize_pos k) (fun _ _ _ ↦ Nat.zero_le _)).trans_eq
      (CompositionBounds.sum_partSize p)

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `app:ch_regular_base:lem:buffered-interpolation`: The explicit Faà di Bruno forcing sum over
partitions with at least two blocks. -/
def jetPartitionRemainder (j : ℕ) (V : E → E) (f : P → E) (x : P) : P [×j]→L[ℝ] E :=
  ∑ p : OrderedFinpartition j with 2 ≤ p.length,
    p.compAlongOrderedFinpartition (iteratedFDeriv ℝ p.length V (f x))
      (fun i ↦ iteratedFDeriv ℝ (p.partSize i) f x)

/-- `app:ch_regular_base:lem:buffered-interpolation`: The single-block chain-rule term is the
linearized vector field applied to the actual spatial jet. -/
lemma singleBlockPartition_term {j : ℕ} (hj : 0 < j) (V : E → E) (f : P → E) (x : P) :
    (singleBlockPartition j hj).compAlongOrderedFinpartition
      (iteratedFDeriv ℝ (singleBlockPartition j hj).length V (f x))
      (fun i ↦ iteratedFDeriv ℝ ((singleBlockPartition j hj).partSize i) f x) =
    (fderiv ℝ V (f x)).compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) := by
  ext v
  simp [OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, singleBlockPartition,
    iteratedFDeriv_one_apply]

/-- `app:ch_regular_base:lem:buffered-interpolation`: The positive-order chain rule splits into
its top variational term and the lower-jet partition sum. -/
lemma iteratedFDeriv_comp_eq_top_add_jetPartitionRemainder {j : ℕ}
    {V : E → E} {f : P → E} {x : P} (hj : 0 < j)
    (hV : ContDiffAt ℝ j V (f x)) (hf : ContDiffAt ℝ j f x) :
    iteratedFDeriv ℝ j (V ∘ f) x =
      (fderiv ℝ V (f x)).compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) +
        jetPartitionRemainder j V f x := by
  classical
  rw [iteratedFDeriv_comp hV hf le_rfl, FormalMultilinearSeries.taylorComp]
  let T := fun p : OrderedFinpartition j ↦ p.compAlongOrderedFinpartition
    (iteratedFDeriv ℝ p.length V (f x)) (fun i ↦ iteratedFDeriv ℝ (p.partSize i) f x)
  change ∑ p, T p = _
  have hfilter : Finset.univ.filter (fun p : OrderedFinpartition j ↦ ¬ 2 ≤ p.length) =
      {singleBlockPartition j hj} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact eq_singleBlockPartition_of_length_eq_one hj p (by have := p.length_pos hj; omega)
    · rintro rfl
      simp [singleBlockPartition]
  have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (OrderedFinpartition j))
    (fun p ↦ 2 ≤ p.length) T
  rw [hfilter, Finset.sum_singleton] at hsum
  rw [← hsum, add_comm]
  exact congrArg (· + jetPartitionRemainder j V f x) (singleBlockPartition_term hj V f x)

/-- `app:ch_regular_base:lem:buffered-interpolation`: The forcing norm is bounded by the
corresponding sum of products of derivative norms. -/
lemma norm_jetPartitionRemainder_le (j : ℕ) (V : E → E) (f : P → E) (x : P) :
    ‖jetPartitionRemainder j V f x‖ ≤
      ∑ p : OrderedFinpartition j with 2 ≤ p.length,
        ‖iteratedFDeriv ℝ p.length V (f x)‖ *
          ∏ i, ‖iteratedFDeriv ℝ (p.partSize i) f x‖ := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun p _ ↦ p.norm_compAlongOrderedFinpartition_le _ _

/-- `app:ch_regular_base:lem:buffered-interpolation`: The explicit lower-jet sum equals the
composition jet minus its top linear term. -/
lemma jetPartitionRemainder_eq_sub {j : ℕ} {V : E → E} {f : P → E} {x : P}
    (hj : 0 < j) (hV : ContDiffAt ℝ j V (f x)) (hf : ContDiffAt ℝ j f x) :
    jetPartitionRemainder j V f x = iteratedFDeriv ℝ j (V ∘ f) x -
      (fderiv ℝ V (f x)).compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) := by
  rw [iteratedFDeriv_comp_eq_top_add_jetPartitionRemainder hj hV hf, add_sub_cancel_left]

/-- `app:ch_regular_base:lem:buffered-interpolation`: There is no lower-jet partition forcing at
order one. -/
lemma jetPartitionRemainder_one (V : E → E) (f : P → E) (x : P) :
    jetPartitionRemainder 1 V f x = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have := (Finset.mem_filter.mp hp).2
  have := p.length_le
  omega

/-- `app:ch_regular_base:lem:buffered-interpolation`: The linear coefficient for the jet
evolution: zero at order zero, and the vector-field derivative at positive orders. -/
def jetEvolutionCoefficient (j : ℕ) (V : E → E) (z : E) : E →L[ℝ] E :=
  if j = 0 then 0 else fderiv ℝ V z

/-- `app:ch_regular_base:lem:buffered-interpolation`: The canonical forcing for all jet orders,
using the original vector field at order zero and the lower-jet sum at positive orders. -/
def jetEvolutionForcing (j : ℕ) (V : E → E) (f : P → E) (x : P) : P [×j]→L[ℝ] E :=
  if j = 0 then iteratedFDeriv ℝ j (V ∘ f) x else jetPartitionRemainder j V f x

/-- `app:ch_regular_base:lem:buffered-interpolation`: The chain-rule identity in the
coefficient-plus-forcing form used by `HasJetEvolutionOn`, including order zero. -/
lemma iteratedFDeriv_comp_eq_jetEvolution {j : ℕ} {V : E → E} {f : P → E} {x : P}
    (hV : ContDiffAt ℝ j V (f x)) (hf : ContDiffAt ℝ j f x) :
    iteratedFDeriv ℝ j (V ∘ f) x =
      (jetEvolutionCoefficient j V (f x)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j f x) + jetEvolutionForcing j V f x := by
  by_cases hj : j = 0
  · subst j
    simp [jetEvolutionCoefficient, jetEvolutionForcing]
    ext
    simp
  · simpa [jetEvolutionCoefficient, jetEvolutionForcing, hj] using
      iteratedFDeriv_comp_eq_top_add_jetPartitionRemainder (Nat.pos_of_ne_zero hj) hV hf

/-- `app:ch_regular_base:lem:buffered-interpolation`: The order-zero forcing is the original
vector field under the canonical zero-multilinear-map identification. -/
lemma jetEvolutionForcing_zero (V : E → E) (f : P → E) (x : P) :
    jetEvolutionForcing 0 V f x =
      (continuousMultilinearCurryFin0 ℝ P E).symm (V (f x)) := by
  simp [jetEvolutionForcing, iteratedFDeriv_zero_eq_comp]

/-- `app:ch_regular_base:lem:buffered-interpolation`: The order-zero forcing norm is the norm of
the original vector field. -/
lemma norm_jetEvolutionForcing_zero (V : E → E) (f : P → E) (x : P) :
    ‖jetEvolutionForcing 0 V f x‖ = ‖V (f x)‖ := by
  simp [jetEvolutionForcing_zero]

/-- `app:ch_regular_base:lem:buffered-interpolation`: At every positive order the canonical
forcing obeys the lower-jet partition norm bound. -/
lemma norm_jetEvolutionForcing_le {j : ℕ} (hj : 0 < j)
    (V : E → E) (f : P → E) (x : P) :
    ‖jetEvolutionForcing j V f x‖ ≤
      ∑ p : OrderedFinpartition j with 2 ≤ p.length,
        ‖iteratedFDeriv ℝ p.length V (f x)‖ *
          ∏ i, ‖iteratedFDeriv ℝ (p.partSize i) f x‖ := by
  simpa [jetEvolutionForcing, hj.ne'] using norm_jetPartitionRemainder_le j V f x

end JanetCartan.ODE
