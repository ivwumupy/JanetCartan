module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Simultaneous selection of a tangent three-frame

The finite linear-algebra selection in Step 3 of
`app:ch_seed:prop:seed-frozen-menu` of `paper.tex`. Successively avoiding
finitely many proper subspaces gives three columns whose images are independent
under every projection, with nonzero incidence on the first column.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

open Module

/-- The simultaneous three-frame selection of
`app:ch_seed:prop:seed-frozen-menu`, Step 3: finitely many maps of rank at least
three admit a common three-frame on which each map is injective, and a given
nonzero functional is nonzero on the first column. The index family may be empty.

At each stage, avoid the functional's kernel and the inverse images of the spans
of the previously chosen projected columns. These subspaces are proper because
fewer than three columns cannot span any of the maps' ranges. -/
theorem exists_threeFrame_of_rank_ge_three
    {ι : Type*} [Finite ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    [∀ i, FiniteDimensional ℝ (W i)]
    (p : ∀ i, V →ₗ[ℝ] W i) (f : V →ₗ[ℝ] ℝ)
    (hf : f ≠ 0) (hp : ∀ i, 3 ≤ finrank ℝ (p i).range) :
    ∃ B : Euclidean 3 →ₗ[ℝ] V,
      f (B (EuclideanSpace.single 0 1)) ≠ 0 ∧
      ∀ i, Function.Injective ((p i).comp B) := by
  classical
  have hframes : ∀ n : ℕ, n ≤ 3 → ∃ v : Fin n → V,
      (∀ j, f (v j) ≠ 0) ∧ ∀ i, LinearIndependent ℝ (fun j => p i (v j)) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨Fin.elim0, fun j => Fin.elim0 j, fun _ => linearIndependent_empty_type⟩
    | succ n ih =>
      intro hn
      obtain ⟨v, hvf, hvp⟩ := ih (by omega)
      let q : Option ι → Submodule ℝ V
        | none => f.ker
        | some i => (Submodule.span ℝ (Set.range fun j => p i (v j))).comap (p i)
      have hq : ∀ i, q i ≠ ⊤ := by
        intro i
        cases i with
        | none => exact fun h => hf (LinearMap.ker_eq_top.mp h)
        | some i =>
          intro h
          have hle : (p i).range ≤ Submodule.span ℝ (Set.range fun j => p i (v j)) := by
            rintro _ ⟨x, rfl⟩
            change x ∈ q (some i)
            rw [h]
            trivial
          have hdim := Submodule.finrank_mono hle
          have hspan := finrank_range_le_card (R := ℝ) (fun j => p i (v j))
          simp only [Fintype.card_fin, Set.finrank] at hspan
          have := hp i
          omega
      obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top q hq
      refine ⟨Fin.cons x v, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact hx none
        · exact hvf j
      · intro i
        have hcomp :
            (fun j : Fin (n + 1) => p i ((Fin.cons x v : Fin (n + 1) → V) j)) =
            Fin.cons (p i x) (fun j => p i (v j)) := by
          funext j
          exact Fin.cases rfl (fun _ => rfl) j
        rw [hcomp, linearIndependent_finCons]
        exact ⟨hvp i, hx (some i)⟩
  obtain ⟨v, hvf, hvp⟩ := hframes 3 le_rfl
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let B : Euclidean 3 →ₗ[ℝ] V := b.constr ℝ v
  have hB : ∀ j, B (EuclideanSpace.single j 1) = v j := by
    intro j
    change (b.constr ℝ v) (EuclideanSpace.single j 1) = v j
    rw [← EuclideanSpace.basisFun_apply (ι := Fin 3) (𝕜 := ℝ)]
    exact b.constr_basis ℝ v j
  refine ⟨B, ?_, ?_⟩
  · rw [hB]
    exact hvf 0
  · intro i
    have heq : (p i).comp B = b.constr ℝ (fun j => p i (v j)) := by
      apply b.ext
      intro j
      simp [B]
    rw [heq]
    exact b.injective_constr_of_linearIndependent (hvp i)

end JanetCartan.FrozenMenu
