module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Terms

/-!
# Counting the actual annular carrier branches

The finite sums in `new:eq:carrier-ibp` retain their multiplicities and original
source/parameter words. These elementary deductions supply the weighted sum
in `app:ch_response:eq:direct-envelope-profile`; they assert no realization.
-/

@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open CompactTransfer Pseudodifferential
variable {n : ℕ} {P M ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [Fintype ι]

/-- Exactly `card ι + 2` terms occur at each literal IBP step
(`new:eq:carrier-ibp`), including terms whose datum derivative vanishes. -/
theorem jointTransferChildren_length
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (e : Euclidean n × P)
    (t : JointTransferTerm n P M ι) :
    (jointTransferChildren b e t).length = Fintype.card ι + 2 := by
  simp [jointTransferChildren, Nat.add_comm, Nat.add_left_comm]

/-- The literal branch list, with multiplicities, has exponential finite
length. Consumer: the weighted annular Sobolev sum following `new:eq:carrier-ibp`. -/
theorem jointTransferTerms_length
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (es : List (Euclidean n × P)) :
    (jointTransferTerms (M := M) b es).length = (Fintype.card ι + 2) ^ es.length := by
  induction es with
  | nil => simp [jointTransferTerms, orderedTransferAction]
  | cons e es ih =>
    change ((jointTransferTerms (M := M) b es).flatMap (jointTransferChildren b e)).length = _
    simp only [List.length_flatMap, jointTransferChildren_length, List.map_const',
      List.sum_replicate, smul_eq_mul, ih, List.length_cons, pow_succ]

/-- The datum order cannot exceed the shared total order. The stronger exact
identity remains `jointTransferTerms_order_budget` (`new:eq:carrier-ibp`). -/
theorem jointTransferTerms_datum_length_le
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (es : List (Euclidean n × P))
    (t : JointTransferTerm n P M ι) (ht : t ∈ jointTransferTerms b es) :
    t.datumWord.length ≤ es.length := by
  have := jointTransferTerms_order_budget b es t ht
  omega

/-- The coefficient power is exactly total order minus ORIGINAL datum order,
not the order of an auxiliary projected envelope (`new:eq:carrier-ibp`). -/
theorem jointTransferTerms_amplitudeCost_eq
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (es : List (Euclidean n × P))
    (t : JointTransferTerm n P M ι) (ht : t ∈ jointTransferTerms b es) :
    t.amplitude.derivativeCost = es.length - t.datumWord.length := by
  have := jointTransferTerms_order_budget b es t ht
  omega

/-- Pure output differentiation produces only unit-bounded source directions
and zero parameter directions in the original datum. Consumer: the actual
datum-word Fourier bound for `app:ch_response:eq:direct-envelope-profile`. -/
theorem jointTransferTerms_spatial_datum_directions
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (es : List (Euclidean n × P)) (he : ∀ e ∈ es, e.2 = 0)
    (t : JointTransferTerm n P M ι) (ht : t ∈ jointTransferTerms b es) :
    ∀ v ∈ t.datumWord, ‖v.1‖ ≤ 1 ∧ v.2 = 0 := by
  induction es generalizing t with
  | nil =>
    simp only [jointTransferTerms, orderedTransferAction, List.mem_singleton] at ht
    subst t
    simp [initialJointTransferTerm]
  | cons e es ih =>
    change t ∈ (jointTransferTerms b es).flatMap (jointTransferChildren b e) at ht
    obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
    have hu' := ih (fun v hv => he v (List.mem_cons_of_mem e hv)) u hu
    have he' := he e (List.mem_cons_self)
    simp only [jointTransferChildren, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | rfl | ⟨i, _, rfl⟩
    · exact hu'
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · simpa using And.intro (show (0 : ℝ) ≤ 1 by norm_num) he'
      · exact hu' v hv
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨(WithLp.norm_fst_le _ (b i)).trans (b.norm_eq_one i).le, rfl⟩
      · exact hu' v hv

/-- Branch-dependent constants have one common bound for the finitely many
coordinate words through a fixed order (with any fixed parameter suffix).
The bound is chosen before scales and varying fields. Consumer: the uniform
branch premise of the all-data and joint Sobolev deductions in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem exists_jointTransferTerms_uniform_constant
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (s : ℕ)
    (directions : Fin n → Euclidean n × P) (suffix : List (Euclidean n × P))
    (Cbranch : JointTransferTerm n P M ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ is : List (Fin n), is.length ≤ s →
      ∀ t ∈ jointTransferTerms b (is.map directions ++ suffix), Cbranch t ≤ C := by
  let W : Set (List (Fin n)) := ⋃ k ∈ Set.Iic s,
    Set.range (fun v : Fin k → Fin n => List.ofFn v)
  have hW : W.Finite := (Set.finite_Iic s).biUnion
    (fun k _ => Set.finite_range (fun v : Fin k → Fin n => List.ofFn v))
  let A : Set (JointTransferTerm n P M ι) := ⋃ is ∈ W,
    {t | t ∈ jointTransferTerms b (is.map directions ++ suffix)}
  have hA : A.Finite := hW.biUnion (fun is _ =>
    (jointTransferTerms (M := M) b (is.map directions ++ suffix)).finite_toSet)
  obtain ⟨C, hC⟩ := (hA.image Cbranch).exists_le
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro is hi t ht
  have his : is ∈ W := Set.mem_iUnion.mpr ⟨is.length,
    Set.mem_iUnion.mpr ⟨hi, ⟨is.get, List.ofFn_get is⟩⟩⟩
  exact (hC _ ⟨t, Set.mem_iUnion.mpr ⟨is, Set.mem_iUnion.mpr ⟨his, ht⟩⟩, rfl⟩).trans
    (le_max_right _ _)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
