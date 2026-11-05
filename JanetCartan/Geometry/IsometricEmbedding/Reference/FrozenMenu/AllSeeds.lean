module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FiveDimensional

/-!
# Pointwise carrier seeds in every dimension at least five

Steps 1–3 of `app:ch_seed:prop:seed-frozen-menu`, including all permutations of
the exceptional five-dimensional node. The explicit carrier from
`app:ch_seed:eq:seed-five-node-carrier` supplies incidence, detection, and
bad-normal avoidance; the general reciprocal transversality theorem supplies
the final field of `CarrierSeed`.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

open CubeCarrier
open FiveDimensional (reindex carrier reciprocalCarrier node)

private theorem quadratic_eq_five (x : Euclidean 5) :
    quadratic x = FiveDimensional.quadratic x := by
  ext i
  norm_num [quadratic, FiveDimensional.quadratic, cubeCoefficient]

private theorem reciprocal_permuted_carrier (σ : Equiv.Perm (Fin 5)) :
    reciprocal (reindex σ carrier) = reindex σ reciprocalCarrier := by
  ext i
  change (carrier (σ i))⁻¹ = reciprocalCarrier (σ i)
  rw [FiveDimensional.carrier_eq_inv, inv_inv]

private theorem reciprocal_permuted_reciprocalCarrier (σ : Equiv.Perm (Fin 5)) :
    reciprocal (reindex σ reciprocalCarrier) = reindex σ carrier := by
  ext i
  exact (FiveDimensional.carrier_eq_inv (σ i)).symm

private theorem normal_permuted_carrier (σ : Equiv.Perm (Fin 5)) :
    normal (reindex σ carrier) = reindex σ (FiveDimensional.quadratic reciprocalCarrier) := by
  rw [normal, reciprocal_permuted_carrier, quadratic_eq_five,
    FiveDimensional.quadratic_reindex]

/-- The explicit carrier, after any permutation, supplies every seed field at
any nonzero point on the corresponding node line
(`app:ch_seed:prop:seed-frozen-menu`, Steps 2–3). -/
theorem carrierSeed_permuted_five_node (σ : Equiv.Perm (Fin 5))
    {t : ℝ} (ht : t ≠ 0) {s : Euclidean 5} (hs : s ≠ 0)
    (hker : (cubePencil (t • reindex σ node)).mulVec (fun i ↦ s i) = 0) :
    CarrierSeed (t • reindex σ node) s (reindex σ carrier) := by
  obtain ⟨hinc, hdet⟩ := FiveDimensional.permuted_node_detection σ t ht s hker hs
  have hk : t • reindex σ node ≠ 0 := by
    intro h
    have hi := congrArg (fun x : Euclidean 5 ↦ x (σ.symm 0)) h
    simp [reindex, node, ht] at hi
  refine {
    coordinates_ne_zero := fun i ↦ (FiveDimensional.carrier_coordinates_ne_zero (σ i)).1
    characteristic := (FiveDimensional.carrier_reindex_characteristic σ).1
    normal_ne_zero := ?_
    incident := ?_
    detects := ?_
    triple_witness := ?_
    pair_sum_witness := ?_
    transverse := ?_
  }
  · rw [normal_permuted_carrier]
    intro h
    apply FiveDimensional.carrier_normals_ne_zero.2
    ext i
    simpa [reindex] using congrArg (fun x : Euclidean 5 ↦ x (σ.symm i)) h
  · simpa only [incidence, normal, reciprocal_permuted_carrier, quadratic_eq_five] using hinc
  · simpa only [quadratic_eq_five] using hdet
  · intro i j l
    obtain ⟨x, hi, hj, hl, hx⟩ := FiveDimensional.normal_triple_witness (σ i) (σ j) (σ l)
    refine ⟨reindex σ x, hi, hj, hl, ?_⟩
    rwa [normal_permuted_carrier, FiveDimensional.pairing_reindex]
  · intro i j
    obtain ⟨x, hi, hj, hsum, hx⟩ := FiveDimensional.normal_pair_sum_witness (σ i) (σ j)
    refine ⟨reindex σ x, hi, hj, ?_, ?_⟩
    · rwa [FiveDimensional.sum_reindex]
    · rwa [normal_permuted_carrier, FiveDimensional.pairing_reindex]
  · have hdetect : (∑ i, s i * quadratic (reciprocal (reindex σ reciprocalCarrier)) i) ≠ 0 := by
      simpa only [reciprocal_permuted_reciprocalCarrier, quadratic_eq_five] using hdet
    change ∃ e : Euclidean 5, fderiv ℝ cubeDeterminant (reindex σ carrier) e = 0 ∧
      fderiv ℝ (fun x : Euclidean 5 ↦ ∑ i, (t • reindex σ node) i *
        quadratic (reciprocal x) i) (reindex σ carrier) e ≠ 0
    simpa only [reciprocal_permuted_reciprocalCarrier] using
      exists_transverse_carrier_tangent hk hs
        (fun i ↦ (FiveDimensional.carrier_coordinates_ne_zero (σ i)).2) hker
        (FiveDimensional.carrier_reindex_characteristic σ).2 hdetect

/-- Pointwise selection on every five-dimensional node line
(`app:ch_seed:prop:seed-frozen-menu`, Step 2). -/
theorem exists_carrierSeed_of_five_node {k s : Euclidean 5}
    (hk : k ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0)
    (hnode : ∃ a b : Fin 5, a ≠ b ∧ ∃ t : ℝ, k = t • cubeVector a b) :
    ∃ ξ, CarrierSeed k s ξ := by
  obtain ⟨a, b, hab, t, rfl⟩ := hnode
  obtain ⟨σ, hσ⟩ := FiveDimensional.exists_node_reindex a b hab
  have ht : t ≠ 0 := by
    intro ht
    apply hk
    simp [ht]
  rw [← hσ] at hker ⊢
  exact ⟨reindex σ carrier, carrierSeed_permuted_five_node σ ht hs hker⟩

/-- Complete pointwise carrier selection for
`app:ch_seed:prop:seed-frozen-menu`, Steps 1–3. Every nonzero covector and
nonzero stress in its pencil kernel admit a detecting, incident carrier with
all normal-avoidance witnesses and a transverse characteristic tangent.
There are no exceptional node directions or additional geometric premises. -/
theorem exists_carrierSeed {n : ℕ} (hn : 5 ≤ n)
    {k s : Euclidean n} (hk : k ≠ 0) (hs : s ≠ 0)
    (hker : (cubePencil k).mulVec (fun i ↦ s i) = 0) :
    ∃ ξ, CarrierSeed k s ξ := by
  classical
  by_cases hn5 : n = 5
  · subst n
    by_cases hnode : ∃ a b : Fin 5, a ≠ b ∧ ∃ t : ℝ, k = t • cubeVector a b
    · exact exists_carrierSeed_of_five_node hk hs hker hnode
    · exact exists_carrierSeed_of_nonexceptional hn hk hs hker (fun _ ↦ hnode)
  · exact exists_carrierSeed_of_nonexceptional hn hk hs hker (fun h ↦ (hn5 h).elim)

end JanetCartan.FrozenMenu
