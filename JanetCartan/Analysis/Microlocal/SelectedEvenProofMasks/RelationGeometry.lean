module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.SymbolReflection
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.ReachableBounds

/-!
# Primitive geometry of the reflected selected relation

The actual finite family supplies both base and frequency bounds, and the
literal root equation supplies zero energy. Reflection preserves all three
on the SAME coefficient field. These are the inputs to the uniform buffered
propagation induction for `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks RegularSector.Characteristic EvolutionIntegratedLocalization
open ProtectedFlow ActualCarriers

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => E × E

/-- The complete original reachable set, with all diagonal steps, is included
in that of the reflected proof relation (`app:ch_regular:lem:finite-chain`). -/
theorem reachableAt_subset_reflectedProofRelation
    (R : P → P → Prop) (S : Set P) (n : ℕ) :
    reachableAt R S n ⊆ reachableAt (reflectedProofRelation R) S n := by
  rintro q ⟨p, hp, hc⟩
  refine ⟨p, hp, ?_⟩
  clear hp
  induction hc with
  | refl p => exact .refl p
  | tail hstep _ ih => exact .tail (hstep.imp_right Or.inl) ih

/-- Reflection retains both physical endpoint bases in the original compact
buffer, for both literal orientations (`app:ch_regular:lem:finite-chain`). -/
theorem reflectedProofRelation_base_mem_of_root_buffer {J : Type*}
    {i : J → Fin (d + 1)} {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : J → Set (RootState (Euclidean d))} {W B : Set E}
    {χsource χout : J → E → ℂ} {Δ : ℝ}
    (hbase : ∀ j v, v ∈ U j ∪ K j → (coordinateSplit (i j)).symm (v.1, v.2.1) ∈ B)
    {p q : P}
    (hpq : reflectedProofRelation (physicalDirectRelation i h Φ U K W χsource χout Δ) p q) :
    p.1 ∈ B ∧ q.1 ∈ B := by
  have hactual {p q : P} (hpq : physicalDirectRelation i h Φ U K W χsource χout Δ p q) :
      p.1 ∈ B ∧ q.1 ∈ B := by
    obtain ⟨j, backward, u, v, huv, rfl, rfl⟩ := hpq
    exact maskedZeroEnergyRelation_base_mem_of_root_buffer (i j) (hbase j) huv
  rcases hpq with hpq | hpq
  · exact hactual hpq
  · exact hactual (p := physicalCovectorReflection p) (q := physicalCovectorReflection q) hpq

/-- Common annular endpoints for the original relation also control its
reflection, before roots, flows, coefficients or histories vary. These are
the SAME primitive section constants (`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_reflectedProofRelation_bounds_of_section
    {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (ε G : J → ℝ) (hG : ∀ j, 0 ≤ G j) :
    ∃ c₀ > (0 : ℝ), ∃ C₀ > (0 : ℝ),
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K : J → Set (RootState (Euclidean d))) (W : Set E)
        (χsource χout : J → E → ℂ) (Δ : ℝ),
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ closedBall (η₀ j) (ε j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        ∀ p q, reflectedProofRelation (physicalDirectRelation i h Φ U K W χsource χout Δ) p q →
          (c₀ ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ C₀) ∧ (c₀ ≤ ‖q.2‖ ∧ ‖q.2‖ ≤ C₀) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, hb⟩ :=
    exists_uniform_physicalDirectRelation_bounds_of_section ℓ η₀ ε G hG
  refine ⟨c₀, hc₀, C₀, hC₀, ?_⟩
  intro i h Φ U K W χsource χout Δ hprimitive p q hpq
  rcases hpq with hpq | hpq
  · exact hb i h Φ U K W χsource χout Δ hprimitive p q hpq
  · simpa only [physicalCovectorReflection_apply, norm_neg] using
      hb i h Φ U K W χsource χout Δ hprimitive _ _ hpq

/-- Both branches of the reflected proof relation lie on the characteristic
set of the original normalized coefficient field. The literal root equation,
flow and whole-segment restriction prove this; zero energy is not assumed of
the desired propagated source (`app:ch_regular:lem:finite-chain`). -/
theorem reflectedProofRelation_source_energy {J : Type*}
    {i : J → Fin (d + 1)} {Q : E → Fin (d + 1) → MetricTensor (d + 1)}
    {h : J → RootState (Euclidean d) → ℝ}
    {Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K D : J → Set (RootState (Euclidean d))} {W : Set E}
    {χsource χout : J → E → ℂ} {Δ : ℝ}
    (hKD : ∀ j, K j ⊆ D j) (hi : ∀ j v, v ∈ U j → Φ j (v, 0) = v)
    (hode : ∀ j v, v ∈ U j → ∀ t ∈ Icc 0 Δ,
      HasDerivAt (fun s ↦ Φ j (v, s)) (rootHamiltonField (h j) (Φ j (v, t))) t)
    (hroot : ∀ j v, v ∈ D j →
      determinant (Q ((coordinateSplit (i j)).symm (v.1, v.2.1)))
        ((coordinateSplit (i j)).symm (h j v, v.2.2)) = 0)
    {p q : P}
    (hpq : reflectedProofRelation (physicalDirectRelation i h Φ U K W χsource χout Δ) p q) :
    normalizedSymbol Q p = 0 := by
  have hactual {p q : P} (hpq : physicalDirectRelation i h Φ U K W χsource χout Δ p q) :
      normalizedSymbol Q p = 0 := by
    obtain ⟨j, backward, u, v, huv, rfl, rfl⟩ := hpq
    exact completePencilRootSegment_source_energy (coordinateSplit (i j)) (hroot j)
      (maskedZeroEnergyRelation_completePencilRootSegment (hKD j) (hi j) (hode j) huv)
  rcases hpq with hpq | hpq
  · exact hactual hpq
  · exact (normalizedSymbol_reflection_eq_zero_iff Q p).mp (hactual hpq)

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
