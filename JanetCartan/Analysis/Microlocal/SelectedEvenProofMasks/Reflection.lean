module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Nested
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.CanonicalBounds

/-!
# Physical covector reflection for the selected proof masks

The relation used to choose the masks in `app:ch_regular:lem:finite-chain`
must contain both the actual selected relation and its covector reflection.
The selected finite chart relation itself need not be invariant. These
constructions concern only proof masks; the actual operators are unchanged.
Consumer: the even nested construction supplying `hieven` and `hoeven` to
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks ProtectedFlow FiniteChain.Graph

variable {d : ℕ}
local notation "P" => Euclidean (d + 1) × Euclidean (d + 1)

/-- Physical covector reflection fixes the base and is an isometry for the
actual phase-space norm (`app:ch_regular:lem:finite-chain`). -/
def physicalCovectorReflection : P ≃ₗᵢ[ℝ] P :=
  { toLinearEquiv := (LinearEquiv.refl ℝ (Euclidean (d + 1))).prodCongr
      (LinearEquiv.neg ℝ)
    norm_map' := by intro p; change ‖(p.1, -p.2)‖ = ‖p‖; simp [Prod.norm_def] }

/-- Reflection acts on the covector only (`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem physicalCovectorReflection_apply (p : P) :
    physicalCovectorReflection p = (p.1, -p.2) := rfl

/-- The physical reflection is involutive (`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem physicalCovectorReflection_involutive (p : P) :
    physicalCovectorReflection (physicalCovectorReflection p) = p := by simp

/-- A closed shoulder of a symmetric compact is symmetric, with its original
radius. This is used before selecting the cutoffs
(`app:ch_regular:lem:finite-chain`). -/
theorem physicalCovectorReflection_mem_cthickening
    {K : Set P} (hK : IsCompact K)
    (hKsym : ∀ p ∈ K, physicalCovectorReflection p ∈ K)
    {δ : ℝ} (hδ : 0 ≤ δ) {p : P} (hp : p ∈ cthickening δ K) :
    physicalCovectorReflection p ∈ cthickening δ K := by
  rw [hK.cthickening_eq_biUnion_closedBall hδ] at hp ⊢
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp hp
  exact mem_iUnion₂.mpr ⟨physicalCovectorReflection q, hKsym q hq,
    by simpa only [mem_closedBall, physicalCovectorReflection.dist_map] using hpq⟩

/-- Enlarge the proof relation explicitly, without assuming symmetry of the
arbitrary selected chart family (`app:ch_regular:lem:finite-chain`). -/
def reflectedProofRelation (R : P → P → Prop) (p q : P) : Prop :=
  R p q ∨ R (physicalCovectorReflection p) (physicalCovectorReflection q)

/-- Every actual selected step remains a proof-relation step
(`app:ch_regular:lem:finite-chain`). -/
theorem subset_reflectedProofRelation {R : P → P → Prop} {p q : P}
    (hpq : R p q) : reflectedProofRelation R p q := Or.inl hpq

/-- The enlarged relation is invariant even when the actual chart relation
is not (`app:ch_regular:lem:finite-chain`). -/
@[simp] theorem reflectedProofRelation_reflection (R : P → P → Prop) (p q : P) :
    reflectedProofRelation R (physicalCovectorReflection p) (physicalCovectorReflection q) ↔
      reflectedProofRelation R p q := by
  simp only [reflectedProofRelation, physicalCovectorReflection_involutive, or_comm]

/-- Compactness of the reflected proof relation follows from compactness of
the same actual relation, including its closed supports and whole segments
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_reflectedProofRelation {R : P → P → Prop}
    (hR : IsCompact {pq : P × P | R pq.1 pq.2}) :
    IsCompact {pq : P × P | reflectedProofRelation R pq.1 pq.2} := by
  let e : (P × P) ≃ₜ (P × P) :=
    physicalCovectorReflection.toHomeomorph.prodCongr physicalCovectorReflection.toHomeomorph
  exact hR.union (e.isCompact_preimage.mpr hR)

/-- The complete buffered images of the reflected proof relation are
symmetric whenever the initial compact is symmetric. Diagonal steps and
every closed shoulder are included (`app:ch_regular:lem:finite-chain`). -/
theorem bufferedReachableAt_reflectedProofRelation_symmetric
    {R : P → P → Prop} (hR : IsCompact {pq : P × P | R pq.1 pq.2})
    {S : Set P} (hS : IsCompact S)
    (hSsym : ∀ p ∈ S, physicalCovectorReflection p ∈ S)
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ∀ p ∈ bufferedReachableAt (reflectedProofRelation R) S δ n,
      physicalCovectorReflection p ∈ bufferedReachableAt (reflectedProofRelation R) S δ n := by
  induction n with
  | zero => exact hSsym
  | succ n ih =>
    rintro q ⟨p, hp, hc⟩
    cases hc with
    | tail hpq hc =>
      cases hc
      apply mem_bufferedReachableAt_succ_of_step
        (physicalCovectorReflection_mem_cthickening
          (isCompact_bufferedReachableAt (isCompact_reflectedProofRelation hR) hS δ n)
          ih hδ hp)
      rcases hpq with rfl | hpq
      · exact Or.inl rfl
      · exact Or.inr ((reflectedProofRelation_reflection R p q).mpr hpq)

/-- The physical reflection commutes with the SAME canonical coordinate
conversion; no independent canonical mask is chosen
(`app:ch_regular:lem:finite-chain`). -/
theorem adaptedPhaseEquiv_physicalCovectorReflection
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d)) (p : P) :
    adaptedPhaseEquiv e (physicalCovectorReflection p) =
      physicalCovectorReflection (adaptedPhaseEquiv e p) := by
  change (e.symm (RegularSector.Characteristic.coordinateSplit 0 p.1),
    e.symm (RegularSector.Characteristic.coordinateSplit 0 (-p.2))) =
      (e.symm (RegularSector.Characteristic.coordinateSplit 0 p.1),
        -e.symm (RegularSector.Characteristic.coordinateSplit 0 p.2))
  simp only [map_neg]

/-- The literal canonical pullback of an even physical proof mask is even.
This supplies the real/adjoint branches of `app:ch_regular:eq:chain-tail`. -/
theorem canonicalProofLocalizer_even
    (e : Euclidean (d + 1) ≃L[ℝ] (ℝ × Euclidean d))
    {m : LocalizerSymbol (d + 1)} (hm : ∀ y ξ, m (y, -ξ) = m (y, ξ)) :
    ∀ y ξ, canonicalProofLocalizer e m (y, -ξ) = canonicalProofLocalizer e m (y, ξ) := by
  intro y ξ
  change m (adaptedPhaseEquiv e (physicalCovectorReflection (y, ξ))) = _
  rw [adaptedPhaseEquiv_physicalCovectorReflection]
  exact hm _ _

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
