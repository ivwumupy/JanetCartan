module

public import JanetCartan.Analysis.Microlocal.SelectedEvenProofMasks.Reflection

/-!
# Source geometry for even physical masks

An even plateau necessarily includes the reflected source. Keep the original
buffer `V`, explicitly recording the necessary geometric inclusion instead of
silently replacing it. Symmetry of the protected angular sets is produced by
`exists_constructed_signed_uniform_protection_with_graph_bounds`.
Consumer: the source step of `app:ch_regular:lem:finite-chain` and the real
restriction factors in `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks

open ProtectedMasks ProtectedFlow FiniteChain.Graph

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => E × E

/-- The same original compact together with its reflected copy, used only
to choose proof masks (`app:ch_regular:lem:finite-chain`). -/
def physicalSymmetricHull (S : Set P) : Set P := S ∪ physicalCovectorReflection '' S

/-- The signed source hull is compact before any varying coefficient field
is chosen (`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_physicalSymmetricHull {S : Set P} (hS : IsCompact S) :
    IsCompact (physicalSymmetricHull S) :=
  hS.union (hS.image physicalCovectorReflection.continuous)

/-- The source hull is invariant under the physical reflection
(`app:ch_regular:lem:finite-chain`). -/
theorem physicalSymmetricHull_reflection (S : Set P) :
    ∀ p ∈ physicalSymmetricHull S, physicalCovectorReflection p ∈ physicalSymmetricHull S := by
  rintro p (hp | ⟨q, hq, rfl⟩)
  · exact Or.inr ⟨p, hp, rfl⟩
  · exact Or.inl (by simpa only [physicalCovectorReflection_involutive] using hq)

/-- Symmetric angular sets have symmetric interiors. Applied to the SAME
initialized `Omega` and `Gamma` (`app:ch_regular:lem:finite-chain`). -/
theorem neg_mem_interior_of_symmetric {A : Set E}
    (hA : ∀ ξ ∈ A, -ξ ∈ A) {ξ : E} (hξ : ξ ∈ interior A) : -ξ ∈ interior A := by
  have heq : Neg.neg ⁻¹' A = A := by
    ext v
    exact ⟨fun h ↦ by simpa only [neg_neg] using hA (-v) h, hA v⟩
  have hi := (Homeomorph.neg E).preimage_interior A
  change Neg.neg ⁻¹' interior A = interior (Neg.neg ⁻¹' A) at hi
  rw [heq] at hi
  have hpre : ξ ∈ Neg.neg ⁻¹' interior A := by rw [hi]; exact hξ
  exact hpre

/-- Reflection preserves the original protected physical region when its
angular set is symmetric (`app:ch_regular:lem:finite-chain`). -/
theorem physicalProtectedRegion_reflection {Γ : Set E}
    (hΓ : ∀ ξ ∈ Γ, -ξ ∈ Γ) {p : P} (hp : p ∈ physicalProtectedRegion Γ) :
    physicalCovectorReflection p ∈ physicalProtectedRegion Γ := by
  refine ⟨neg_ne_zero.mpr hp.1, ?_⟩
  have h := neg_mem_interior_of_symmetric hΓ hp.2
  simpa only [physicalCovectorReflection_apply, normalizedCovector, norm_neg, smul_neg] using h

/-- The symmetric source hull preserves the original physical and angular
source conditions on the SAME initialized geometry
(`app:ch_regular:lem:finite-chain`). -/
theorem physicalSymmetricHull_source_geometry
    {S : Set P} {Ω : Set E} {r : ℝ} (hΩ : ∀ ξ ∈ Ω, -ξ ∈ Ω)
    (hsource : ∀ p ∈ S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω) :
    ∀ p ∈ physicalSymmetricHull S, p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
      normalizedCovector p.2 ∈ interior Ω := by
  rintro p (hp | ⟨q, hq, rfl⟩)
  · exact hsource p hp
  · exact ⟨(hsource q hq).1,
      physicalProtectedRegion_reflection hΩ (hsource q hq).2⟩

/-- Evenness and the original plateau force the reflected source to lie
inside the original buffer. Thus `S ⊆ V` alone cannot support the stronger
selected-mask conclusion for arbitrary `S,V`. The actual source/buffer
producer must supply this geometric inclusion
(`app:ch_regular:lem:finite-chain`). -/
theorem reflected_source_subset_of_even_bufferedLocalizer
    {m : LocalizerSymbol (d + 1)} {S V : Set P}
    (hm : IsBufferedLocalizer m S V) (heven : ∀ y ξ, m (y, -ξ) = m (y, ξ)) :
    physicalCovectorReflection '' S ⊆ V := by
  rintro p ⟨q, hq, rfl⟩
  apply hm.support_subset
  apply subset_tsupport m
  change m (q.1, -q.2) ≠ 0
  rw [heven, show m (q.1, q.2) = 1 from
    interior_subset (s := {p | m p = 1}) (hm.plateau hq)]
  exact one_ne_zero

/-- If the actual source frequency compact is symmetric, its original
buffer already contains the reflected product. No source cutoff or inverse
is replaced (`app:ch_regular:lem:finite-chain`). -/
theorem reflected_source_product_subset
    {χ : E → ℝ} {K : Set E} {V : Set P}
    (hK : ∀ ξ ∈ K, -ξ ∈ K) (hV : tsupport χ ×ˢ K ⊆ V) :
    physicalCovectorReflection '' (tsupport χ ×ˢ K) ⊆ V := by
  rintro p ⟨q, hq, rfl⟩
  exact hV ⟨hq.1, hK q.2 hq.2⟩

/-- The full closed support of an actual even frequency cutoff is symmetric.
This applies to the cutoff already produced by `exists_even_angular_mask`,
without making a new cutoff choice (`app:ch_regular:lem:finite-chain`). -/
theorem neg_mem_tsupport_even_frequency {a : E → ℝ}
    (ha : ∀ ξ, a (-ξ) = a ξ) {ξ : E} (hξ : ξ ∈ tsupport a) : -ξ ∈ tsupport a := by
  have heq : a ∘ (Homeomorph.neg E) = a := funext ha
  have ht := tsupport_comp_eq_preimage a (Homeomorph.neg E)
  rw [heq] at ht
  have hpre : ξ ∈ (Homeomorph.neg E) ⁻¹' tsupport a := by rw [← ht]; exact hξ
  exact hpre

/-- The original product over an even frequency cutoff supplies the source
symmetry needed by the actual nested constructor, retaining the entire
physical source support (`app:ch_regular:lem:finite-chain`). -/
theorem source_product_reflection_of_even_frequency (χ : E → ℝ) {a : E → ℝ}
    (ha : ∀ ξ, a (-ξ) = a ξ) :
    ∀ p ∈ tsupport χ ×ˢ tsupport a,
      physicalCovectorReflection p ∈ tsupport χ ×ˢ tsupport a := by
  intro p hp
  exact ⟨hp.1, neg_mem_tsupport_even_frequency ha hp.2⟩

end JanetCartan.ArbitraryAccuracy.SelectedEvenProofMasks
