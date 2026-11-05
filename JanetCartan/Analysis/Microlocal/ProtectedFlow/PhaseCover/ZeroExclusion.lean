module

public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Exclusion of new characteristic points outside a frozen cover

The finite comparison-phase paragraph of `app:ch_regular:thm:no-return`
requires coverage of the current characteristic set, including covectors
which are not characteristic for the frozen symbol. Compactness supplies a
positive lower bound for the frozen symbol outside its open chart cover.
The estimates below turn this into coverage for every sufficiently close
current symbol on the entire physical-angular product.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ProtectedFlow.PhaseCover

/-- Outside any open neighborhood of the frozen zero set, the frozen symbol
has a strictly positive absolute lower bound on the compact source.
This is the quantitative exclusion step of `app:ch_regular:thm:no-return`.
The statement also covers an empty frozen characteristic set. -/
theorem exists_positive_frozen_gap {P : Type*} [TopologicalSpace P]
    {K O : Set P} {f : P → ℝ} (hK : IsCompact K) (hO : IsOpen O)
    (hf : ContinuousOn f K) (hcover : ∀ p ∈ K, f p = 0 → p ∈ O) :
    ∃ δ > 0, ∀ p ∈ K \ O, δ ≤ |f p| := by
  apply (hK.diff hO).exists_forall_le' (hf.abs.mono sdiff_subset)
  intro p hp
  exact abs_pos.mpr (fun hz ↦ hp.2 (hcover p hp.1 hz))

/-- Every current zero on the complete product lies in the frozen open cover
when the scalar symbols are uniformly close. No current zero is assumed to
be a frozen zero (`app:ch_regular:thm:no-return`). -/
theorem exists_zero_exclusion_threshold {P X : Type*} [TopologicalSpace P]
    {K O : Set P} {f : P → ℝ} (hK : IsCompact K) (hO : IsOpen O)
    (hf : ContinuousOn f K) (hcover : ∀ p ∈ K, f p = 0 → p ∈ O) :
    ∃ δ > 0, ∀ (S : Set X) (h : X × P → ℝ),
      (∀ x ∈ S, ∀ p ∈ K, |h (x, p) - f p| < δ) →
      ∀ x ∈ S, ∀ p ∈ K, h (x, p) = 0 → p ∈ O := by
  obtain ⟨δ, hδ, hgap⟩ := exists_positive_frozen_gap hK hO hf hcover
  refine ⟨δ, hδ, fun S h hclose x hx p hp hz ↦ ?_⟩
  by_contra hout
  have hsmall := hclose x hx p hp
  rw [hz, zero_sub, abs_neg] at hsmall
  exact (not_lt_of_ge (hgap p ⟨hp, hout⟩)) hsmall

/-- A finite frozen open cover covers all current characteristic points of
the full physical-angular product after one scalar perturbation threshold.
This selects charts only at frozen zeros, but its conclusion includes all
current zeros (`app:ch_regular:thm:no-return`). -/
theorem exists_finite_stable_zero_cover {P X I : Type*} [TopologicalSpace P]
    {K : Set P} {f : P → ℝ} (hK : IsCompact K) (hf : ContinuousOn f K)
    (O : I → Set P) (hO : ∀ i, IsOpen (O i))
    (hcover : ∀ p ∈ K, f p = 0 → ∃ i, p ∈ O i) :
    ∃ (s : Finset I) (δ : ℝ), 0 < δ ∧
      (∀ p ∈ K, f p = 0 → ∃ i ∈ s, p ∈ O i) ∧
      ∀ (S : Set X) (h : X × P → ℝ),
        (∀ x ∈ S, ∀ p ∈ K, |h (x, p) - f p| < δ) →
        ∀ x ∈ S, ∀ p ∈ K, h (x, p) = 0 → ∃ i ∈ s, p ∈ O i := by
  have hZ : IsCompact {p ∈ K | f p = 0} := by
    obtain ⟨F, hF, he⟩ := continuousOn_iff_isClosed.mp hf {0} isClosed_singleton
    have he' : {p ∈ K | f p = 0} = f ⁻¹' {0} ∩ K := by
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, and_comm]
    rw [he', he]
    exact hK.inter_left hF
  obtain ⟨s, hs⟩ := hZ.elim_finite_subcover O hO (by
    intro p hp
    obtain ⟨i, hi⟩ := hcover p hp.1 hp.2
    exact mem_iUnion.mpr ⟨i, hi⟩)
  have hfrozen : ∀ p ∈ K, f p = 0 → p ∈ ⋃ i ∈ s, O i :=
    fun p hp hz ↦ hs ⟨hp, hz⟩
  obtain ⟨δ, hδ, hstable⟩ := exists_zero_exclusion_threshold (X := X) hK
    (isOpen_biUnion fun i _ ↦ hO i) hf hfrozen
  refine ⟨s, δ, hδ, ?_, ?_⟩
  · intro p hp hz
    simpa only [mem_iUnion, exists_prop] using hfrozen p hp hz
  · intro S h hclose x hx p hp hz
    simpa only [mem_iUnion, exists_prop, Finset.mem_coe] using
      hstable S h hclose x hx p hp hz

/-- The primitive scalar-symbol seminorm controls the pointwise perturbation
used in zero exclusion. Smoothness is needed only near the compact estimate
set, as in the buffered domains of `app:lem:common-hamilton-phase`. -/
theorem abs_sub_le_cNorm_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D K : Set E} {f g : E → ℝ} {k : ℕ} (hD : IsOpen D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : ContDiffOn ℝ ∞ f D) (hg : ContDiffOn ℝ ∞ g D)
    {z : E} (hz : z ∈ K) : |f z - g z| ≤ cNorm K k (fun z ↦ f z - g z) := by
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun z hz ↦ ((hf.sub hg).contDiffAt (hD.mem_nhds (hKD hz))).of_le (by simp))
      hz (Nat.zero_le k)

end JanetCartan.ProtectedFlow.PhaseCover
