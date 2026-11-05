module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Localizers.Masks
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.Gaps
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.FrequencyGaps
import Mathlib.Tactic.Linarith

/-!
# Gaps on complementary retarded mask supports

The compactness step of `app:ch_regular:lem:finite-chain`, “Retarded and signed
factors”, for the masks constructed in `Localizers.Masks`. The buffer concerns
the entire closed input support. The output is in the actual rectangle and in
the closed support of the complementary mask, including its identity part.

The integration parameter space is arbitrary. Its compact subsets may include
all base, covector, common-time and transverse integration variables. The
literal adjoint uses the swapped defects and the backward complete image.
No analytic tail estimate is assumed here.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.FiniteChain.Retarded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The buffer on the entire input support excludes the complete relation on
the complementary output support (`app:ch_regular:lem:finite-chain`). The
output mask retains its smoothness, compact support and chart hypotheses. -/
theorem IsBufferedMask.not_completeRelation_of_complement
    {backward : Bool} {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage backward R (tsupport mi) ⊆ interior {q | mo q = 1})
    {p q : CanonicalPhase E} (hp : p ∈ tsupport mi) (hqR : q.1 ∈ R)
    (hq : q ∈ tsupport (fun q => 1 - mo q)) :
    ¬ CompleteRelation backward p q := by
  have hm : IsBufferedMask mo (completeImage backward R (tsupport mi)) Oo :=
    { hmo with plateau := hbuffer }
  intro hrel
  exact disjoint_left.mp hm.disjoint_complement ⟨hqR, p, hp, hrel⟩ hq

/-- Complementary supports exclude the full diagonal, including both base
coordinates (`app:ch_regular:lem:finite-chain`), in either time orientation. -/
theorem IsBufferedMask.not_diagonal_of_complement
    {backward : Bool} {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage backward R (tsupport mi) ⊆ interior {q | mo q = 1})
    {xi xo : ℝ × E} {κ τ : ℝ} {ζ η : E}
    (hi : (xi, τ, η) ∈ tsupport mi) (hoR : xo ∈ R)
    (ho : (xo, κ, ζ) ∈ tsupport (fun q => 1 - mo q)) :
    ¬ (xo = xi ∧ κ = τ ∧ ζ = η) := by
  rintro ⟨hx, hκ, hζ⟩
  exact hmo.not_completeRelation_of_complement hbuffer hi hoR ho
    (Or.inl (Prod.ext hx (Prod.ext hκ hζ)))

/-- The compact complementary support has a boundary tangential gap and a
quantitative collar of half that width (`app:ch_regular:lem:finite-chain`).
Every input-base term is retained; the collar allows any normal coordinate. -/
theorem exists_complementary_boundary_gap
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {backward : Bool} {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage backward R (tsupport mi) ⊆ interior {q | mo q = 1})
    (xi xo : X → ℝ × E) (s κ τ : X → ℝ) (y ζ η : X → E)
    (hxi : Continuous xi) (hxo : Continuous xo) (hs : Continuous s)
    (hκ : Continuous κ) (hτ : Continuous τ) (hy : Continuous y)
    (hζ : Continuous ζ) (hη : Continuous η)
    (hi : ∀ p ∈ K, (xi p, τ p, η p) ∈ tsupport mi)
    (hoR : ∀ p ∈ K, xo p ∈ R)
    (ho : ∀ p ∈ K, (xo p, κ p, ζ p) ∈ tsupport (fun q => 1 - mo q)) :
    ∃ δ > 0, ∀ p ∈ K,
      δ ≤ tangentialDefect (xi p) (xo p) 0 (s p) (y p) (κ p) (ζ p) (τ p) (η p) ∧
      ∀ d : ℝ, |d| ≤ δ / 2 →
        δ / 2 ≤ tangentialDefect (xi p) (xo p) d (s p) (y p) (κ p) (ζ p) (τ p) (η p) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_boundary_gap hK xi xo s κ τ y ζ η
    hxi hxo hs hκ hτ hy hζ hη (fun p hp =>
      hmo.not_diagonal_of_complement hbuffer (hi p hp) (hoR p hp) (ho p hp))
  exact ⟨δ, hδ, fun p hp => ⟨hgap p hp, fun _ hd => tangentialDefect_collar (hgap p hp) hd⟩⟩

/-- The forward complete-image buffer discharges the off-characteristic
premise of the compact full-defect gap (`app:ch_regular:lem:finite-chain`). -/
theorem exists_complementary_interior_gap
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage false R (tsupport mi) ⊆ interior {q | mo q = 1})
    (xi xo : X → ℝ × E) (d s κ τ : X → ℝ) (y ζ η : X → E)
    (hxi : Continuous xi) (hxo : Continuous xo) (hd : Continuous d) (hs : Continuous s)
    (hκ : Continuous κ) (hτ : Continuous τ) (hy : Continuous y)
    (hζ : Continuous ζ) (hη : Continuous η) (hdpos : ∀ p ∈ K, 0 ≤ d p)
    (hi : ∀ p ∈ K, (xi p, τ p, η p) ∈ tsupport mi)
    (hoR : ∀ p ∈ K, xo p ∈ R)
    (ho : ∀ p ∈ K, (xo p, κ p, ζ p) ∈ tsupport (fun q => 1 - mo q)) :
    ∃ δ > 0, ∀ p ∈ K,
      δ ≤ fullDefect (xi p) (xo p) (d p) (s p) (y p) (κ p) (ζ p) (τ p) (η p) := by
  apply exists_interior_gap hK xi xo d s κ τ y ζ η
    hxi hxo hd hs hκ hτ hy hζ hη hdpos
  intro p hp hrel
  exact hmo.not_completeRelation_of_complement hbuffer (hi p hp) (hoR p hp) (ho p hp)
    (Or.inr hrel)

/-- The literal adjoint has a boundary gap and collar for its swapped
tangential defect (`app:ch_regular:lem:finite-chain`). Its input support is
protected by the backward image, with the actual output base still in `R`. -/
theorem exists_adjoint_complementary_boundary_gap
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage true R (tsupport mi) ⊆ interior {q | mo q = 1})
    (xi xo : X → ℝ × E) (t κ τ : X → ℝ) (y ζ η : X → E)
    (hxi : Continuous xi) (hxo : Continuous xo) (ht : Continuous t)
    (hκ : Continuous κ) (hτ : Continuous τ) (hy : Continuous y)
    (hζ : Continuous ζ) (hη : Continuous η)
    (hi : ∀ p ∈ K, (xi p, τ p, η p) ∈ tsupport mi)
    (hoR : ∀ p ∈ K, xo p ∈ R)
    (ho : ∀ p ∈ K, (xo p, κ p, ζ p) ∈ tsupport (fun q => 1 - mo q)) :
    ∃ δ > 0, ∀ p ∈ K,
      δ ≤ tangentialDefect (xo p) (xi p) 0 (t p) (y p) (τ p) (η p) (κ p) (ζ p) ∧
      ∀ d : ℝ, |d| ≤ δ / 2 →
        δ / 2 ≤ tangentialDefect (xo p) (xi p) d (t p) (y p) (τ p) (η p) (κ p) (ζ p) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_boundary_gap hK xo xi t τ κ y η ζ
    hxo hxi ht hτ hκ hy hη hζ (fun p hp hdiag =>
      hmo.not_diagonal_of_complement hbuffer (hi p hp) (hoR p hp) (ho p hp)
        ⟨hdiag.1.symm, hdiag.2.1.symm, hdiag.2.2.symm⟩)
  exact ⟨δ, hδ, fun p hp => ⟨hgap p hp, fun _ hd => tangentialDefect_collar (hgap p hp) hd⟩⟩

/-- The literal adjoint uses the swapped full defect and backward relation
(`app:ch_regular:lem:finite-chain`), with normal coordinate `d = s - t ≥ 0`. -/
theorem exists_adjoint_complementary_interior_gap
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage true R (tsupport mi) ⊆ interior {q | mo q = 1})
    (xi xo : X → ℝ × E) (d t κ τ : X → ℝ) (y ζ η : X → E)
    (hxi : Continuous xi) (hxo : Continuous xo) (hd : Continuous d) (ht : Continuous t)
    (hκ : Continuous κ) (hτ : Continuous τ) (hy : Continuous y)
    (hζ : Continuous ζ) (hη : Continuous η) (hdpos : ∀ p ∈ K, 0 ≤ d p)
    (hi : ∀ p ∈ K, (xi p, τ p, η p) ∈ tsupport mi)
    (hoR : ∀ p ∈ K, xo p ∈ R)
    (ho : ∀ p ∈ K, (xo p, κ p, ζ p) ∈ tsupport (fun q => 1 - mo q)) :
    ∃ δ > 0, ∀ p ∈ K,
      δ ≤ fullDefect (xo p) (xi p) (d p) (t p) (y p) (τ p) (η p) (κ p) (ζ p) := by
  apply exists_interior_gap hK xo xi d t τ κ y η ζ
    hxo hxi hd ht hτ hκ hy hη hζ hdpos
  intro p hp hrel
  exact hmo.not_completeRelation_of_complement hbuffer (hi p hp) (hoR p hp) (ho p hp)
    (Or.inr hrel)

omit [InnerProductSpace ℝ E] in
/-- Reflection transports the complementary closed support, including its
identity contribution (`app:ch_regular:lem:finite-chain`). -/
theorem tsupport_complement_signedMask (m : CanonicalPhase E → ℝ) :
    tsupport (fun q => 1 - signedMask m q) =
      reflectCovector ⁻¹' tsupport (fun q => 1 - m q) :=
  tsupport_signedMask (fun q => 1 - m q)

omit [InnerProductSpace ℝ E] in
/-- The complete support buffer survives signed covector reflection with the
same time orientation (`app:ch_regular:lem:finite-chain`). -/
theorem completeImage_signedMask_subset_plateau
    {backward : Bool} {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    (hbuffer : completeImage backward R (tsupport mi) ⊆ interior {q | mo q = 1}) :
    completeImage backward R (tsupport (signedMask mi)) ⊆
      interior {q | signedMask mo q = 1} := by
  rintro q ⟨hqR, p, hp, hrel⟩
  rw [tsupport_signedMask] at hp
  have hq : reflectCovector q ∈ completeImage backward R (tsupport mi) :=
    ⟨hqR, reflectCovector p, hp,
      (completeRelation_reflectCovector backward p q).mpr hrel⟩
  have hpre : q ∈ reflectCovectorHomeomorph ⁻¹' interior {q | mo q = 1} := hbuffer hq
  rw [reflectCovectorHomeomorph.preimage_interior] at hpre
  exact hpre

omit [InnerProductSpace ℝ E] in
/-- Signed conjugation leaves the full tangential defect unchanged, including
the input-base terms (`app:ch_regular:lem:finite-chain`). -/
theorem tangentialDefect_neg_covectors (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    tangentialDefect xi xo d s y (-κ) (-ζ) (-τ) (-η) =
      tangentialDefect xi xo d s y κ ζ τ η := by
  simp only [tangentialDefect, neg_sub_neg, abs_sub_comm κ τ, norm_sub_rev ζ η]

omit [InnerProductSpace ℝ E] in
/-- Signed conjugation leaves the interior full defect unchanged
(`app:ch_regular:lem:finite-chain`). -/
theorem fullDefect_neg_covectors (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    fullDefect xi xo d s y (-κ) (-ζ) (-τ) (-η) =
      fullDefect xi xo d s y κ ζ τ η := by
  simp only [fullDefect, tangentialDefect_neg_covectors, abs_neg]

/-- Signed forward masks give the boundary collar and the interior gap on
compact complementary supports (`app:ch_regular:lem:finite-chain`). Smooth
mask hypotheses are transported by `IsBufferedMask.signed`. -/
theorem exists_signed_complementary_gaps
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage false R (tsupport mi) ⊆ interior {q | mo q = 1})
    (xi xo : X → ℝ × E) (d s κ τ : X → ℝ) (y ζ η : X → E)
    (hxi : Continuous xi) (hxo : Continuous xo) (hd : Continuous d) (hs : Continuous s)
    (hκ : Continuous κ) (hτ : Continuous τ) (hy : Continuous y)
    (hζ : Continuous ζ) (hη : Continuous η) (hdpos : ∀ p ∈ K, 0 ≤ d p)
    (hi : ∀ p ∈ K, (xi p, τ p, η p) ∈ tsupport (signedMask mi))
    (hoR : ∀ p ∈ K, xo p ∈ R)
    (ho : ∀ p ∈ K, (xo p, κ p, ζ p) ∈ tsupport (fun q => 1 - signedMask mo q)) :
    ∃ δb > 0, ∃ δi > 0, ∀ p ∈ K,
      (δb ≤ tangentialDefect (xi p) (xo p) 0 (s p) (y p) (κ p) (ζ p) (τ p) (η p) ∧
        ∀ r : ℝ, |r| ≤ δb / 2 →
          δb / 2 ≤ tangentialDefect (xi p) (xo p) r (s p) (y p) (κ p) (ζ p) (τ p) (η p)) ∧
      δi ≤ fullDefect (xi p) (xo p) (d p) (s p) (y p) (κ p) (ζ p) (τ p) (η p) := by
  have hbuffer' := completeImage_signedMask_subset_plateau hbuffer
  obtain ⟨δb, hδb, hb⟩ := exists_complementary_boundary_gap hK hmo.signed hbuffer'
    xi xo s κ τ y ζ η hxi hxo hs hκ hτ hy hζ hη hi hoR ho
  obtain ⟨δi, hδi, hi'⟩ := exists_complementary_interior_gap hK hmo.signed hbuffer'
    xi xo d s κ τ y ζ η hxi hxo hd hs hκ hτ hy hζ hη hdpos hi hoR ho
  exact ⟨δb, hδb, δi, hδi, fun p hp => ⟨hb p hp, hi' p hp⟩⟩

/-- Signed literal-adjoint masks give gaps for the swapped defects. Covector
reflection preserves the backward orientation
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_signed_adjoint_complementary_gaps
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {R : Set (ℝ × E)} {mi mo : CanonicalPhase E → ℝ}
    {Ko Oo : Set (CanonicalPhase E)} (hmo : IsBufferedMask mo Ko Oo)
    (hbuffer : completeImage true R (tsupport mi) ⊆ interior {q | mo q = 1})
    (xi xo : X → ℝ × E) (d t κ τ : X → ℝ) (y ζ η : X → E)
    (hxi : Continuous xi) (hxo : Continuous xo) (hd : Continuous d) (ht : Continuous t)
    (hκ : Continuous κ) (hτ : Continuous τ) (hy : Continuous y)
    (hζ : Continuous ζ) (hη : Continuous η) (hdpos : ∀ p ∈ K, 0 ≤ d p)
    (hi : ∀ p ∈ K, (xi p, τ p, η p) ∈ tsupport (signedMask mi))
    (hoR : ∀ p ∈ K, xo p ∈ R)
    (ho : ∀ p ∈ K, (xo p, κ p, ζ p) ∈ tsupport (fun q => 1 - signedMask mo q)) :
    ∃ δb > 0, ∃ δi > 0, ∀ p ∈ K,
      (δb ≤ tangentialDefect (xo p) (xi p) 0 (t p) (y p) (τ p) (η p) (κ p) (ζ p) ∧
        ∀ r : ℝ, |r| ≤ δb / 2 →
          δb / 2 ≤ tangentialDefect (xo p) (xi p) r (t p) (y p) (τ p) (η p) (κ p) (ζ p)) ∧
      δi ≤ fullDefect (xo p) (xi p) (d p) (t p) (y p) (τ p) (η p) (κ p) (ζ p) := by
  have hbuffer' := completeImage_signedMask_subset_plateau hbuffer
  obtain ⟨δb, hδb, hb⟩ := exists_adjoint_complementary_boundary_gap hK hmo.signed hbuffer'
    xi xo t κ τ y ζ η hxi hxo ht hκ hτ hy hζ hη hi hoR ho
  obtain ⟨δi, hδi, hi'⟩ := exists_adjoint_complementary_interior_gap hK hmo.signed hbuffer'
    xi xo d t κ τ y ζ η hxi hxo hd ht hκ hτ hy hζ hη hdpos hi hoR ho
  exact ⟨δb, hδb, δi, hδi, fun p hp => ⟨hb p hp, hi' p hp⟩⟩

omit [InnerProductSpace ℝ E] in
/-- The radial covector norm is bounded by the sum of the two tangential
frequency components (`app:ch_regular:lem:finite-chain`). -/
theorem frequencySize_le_abs_add_norm (τ : ℝ) (η : E) :
    frequencySize τ η ≤ |τ| + ‖η‖ := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_abs τ, mul_nonneg (abs_nonneg τ) (norm_nonneg η)]

omit [InnerProductSpace ℝ E] in
/-- The joint frequency difference is controlled by the actual tangential
defect, without discarding any base terms (`app:ch_regular:lem:finite-chain`). -/
theorem frequencySize_sub_le_tangentialDefect (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E) :
    frequencySize (τ - κ) (η - ζ) ≤ tangentialDefect xi xo d s y κ ζ τ η := by
  have h := frequencySize_le_abs_add_norm (τ - κ) (η - ζ)
  dsimp [tangentialDefect]
  linarith [abs_nonneg (xo.1 - (s + d)), norm_nonneg (xo.2 - y),
    abs_nonneg (s - xi.1), norm_nonneg (y - xi.2)]

omit [InnerProductSpace ℝ E] in
/-- Noncomparable frequencies give a tangential gap controlled by the larger
frequency everywhere, including the boundary collar
(`app:ch_regular:lem:finite-chain`). No division by a time covector occurs. -/
theorem noncomparable_tangentialDefect_gap (xi xo : ℝ × E) (d s : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E)
    (h : 2 * frequencySize τ η ≤ frequencySize κ ζ ∨
      2 * frequencySize κ ζ ≤ frequencySize τ η) :
    max (frequencySize τ η) (frequencySize κ ζ) / 2 ≤
      tangentialDefect xi xo d s y κ ζ τ η :=
  (noncomparable_frequency_gap τ κ η ζ h).trans
    (frequencySize_sub_le_tangentialDefect xi xo d s y κ ζ τ η)

omit [InnerProductSpace ℝ E] in
/-- The larger-frequency bound also holds for the literal adjoint's swapped
tangential defect (`app:ch_regular:lem:finite-chain`). -/
theorem noncomparable_adjoint_tangentialDefect_gap (xi xo : ℝ × E) (d t : ℝ) (y : E)
    (κ : ℝ) (ζ : E) (τ : ℝ) (η : E)
    (h : 2 * frequencySize τ η ≤ frequencySize κ ζ ∨
      2 * frequencySize κ ζ ≤ frequencySize τ η) :
    max (frequencySize τ η) (frequencySize κ ζ) / 2 ≤
      tangentialDefect xo xi d t y τ η κ ζ := by
  simpa only [max_comm] using noncomparable_tangentialDefect_gap xo xi d t y τ η κ ζ h.symm

end JanetCartan.FiniteChain.Retarded
