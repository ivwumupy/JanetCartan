module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionProtection.Segments

/-!
# Buffered direct chains with changing root patches

The comparison family, its source coverage, and its angular buffer are the
literal retained outputs of `ProtectedFlow.exists_initialized_signed_no_return`.
The source buffer used for the elliptic branch is that theorem's characteristic
chain conclusion at length zero. No new reference, coefficient margin or
protection set is constructed. The parent must instantiate the SAME extended
current frame in the pencil roots and the comparison charts, and the sector
owner must prove the pairing for its adapted coordinates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy
open RegularSector.Characteristic ActualCarriers HamiltonPhase ProtectedFlow PhaseCover

variable {n d : ℕ} {I J : Type*}

/-- Direct chains retain nonzero covectors, including the diagonal and
elliptic branches. The only frequency input is nonvanishing at the source and
on the actual root domains (`app:ch_regular:lem:finite-chain`). -/
theorem pencilRoot_chain_covector_ne_zero
    (e : J → Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {h : J → RootState (Euclidean d) → ℝ} {D : J → Set (RootState (Euclidean d))}
    (hne : ∀ j, ∀ v ∈ D j, v.2.2 ≠ 0)
    {W : Set (Euclidean n)} {z w : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain
      (fun z w ↦ ∃ j, CompletePencilRootSegment (e j) (h j) (D j) W z w) z w k)
    (hz : z.2 ≠ 0) : w.2 ≠ 0 := by
  induction hchain with
  | refl z => exact hz
  | @tail z y w k hstep _ ih =>
    apply ih
    rcases hstep with hdiag | ⟨j, hseg⟩
    · exact hdiag ▸ hz
    · exact completePencilRootSegment_target_ne_zero (e j) (hne j) hseg

/-- Finite chains of whole root segments preserve the retained comparison
family, even when each segment uses a different adapted root patch. Diagonal
steps are included by `PositiveConicChain` (`app:ch_regular:lem:finite-chain`). -/
theorem comparisonFamily_preserves_pencilRootChain
    (e : J → Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (hpair : ∀ j, ∀ u v : ℝ × Euclidean d,
      ⟪(e j).symm u, (e j).symm v⟫_ℝ = u.1 * v.1 + ⟪u.2, v.2⟫_ℝ)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiff ℝ ∞ Q)
    {h : J → RootState (Euclidean d) → ℝ} {D : J → Set (RootState (Euclidean d))}
    (hD : ∀ j, IsOpen (D j)) (hh : ∀ j, ContDiffOn ℝ ∞ (h j) (D j))
    (hroot : ∀ j, ∀ v ∈ D j, v.2.2 ≠ 0 ∧
      determinant (Q ((e j).symm (v.1, v.2.1))) ((e j).symm (h j v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q ((e j).symm (v.1, v.2.1))))
        ((e j).symm (h j v, v.2.2)) ((e j).symm (1, 0)) ≠ 0)
    {g : I → ComparisonGeometry (Euclidean n)}
    (C : (i : I) → ComparisonChart (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g i))
    {r : ℝ} (hradius : ∀ i, 2 * r < (g i).radius)
    {z w : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain
      (fun z w ↦ ∃ j, CompletePencilRootSegment (e j) (h j) (D j) (ball 0 (2 * r)) z w) z w k)
    (hz : z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ) :
    w ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ := by
  apply positiveConicChain_preserves (hchain := hchain) (hz := hz)
  intro z w hz hseg
  obtain ⟨j, hj⟩ := hseg
  exact comparisonFamily_preserves_pencilRootSegment (e j) (hpair j) hQ (hD j)
    (hh j) (hroot j) C hradius hz hj

/-- Elliptic input has only diagonal images in a chain of direct zero-energy
root segments. The conclusion follows from the literal pencil equations of
the patches (`app:ch_regular:thm:no-return`). -/
theorem elliptic_pencilRoot_chain_eq
    (e : J → Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Q : Euclidean n → Fin n → MetricTensor n}
    {h : J → RootState (Euclidean d) → ℝ} {D : J → Set (RootState (Euclidean d))}
    (hroot : ∀ j, ∀ v ∈ D j,
      determinant (Q ((e j).symm (v.1, v.2.1))) ((e j).symm (h j v, v.2.2)) = 0)
    {W : Set (Euclidean n)} {z w : Euclidean n × Euclidean n} {k : ℕ}
    (hchain : PositiveConicChain
      (fun z w ↦ ∃ j, CompletePencilRootSegment (e j) (h j) (D j) W z w) z w k)
    (helliptic : normalizedSymbol Q z ≠ 0) : z = w := by
  induction hchain with
  | refl z => rfl
  | @tail z y w k hstep _ ih =>
    rcases hstep with hdiag | ⟨j, hseg⟩
    · exact hdiag.trans (ih (by simpa only [← hdiag] using helliptic))
    · exact (helliptic (completePencilRootSegment_source_energy (e j) (hroot j) hseg)).elim

/-- The retained angular radius protects every direct chain from the complete
source product. `hcover` and `hbuffer` are outputs for the SAME charts in
`exists_initialized_signed_no_return`; `hsource` is its length-zero chain case.
The proof discharges direct-chain invariance and the elliptic branch, without
introducing a new protection hypothesis (`app:ch_regular:thm:no-return`,
`app:ch_regular:lem:finite-chain`). -/
theorem pencilRoot_chain_angular_buffer
    (e : J → Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (hpair : ∀ j, ∀ u v : ℝ × Euclidean d,
      ⟪(e j).symm u, (e j).symm v⟫_ℝ = u.1 * v.1 + ⟪u.2, v.2⟫_ℝ)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiff ℝ ∞ Q)
    {h : J → RootState (Euclidean d) → ℝ} {D : J → Set (RootState (Euclidean d))}
    (hD : ∀ j, IsOpen (D j)) (hh : ∀ j, ContDiffOn ℝ ∞ (h j) (D j))
    (hroot : ∀ j, ∀ v ∈ D j, v.2.2 ≠ 0 ∧
      determinant (Q ((e j).symm (v.1, v.2.1))) ((e j).symm (h j v, v.2.2)) = 0 ∧
      fderiv ℝ (determinant (Q ((e j).symm (v.1, v.2.1))))
        ((e j).symm (h j v, v.2.2)) ((e j).symm (1, 0)) ≠ 0)
    {g : I → ComparisonGeometry (Euclidean n)}
    (C : (i : I) → ComparisonChart (normalizedHomogeneousSymbol isOpen_univ Q hQ.contDiffOn) (g i))
    {r ε : ℝ} (hradius : ∀ i, 2 * r < (g i).radius)
    {S : Set (Euclidean n × Euclidean n)} {G : Set (Euclidean n)}
    (hcover : ∀ z ∈ S, normalizedSymbol Q z = 0 →
      z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ)
    (hbuffer : ∀ z ∈ positiveConicLift (ComparisonChart.familyGradient C) (ball 0 (2 * r)) univ,
      closedBall (normalizedCovector z.2) ε ⊆ G)
    (hsource : ∀ z ∈ S, closedBall (normalizedCovector z.2) ε ⊆ G)
    {z w : Euclidean n × Euclidean n} {k : ℕ} (hz : z ∈ S)
    (hchain : PositiveConicChain
      (fun z w ↦ ∃ j, CompletePencilRootSegment (e j) (h j) (D j) (ball 0 (2 * r)) z w) z w k) :
    closedBall (normalizedCovector w.2) ε ⊆ G := by
  by_cases he : normalizedSymbol Q z = 0
  · exact hbuffer w (comparisonFamily_preserves_pencilRootChain e hpair hQ hD hh hroot C
      hradius hchain (hcover z hz he))
  · have hw := elliptic_pencilRoot_chain_eq e (fun j v hv ↦ (hroot j v hv).2.1) hchain he
    exact hw ▸ hsource z hz

end JanetCartan.ArbitraryAccuracy
