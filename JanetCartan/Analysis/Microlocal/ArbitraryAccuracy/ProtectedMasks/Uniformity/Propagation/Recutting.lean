module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Shoulders
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Propagation.SourceNeighborhood

/-!
# Buffered source products and literal source recutting

Use `X = tsupport χ₂` in the protected finite-chain paragraph of
`app:ch_regular:lem:finite-chain`. The same positive shoulder works for the
recut relation; its diagonal branches remain present. The existing
`sourceRecutRelation_outer_eq_one` identifies the original `χ₃ = 1` plateau
at each actual recut source.
-/

@[expose] public noncomputable section

open Set Metric

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open ProtectedFlow

variable {d : ℕ}

/-- Restricting the possible actual steps preserves every closed buffered
image. A step of the smaller relation may also be a full diagonal step of
the larger one (`app:ch_regular:lem:finite-chain`). -/
theorem bufferedReachableAt_step_mono
    {R R' : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop}
    (hRR' : ∀ p q, R p q → p = q ∨ R' p q)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) (δ : ℝ) :
    ∀ n, bufferedReachableAt R S δ n ⊆ bufferedReachableAt R' S δ n := by
  intro n
  induction n with
  | zero => exact subset_refl _
  | succ n ih =>
    rintro q ⟨p, hp, hc⟩
    apply mem_bufferedReachableAt_succ_of_step (cthickening_subset_of_subset δ ih hp)
    cases hc with
    | tail hs hc =>
      cases hc
      exact hs.elim Or.inl (hRR' p q)

/-- Source recutting does not enlarge any closed shoulder, at any depth or
width. Therefore the uniform annular and angular conclusions for the actual
relation also hold for the paper's literal recut source relation
(`app:ch_regular:lem:finite-chain`). -/
theorem cthickening_bufferedReachableAt_sourceRecut_subset
    (χ₂ : Euclidean (d + 1) → ℝ)
    (R : (Euclidean (d + 1) × Euclidean (d + 1)) →
      (Euclidean (d + 1) × Euclidean (d + 1)) → Prop)
    (S : Set (Euclidean (d + 1) × Euclidean (d + 1))) (δ : ℝ) (n : ℕ) :
    cthickening δ (bufferedReachableAt (sourceRecutRelation χ₂ R) S δ n) ⊆
      cthickening δ (bufferedReachableAt R S δ n) :=
  cthickening_subset_of_subset δ
    (bufferedReachableAt_step_mono (fun _ _ h ↦ h.2) S δ n)

/-- The paper's actual source product supplies the fixed neighborhood used
by the first characteristic step. Its spatial buffer is the original compact
support of `χ₂`; its angular buffer is the retained `Ω₀ ⊆ interior Ω₁`.
No neighborhood depending on the current coefficients is chosen
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem exists_buffered_source_product_neighborhood
    {χ₂ : Euclidean (d + 1) → ℝ} (hχ₂ : HasCompactSupport χ₂)
    {r : ℝ} (hX : tsupport χ₂ ⊆ ball 0 r)
    {F Ω₀ Ω₁ Γ : Set (Euclidean (d + 1))}
    (hF : IsCompact F) (hne : ∀ ξ ∈ F, ξ ≠ 0)
    (hangle : ∀ ξ ∈ F, normalizedCovector ξ ∈ Ω₀)
    (hΩ : Ω₀ ⊆ interior Ω₁) (hΓ : Ω₁ ⊆ interior Γ)
    {V : Set (Euclidean (d + 1) × Euclidean (d + 1))}
    (hV : IsOpen V) (hsource : tsupport χ₂ ×ˢ F ⊆ V) :
    ∃ σ > (0 : ℝ), ∃ a > (0 : ℝ), ∃ b > a,
      ∀ p ∈ cthickening σ (tsupport χ₂ ×ˢ F),
        p ∈ V ∧ p.1 ∈ ball 0 r ∧ p.2 ≠ 0 ∧
        normalizedCovector p.2 ∈ Ω₁ ∧
        p ∈ physicalProtectedRegion Γ ∧ a ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ b :=
  exists_buffered_source_neighborhood (hχ₂.prod hF)
    (fun p hp ↦ ⟨hX hp.1, hne p.2 hp.2, hΩ (hangle p.2 hp.2)⟩) hΓ hV hsource

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
