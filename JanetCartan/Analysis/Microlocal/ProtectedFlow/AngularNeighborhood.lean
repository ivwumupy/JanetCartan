module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.CubeSymbol

/-!
# Buffered annular neighborhoods of all signed directions

The compact angular set constructed by `ConstructedSignedGeometry` includes
limiting short chords and antipodes. Here it is enlarged to the two nested
compact annular source sets in `app:ch_regular:thm:no-return`, with one positive
buffer from the actual frozen forbidden cone.
-/

@[expose] public noncomputable section
open Set Metric

namespace JanetCartan.ProtectedFlow
open SignedPairs

private theorem neg_mem_cthickening_angularSet {n : ℕ} {γ δ : ℝ}
    (hδ : 0 ≤ δ) {v : Euclidean n} (hv : v ∈ cthickening δ (angularSet n γ)) :
    -v ∈ cthickening δ (angularSet n γ) := by
  rw [(isCompact_angularSet n γ).cthickening_eq_biUnion_closedBall hδ] at hv ⊢
  obtain ⟨w, hw, hvw⟩ := mem_iUnion₂.mp hv
  exact mem_iUnion₂.mpr ⟨-w, neg_mem_angularSet hw, by simpa using hvw⟩

/-- Nested compact symmetric annular neighborhoods around the complete signed
angular family. The outer set, including its boundary, has a positive buffer
from the nonprincipal cone. Both neighborhoods precede the current frame,
frequencies, histories and requested accuracy (`app:ch_regular:thm:no-return`). -/
theorem exists_signed_angular_neighborhoods {n : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    ∃ ε > (0 : ℝ), ∃ Ω₀ Ω₁ : Set (Euclidean n),
      IsCompact Ω₀ ∧ IsCompact Ω₁ ∧
      angularSet n γ ⊆ interior Ω₀ ∧ Ω₀ ⊆ interior Ω₁ ∧
      (∀ v ∈ Ω₀, -v ∈ Ω₀) ∧ (∀ v ∈ Ω₁, -v ∈ Ω₁) ∧
      (∀ v ∈ Ω₁, (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2) ∧
      Disjoint Ω₁ (cubeBadSubspaceUnion n) ∧
      (∀ v ∈ Ω₁, closedBall v ε ⊆ (cubeBadSubspaceUnion n)ᶜ) := by
  let V : Set (Euclidean n) :=
    {v | (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2} ∩ (cubeBadSubspaceUnion n)ᶜ
  have hV : IsOpen V :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).inter
        (isClosed_cubeBadSubspaceUnion n).isOpen_compl
  have hsub : angularSet n γ ⊆ V := by
    intro v hv
    exact ⟨by change (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2; rw [hv.1]; norm_num,
      disjoint_left.mp (angularSet_disjoint_bad hγ) hv⟩
  obtain ⟨d, hd, hdV⟩ := (isCompact_angularSet n γ).exists_cthickening_subset_open hV hsub
  let ε := d / 4
  have hε : 0 < ε := div_pos hd (by norm_num)
  let Ω₀ := cthickening ε (angularSet n γ)
  let Ω₁ := cthickening (2 * ε) (angularSet n γ)
  have houter : Ω₁ ⊆ V :=
    (cthickening_mono (by dsimp [ε]; linarith) _).trans hdV
  have hbuffer (v : Euclidean n) (hv : v ∈ Ω₁) :
      closedBall v ε ⊆ (cubeBadSubspaceUnion n)ᶜ := by
    intro w hw
    have hh : w ∈ cthickening ε Ω₁ := closedBall_subset_cthickening hv ε hw
    have hh' := cthickening_cthickening_subset hε.le (by positivity : 0 ≤ 2 * ε)
      (angularSet n γ) hh
    exact (hdV (cthickening_mono (by dsimp [ε]; linarith) _ hh')).2
  refine ⟨ε, hε, Ω₀, Ω₁, (isCompact_angularSet n γ).cthickening,
    (isCompact_angularSet n γ).cthickening, ?_, ?_,
    fun _ hv ↦ neg_mem_cthickening_angularSet hε.le hv,
    fun _ hv ↦ neg_mem_cthickening_angularSet (by positivity) hv,
    fun _ hv ↦ (houter hv).1, disjoint_left.mpr (fun _ hv ↦ (houter hv).2), hbuffer⟩
  · exact (self_subset_thickening hε _).trans (thickening_subset_interior_cthickening _ _)
  · exact (cthickening_subset_thickening' (by positivity : 0 < 2 * ε)
      (by linarith) _).trans (thickening_subset_interior_cthickening _ _)

end JanetCartan.ProtectedFlow
