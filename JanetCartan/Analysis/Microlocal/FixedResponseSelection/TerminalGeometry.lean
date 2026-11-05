module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.RegularSectors

/-!
# The outer compact for the complete terminal source

The relative signed no-return producer supplies compact symmetric regular
sectors `Γin ⊆ interior Γout`. The corrected complete source uses `K = Γout`.
This includes the whole terminal angular collar, not just initial directions.
The properties below discharge the actual finite selector's zero, regularity
and aperture obligations before any reference is chosen.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace JanetCartan.ProtectedFlow
open ActualCarriers

/-- The outer protected sector is the compact for the corrected complete
source; its inner sector supplies a uniform terminal collar. This preserves
both signs and every frozen regularity input of the finite selector
(`app:ch_regular:thm:no-return`, `app:ch_regular:lem:finite-chain`). -/
theorem protected_terminal_compact_selection_data {n : ℕ} (hd : 5 ≤ n)
    {Γin Γout : Set (Euclidean n)}
    (hin : IsCompact Γin) (hout : IsCompact Γout)
    (hnest : Γin ⊆ interior Γout)
    (hsym : ∀ ξ ∈ Γout, -ξ ∈ Γout)
    (hbad : Γout ⊆ (cubeBadSubspaceUnion n)ᶜ) :
    (0 : Euclidean n) ∉ Γout ∧
    (∀ ξ ∈ Γout, determinant (cubeStress n) ξ = 0 →
      fderiv ℝ (determinant (cubeStress n)) ξ ≠ 0) ∧
    ∃ aperture > (0 : ℝ), (∀ ξ ∈ Γout, ∀ i, |ξ i| < aperture) ∧
    ∃ θ > (0 : ℝ), ∀ ξ ∈ Γin,
      closedBall ξ θ ⊆ interior Γout ∧ closedBall (-ξ) θ ⊆ interior Γout := by
  have hzero : (0 : Euclidean n) ∉ Γout := fun h ↦
    hbad h (zero_mem_cubeBadSubspaceUnion hd)
  have hregular (ξ) (hξ : ξ ∈ Γout) (hz : determinant (cubeStress n) ξ = 0) :
      fderiv ℝ (determinant (cubeStress n)) ξ ≠ 0 := by
    have he : determinant (cubeStress n) = cubeDeterminant := funext determinant_cubeStress
    rw [he] at hz ⊢
    exact fderiv_cubeDeterminant_ne_zero_of_not_mem_badSubspaceUnion hd (hbad hξ) hz
  obtain ⟨A, hA, hbound⟩ := hout.isBounded.exists_pos_norm_lt
  obtain ⟨θ, hθ, hθin⟩ := hin.exists_cthickening_subset_open isOpen_interior hnest
  have hnegin : MapsTo (fun ξ : Euclidean n ↦ -ξ) (interior Γout) (interior Γout) := by
    intro ξ hξ
    exact interior_mono (image_subset_iff.mpr hsym)
      ((Homeomorph.neg (Euclidean n)).isOpenMap.image_interior_subset Γout
        (mem_image_of_mem (fun ξ ↦ -ξ) hξ))
  refine ⟨hzero, hregular, A, hA, ?_, θ, hθ, ?_⟩
  · intro ξ hξ i
    have hi : |ξ i| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i
    exact hi.trans_lt (hbound ξ hξ)
  · intro ξ hξ
    have hball := (closedBall_subset_cthickening hξ θ).trans hθin
    refine ⟨hball, ?_⟩
    intro v hv
    have hn : -v ∈ closedBall ξ θ := by simpa only [mem_closedBall, ← dist_neg_neg v (-ξ), neg_neg] using hv
    simpa only [neg_neg] using hnegin (hball hn)

end JanetCartan.ProtectedFlow
