module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Cover
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.UniformBounds

/-!
# Common margins and restrictions for incidence charts

The finite minimum and neighborhood shrinking operations in Step 4 of
`app:ch_seed:prop:seed-frozen-menu` preserve every patch and section field.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

/-- A smaller positive lower margin and larger upper margin preserve all
frozen patch estimates (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem Patch.IsValid.mono {n : ℕ} {P : Patch n} {c C c' C' : ℝ}
    (h : P.IsValid c C) (hc' : 0 < c') (hc : c' ≤ c) (hC : C ≤ C') :
    P.IsValid c' C' := by
  rcases h with ⟨hρ, hpos, hCpos, hsmooth, hpoint, hpair⟩
  refine ⟨hρ, hc', hCpos.trans_le hC, hsmooth, ?_, ?_⟩
  · intro z hz
    obtain ⟨hcoord, hchar, hrank, hn, hlo, hhi, hgap⟩ := hpoint z hz
    exact ⟨hcoord, hchar, hrank, hn, hc.trans hlo, hhi.trans hC, hgap.mono hc⟩
  · intro z hz w hw
    obtain ⟨hproj, hupper, hsum, hgap⟩ := hpair z hz w hw
    refine ⟨fun L hL ↦ ?_, ?_, hsum, hgap.mono hc⟩
    · exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (hproj L hL)
    · exact hupper.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

/-- Restricting the covector neighborhood and decreasing the derivative
margin preserve the entire incidence-section specification
(`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem Patch.IsIncidenceSection.mono {n : ℕ} {P : Patch n}
    {U V : Set (Euclidean n)} {root : Euclidean n → Euclidean 3} {c c' : ℝ}
    (h : P.IsIncidenceSection U root c) (hVU : V ⊆ U) (hc : c' ≤ c) :
    P.IsIncidenceSection V root c' := by
  refine ⟨h.1.mono hVU, fun k hk ↦ h.2.1 k (hVU hk), ?_⟩
  exact fun k hk z hz ↦ hc.trans (h.2.2 k (hVU hk) z hz)

end JanetCartan.FrozenMenu
