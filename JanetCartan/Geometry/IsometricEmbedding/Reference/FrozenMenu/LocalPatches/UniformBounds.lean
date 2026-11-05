module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import Mathlib.Algebra.Order.Field.Pi
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform positive bounds for frozen patches

Finite-dimensional injectivity gives lower singular bounds for the projected
frames. Avoidance of the finite bad-subspace union gives positive directional
gaps at the carrier. These are the pointwise inputs to shrinking in Step 3 of
`app:ch_seed:prop:seed-frozen-menu`.
-/

@[expose] public noncomputable section

namespace JanetCartan.FrozenMenu

/-- Decreasing a directional gap preserves it
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem BadDirectionGap.mono {n : ℕ} {x : Euclidean n} {a b : ℝ}
    (hb : BadDirectionGap b x) (hab : a ≤ b) : BadDirectionGap a x :=
  fun L hL ↦ hab.trans (hb L hL)

/-- Avoidance of the bad-subspace union gives a strictly positive uniform
directional gap (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem exists_pos_badDirectionGap_of_not_mem {n : ℕ} {ξ : Euclidean n}
    (hξ : ξ ∉ cubeBadSubspaceUnion n) : ∃ γ > 0, BadDirectionGap γ ξ := by
  classical
  have hp (L : ↥(cubeBadSubspaces n)) :
      0 < ‖L.valᗮ.orthogonalProjectionOnto (NormedSpace.normalize ξ)‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hm : NormedSpace.normalize ξ ∈ L.val := by
      simpa only [Submodule.orthogonal_orthogonal] using
        (Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hz)
    have hmξ : ξ ∈ L.val := by
      simpa only [NormedSpace.norm_smul_normalize] using L.val.smul_mem ‖ξ‖ hm
    apply hξ
    exact Set.mem_iUnion.mpr ⟨L.val, Set.mem_iUnion.mpr ⟨L.property, hmξ⟩⟩
  obtain ⟨γ, hγ, hbound⟩ := Pi.exists_forall_pos_add_lt hp
  refine ⟨γ, hγ, fun L hL ↦ ?_⟩
  simpa only [zero_add] using (hbound ⟨L, hL⟩).le

/-- Every selected carrier has the positive directional gap used to control
same-patch sums (`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem CarrierSeed.exists_pos_badDirectionGap {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ) :
    ∃ γ > 0, BadDirectionGap γ ξ :=
  exists_pos_badDirectionGap_of_not_mem (h.not_mem_badSubspaceUnion hn)

/-- A positive directional gap implies avoidance of every bad subspace
(`app:ch_seed:prop:seed-frozen-menu`, Step 3). -/
theorem BadDirectionGap.not_mem_badSubspaceUnion {n : ℕ} {ξ : Euclidean n} {γ : ℝ}
    (hgap : BadDirectionGap γ ξ) (hγ : 0 < γ) : ξ ∉ cubeBadSubspaceUnion n := by
  classical
  intro hmem
  obtain ⟨L, hL, hξ⟩ := Set.mem_iUnion.mp hmem |>.imp fun L h ↦
    Set.mem_iUnion.mp h
  have hn : NormedSpace.normalize ξ ∈ L := L.smul_mem ‖ξ‖⁻¹ hξ
  have hz : Lᗮ.orthogonalProjectionOnto (NormedSpace.normalize ξ) = 0 := by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    simpa only [Submodule.orthogonal_orthogonal] using hn
  have hg := hgap L hL
  rw [hz, norm_zero] at hg
  exact (not_le_of_gt hγ) hg

/-- A common lower singular bound for all projected columns of an admissible
frame (`app:ch_seed:eq:seed-frozen-chord`). Finiteness makes this bound uniform
over the entire bad-subspace family. -/
theorem IsAdmissibleFrame.exists_uniform_lower_bound {n : ℕ} {k ξ : Euclidean n}
    {A : Euclidean 3 →L[ℝ] Euclidean n} (hA : IsAdmissibleFrame k ξ A) :
    ∃ a > 0, ∀ L ∈ cubeBadSubspaces n, ∀ v : Euclidean 3,
      a * ‖v‖ ≤ ‖Lᗮ.orthogonalProjectionOnto (A v)‖ := by
  classical
  have hsingle (L : ↥(cubeBadSubspaces n)) :
      ∃ a : ℝ, 0 < a ∧ ∀ v : Euclidean 3,
        a * ‖v‖ ≤ ‖L.valᗮ.orthogonalProjectionOnto (A v)‖ := by
    let B := L.valᗮ.orthogonalProjectionOnto.comp A
    obtain ⟨K, hK, hbound⟩ := B.toLinearMap.injective_iff_antilipschitz.mp
      (hA.2.2 L.val L.property)
    have hK' : 0 < (K : ℝ) := hK
    refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hK', fun v ↦ ?_⟩
    have hb := ZeroHomClass.bound_of_antilipschitz B hbound v
    change (K : ℝ)⁻¹ * ‖v‖ ≤ ‖B v‖
    calc
      _ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * ‖B v‖) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hK'.le)
      _ = ‖B v‖ := by rw [← mul_assoc, inv_mul_cancel₀ hK'.ne', one_mul]
  choose a ha hb using hsingle
  obtain ⟨b, hbpos, hba⟩ := Pi.exists_forall_pos_add_lt ha
  refine ⟨b, hbpos, fun L hL v ↦ ?_⟩
  exact (mul_le_mul_of_nonneg_right (by simpa only [zero_add] using
    (hba ⟨L, hL⟩).le) (norm_nonneg v)).trans (hb ⟨L, hL⟩ v)

end JanetCartan.FrozenMenu
