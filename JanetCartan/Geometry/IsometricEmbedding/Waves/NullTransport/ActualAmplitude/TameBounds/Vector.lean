module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Scalar

/-!
# Nullvector multiplication for the characteristic amplitude

The scalar and vector amplitude in `app:ch_waves:eq:joint-tame` have an
additive estimate with reserve six from the characteristic coefficient,
footpoint, initial scalar and nullvector. The scalar's low bound is proved
from fixed `C⁵` primitive budgets, never assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.NullTransport.AmplitudeTame

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Both the scalar and its nullvector product have one high norm. Fixed
`C⁵` budgets for the coefficient, footpoint and initial scalar produce the
scalar `C¹` budget used in the final multiplication; the nullvector requires
only `C¹` (`app:ch_waves:eq:joint-tame`). -/
theorem exists_cNorm_transportAmplitude_bounds
    (e : (ℝ × E) ≃L[ℝ] ℝ × E) (a : ℝ × E) (p : E)
    {ρ τ σ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) (hσ : 0 < σ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (U V W : Set (ℝ × E)) (L : Set E), IsOpen U → IsOpen V → IsOpen W → IsOpen L →
      e '' closedBall a ρ ⊆ U → Icc (-τ) τ ×ˢ closedBall p σ ⊆ V →
      e '' closedBall a ρ ⊆ W → closedBall p σ ⊆ L →
      ∀ (Y : ℝ × E → E) (c : ℝ × E → ℝ) (r : E → ℝ) (k : ℝ × E → F),
      ContDiffOn ℝ ∞ Y U → ContDiffOn ℝ ∞ c V → ContDiffOn ℝ ∞ r L → ContDiffOn ℝ ∞ k W →
      MapsTo (fun q ↦ (q.1, Y q)) (e '' closedBall a ρ)
        (Icc (-τ) τ ×ˢ closedBall p σ) →
      cNorm (e '' closedBall a ρ) 5 Y ≤ M →
      cNorm (Icc (-τ) τ ×ˢ closedBall p σ) 5 c ≤ M →
      cNorm (closedBall p σ) 5 r ≤ M → cNorm (e '' closedBall a ρ) 1 k ≤ M →
      ∀ j, cNorm (e '' closedBall a ρ) j (transportFromFootpoint c 0 r Y) +
          cNorm (e '' closedBall a ρ) j (fun q ↦ transportFromFootpoint c 0 r Y q • k q) ≤
        B j * (1 + cNorm (e '' closedBall a ρ) (j + 6) Y +
          cNorm (Icc (-τ) τ ×ˢ closedBall p σ) (j + 6) c +
          cNorm (closedBall p σ) (j + 6) r + cNorm (e '' closedBall a ρ) (j + 6) k) := by
  let K := e '' closedBall a ρ
  let J := Icc (-τ) τ ×ˢ closedBall p σ
  obtain ⟨A, hA, hscalar⟩ := exists_cNorm_transportFromFootpoint_bounds e a p hρ hτ hσ hM
  choose P hP hp using fun j ↦ exists_cNorm_smul_le_ballImage (F := F) e a hρ j
    (mul_nonneg (hA 1).le (by linarith : 0 ≤ 1 + 3 * M)) hM
  let B := fun j ↦ A j + P j * (1 + A (j + 2))
  refine ⟨B, fun j ↦ add_pos (hA j) (mul_pos (hP j) (by linarith [hA (j + 2)])), ?_⟩
  intro U V W L hU hV hW hL hKU hJV hKW hBL Y c r k hY hc hr hk hm hYlow hclow hrlow hklow j
  have hs (i) := hscalar U V L hU hV hL hKU hJV hBL Y c r hY hc hr hm
    ((cNorm_mono_order (by omega : 3 ≤ 5)).trans hYlow)
    ((cNorm_mono_order (by omega : 3 ≤ 5)).trans hclow)
    ((cNorm_mono_order (by omega : 3 ≤ 5)).trans hrlow) i
  let α := transportFromFootpoint c 0 r Y
  have hα1 : cNorm K 1 α ≤ A 1 * (1 + 3 * M) := by
    apply (hs 1).trans
    apply mul_le_mul_of_nonneg_left _ (hA 1).le
    change 1 + cNorm K 5 Y + cNorm J 5 c + cNorm (closedBall p σ) 5 r ≤ _
    linarith
  obtain ⟨W', hW', hKW', hα⟩ :=
    exists_transportFromFootpoint_smooth_near hτ hσ hU hV hL hKU hJV hBL hY hc hr hm
  have hh := hp j (W' ∩ W) (hW'.inter hW) (fun q hq ↦ ⟨hKW' hq, hKW hq⟩)
    α k (hα.mono inter_subset_left) (hk.mono inter_subset_right) hα1 hklow
  let Z := 1 + cNorm K (j + 6) Y + cNorm J (j + 6) c +
    cNorm (closedBall p σ) (j + 6) r + cNorm K (j + 6) k
  have hZ : 1 ≤ Z := by
    dsimp [Z]
    linarith [cNorm_nonneg K (j + 6) Y, cNorm_nonneg J (j + 6) c,
      cNorm_nonneg (closedBall p σ) (j + 6) r, cNorm_nonneg K (j + 6) k]
  have hαj : cNorm K j α ≤ A j * Z := by
    apply (hs j).trans
    apply mul_le_mul_of_nonneg_left _ (hA j).le
    dsimp [Z]
    linarith [cNorm_mono_order (s := K) (f := Y) (by omega : j + 4 ≤ j + 6),
      cNorm_mono_order (s := J) (f := c) (by omega : j + 4 ≤ j + 6),
      cNorm_mono_order (s := closedBall p σ) (f := r) (by omega : j + 4 ≤ j + 6),
      cNorm_nonneg K (j + 6) k]
  have hαj2 : cNorm K (j + 2) α ≤ A (j + 2) * Z := by
    apply (hs (j + 2)).trans
    apply mul_le_mul_of_nonneg_left _ (hA (j + 2)).le
    dsimp [Z]
    simp only [Nat.add_assoc]
    linarith [cNorm_nonneg K (j + 6) k]
  have hkZ : 1 + cNorm K (j + 2) k ≤ Z := by
    dsimp [Z]
    linarith [cNorm_mono_order (s := K) (f := k) (by omega : j + 2 ≤ j + 6),
      cNorm_nonneg K (j + 6) Y, cNorm_nonneg J (j + 6) c,
      cNorm_nonneg (closedBall p σ) (j + 6) r]
  have hv : cNorm K j (fun q ↦ α q • k q) ≤ P j * (1 + A (j + 2)) * Z := by
    apply hh.trans
    calc
      _ ≤ P j * ((1 + A (j + 2)) * Z) :=
        mul_le_mul_of_nonneg_left (by linarith) (hP j).le
      _ = _ := by ring
  exact (add_le_add hαj hv).trans_eq (by dsimp [B]; ring)

end JanetCartan.NullTransport.AmplitudeTame
