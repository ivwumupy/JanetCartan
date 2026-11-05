module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.CompactFamily

/-!
# The named source-scaled amplitude

Shared input formulas for the transport deduction in
`app:ch_background:eq:bg-Nsigma`. These elementary identities do not assert
that the displayed amplitude solves the scaled geometric transport equation.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.NormalizedBackground.SourceGeometry

variable {E Z F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Source-scaled amplitude with unchanged carrier labels
(`app:ch_background:eq:bg-Nsigma`). -/
def sourceAmplitude (b : E × Z → F) (ρ : ℝ) (p : E × Z) : F :=
  ρ • b (ρ • p.1, p.2)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The normalized amplitude is precisely the regular pullback
(`app:ch_background:prop:bg-normalized`). -/
theorem inv_smul_sourceAmplitude (b : E × Z → F) {ρ : ℝ} (hρ : ρ ≠ 0) (p : E × Z) :
    ρ⁻¹ • sourceAmplitude b ρ p = normalizedPullback b (ρ, p) :=
  inv_smul_scaled_pullback b hρ p.1 p.2

/-- Smoothness of the named amplitude on the full inverse image of the seed
coefficient domain (`app:ch_background:prop:bg-normalized`). -/
theorem contDiffOn_sourceAmplitude {b : E × Z → F} {U : Set (E × Z)}
    (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (E × Z) ↦ sourceAmplitude b q.1 q.2)
      {q : ℝ × (E × Z) | (q.1 • q.2.1, q.2.2) ∈ U} :=
  contDiffOn_fst.smul (contDiffOn_normalizedPullback hb)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- For a positive seed scalar the rescaled scalar is positive at every
positive scale (`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceAmplitude_pos {a : E × Z → ℝ} {ρ : ℝ} {p : E × Z}
    (hρ : 0 < ρ) (ha : 0 < a (ρ • p.1, p.2)) : 0 < sourceAmplitude a ρ p :=
  mul_pos hρ ha

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The scalar multiplies the same pulled-back kernel vector
(`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceAmplitude_smul (a : E × Z → ℝ) (k : E × Z → F) (ρ : ℝ) (p : E × Z) :
    sourceAmplitude (fun q ↦ a q • k q) ρ p =
      sourceAmplitude a ρ p • k (ρ • p.1, p.2) := by
  simp only [sourceAmplitude, smul_smul, smul_eq_mul]

omit [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- The unchanged linear Cauchy section has scalar exactly `ρ`, from the seed
scalar value `1` (`app:ch_background:eq:bg-Nsigma`). -/
theorem sourceAmplitude_initial_scalar {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a : E × Z → ℝ} (j : Y →L[ℝ] E) {ρ : ℝ} {u : Y} {z : Z}
    (ha : a (j (ρ • u), z) = 1) : sourceAmplitude a ρ (j u, z) = ρ := by
  rw [j.map_smul] at ha
  simp [sourceAmplitude, ha]

end JanetCartan.NormalizedBackground.SourceGeometry
