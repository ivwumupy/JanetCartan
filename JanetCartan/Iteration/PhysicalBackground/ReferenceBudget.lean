module

public import JanetCartan.Iteration.PhysicalBackground.NormalizedBaseline

/-!
# Pre-σ raw reference budget

The strong reference producer supplies a Cfull estimate for the SAME
uncorrected raw inverse.  This leaf performs only the quantitative composition
with the literal normalized-reference source `O(σ)` bound: choose the source
scale before the source order and reserve, so the reference raw seed spends
half the fixed finite-low admission tolerance.  It does not identify the
current-history raw operator with the reference operator.
-/

@[expose] public noncomputable section
open Set

namespace JanetCartan.PhysicalBackground

/-- A pre-scale `Cfull` raw bound and a pre-scale linear source bound produce a
single source cap making the reference raw seed smaller than half the fixed
finite-low tolerance.  The caller instantiates `rawGrade` with the SAME
`rightInverse` raw correction from `StrongSourceGap.reference_uncorrected_raw`.
No current-operator continuity is used here. -/
theorem reference_rawSeed_half_budget
    (m : ℕ) (δ σcap : ℝ) (hδ : 0 < δ) (hcap : 0 < σcap)
    (Cfull B : ℕ → ℝ) (hCfull : ∀ s, 0 ≤ Cfull s) (hB : ∀ s, 0 ≤ B s)
    (rawGrade sourceGrade sourceNorm : ℝ → ℝ)
    (hraw : ∀ σ ∈ Ioc (0 : ℝ) σcap,
      rawGrade σ ≤ Cfull m * (sourceGrade σ + sourceNorm σ))
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) σcap,
      sourceGrade σ ≤ B m * σ)
    (hsourceNorm : ∀ σ ∈ Ioc (0 : ℝ) σcap,
      sourceNorm σ ≤ B 0 * σ) :
    ∃ σhalf > (0 : ℝ), σhalf ≤ σcap ∧
      ∀ σ ∈ Ioc (0 : ℝ) σhalf, rawGrade σ ≤ δ / 2 := by
  let A := Cfull m * (B m + B 0)
  let D := A + 1
  let σhalf := min σcap (δ / (2 * D))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (hCfull m) (add_nonneg (hB m) (hB 0))
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hδD : 0 < δ / (2 * D) := by positivity
  have hhalf : 0 < σhalf := lt_min hcap hδD
  have hhalfCap : σhalf ≤ σcap := min_le_left _ _
  refine ⟨σhalf, hhalf, hhalfCap, ?_⟩
  intro σ hσ
  have hσcap : σ ∈ Ioc (0 : ℝ) σcap :=
    ⟨hσ.1, hσ.2.trans hhalfCap⟩
  have hsum : sourceGrade σ + sourceNorm σ ≤ (B m + B 0) * σ := by
    have h₁ := hsource σ hσcap
    have h₂ := hsourceNorm σ hσcap
    nlinarith
  have hrawA : rawGrade σ ≤ A * σ := by
    calc
      rawGrade σ ≤ Cfull m * (sourceGrade σ + sourceNorm σ) := hraw σ hσcap
      _ ≤ Cfull m * ((B m + B 0) * σ) :=
        mul_le_mul_of_nonneg_left hsum (hCfull m)
      _ = A * σ := by ring
  have hσD : σ ≤ δ / (2 * D) := hσ.2.trans (min_le_right _ _)
  have hDσ : D * σ ≤ D * (δ / (2 * D)) :=
    mul_le_mul_of_nonneg_left hσD (le_of_lt hD)
  have hAσ : A * σ ≤ D * σ := by
    exact mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hσ.1.le
  calc
    rawGrade σ ≤ A * σ := hrawA
    _ ≤ D * σ := hAσ
    _ ≤ D * (δ / (2 * D)) := hDσ
    _ = δ / 2 := by field_simp [ne_of_gt hD]

end JanetCartan.PhysicalBackground
