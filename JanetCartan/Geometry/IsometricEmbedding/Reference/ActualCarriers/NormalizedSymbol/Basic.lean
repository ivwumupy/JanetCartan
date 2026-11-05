module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PencilContinuity
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The literal normalized determinant symbol

Step 1 of `app:ch_seed:prop:seed-actual-menu` uses
`h_F(x, ξ) = p_F(x, ξ) |ξ|^(1-n)`. These algebraic identities apply to any
frame, hence in particular to the symmetric projected stress frame. Smoothness
is asserted only off the zero covector. The physical frame and its smoothness
are inputs supplied by the projected-frame construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

/-- The positive normalizing factor in `app:ch_seed:prop:seed-actual-menu`, Step 1. -/
def determinantNormalization {n : ℕ} (ξ : Euclidean n) : ℝ :=
  ‖ξ‖ ^ (1 - (n : ℤ))

/-- The literal real degree-one symbol of `app:ch_seed:prop:seed-actual-menu`, Step 1. -/
def normalizedSymbol {n : ℕ} (Q : Euclidean n → Fin n → MetricTensor n)
    (z : Euclidean n × Euclidean n) : ℝ :=
  determinant (Q z.1) z.2 * determinantNormalization z.2

/-- Phase space over a physical patch with zero covectors excluded
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
def normalizedSymbolDomain {n : ℕ} (Ω : Set (Euclidean n)) :
    Set (Euclidean n × Euclidean n) := Ω ×ˢ {ξ | ξ ≠ 0}

/-- The punctured phase-space domain is open (`app:lem:common-hamilton-phase`). -/
theorem isOpen_normalizedSymbolDomain {n : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) : IsOpen (normalizedSymbolDomain Ω) :=
  hΩ.prod isOpen_ne

/-- Positivity of the normalization on the nonzero covectors used in
`app:ch_seed:prop:seed-actual-menu`, Step 1. -/
theorem determinantNormalization_pos {n : ℕ} {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    0 < determinantNormalization ξ := zpow_pos (norm_pos_iff.mpr hξ) _

/-- Smoothness of the normalization away from zero, for
`app:ch_seed:prop:seed-actual-menu`, Step 1. -/
theorem contDiffAt_determinantNormalization {n : ℕ} {ξ : Euclidean n} (hξ : ξ ≠ 0) :
    ContDiffAt ℝ ∞ determinantNormalization ξ := by
  have hn := contDiffAt_norm ℝ (n := (∞ : ℕ∞ω)) hξ
  unfold determinantNormalization
  generalize (1 - (n : ℤ)) = k
  cases k with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hn.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hn.pow (k + 1)).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr hξ))

/-- The current determinant has degree `n` in the covector
(`app:ch_seed:setup:seed-current`). -/
theorem determinant_smul {n : ℕ} (Q : Fin n → MetricTensor n)
    (ξ : Euclidean n) (r : ℝ) : determinant Q (r • ξ) = r ^ n * determinant Q ξ := by
  have hp : pencil Q (r • ξ) = r • pencil Q ξ :=
    (pencilContinuousLinearMap Q).map_smul r ξ
  simp [determinant, hp]

/-- Positive degree-one homogeneity, proved from the determinant formula
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem normalizedSymbol_pos_homogeneous {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (z : Euclidean n × Euclidean n)
    {r : ℝ} (hr : 0 < r) :
    normalizedSymbol Q (z.1, r • z.2) = r * normalizedSymbol Q z := by
  simp only [normalizedSymbol, determinant_smul, determinantNormalization,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_zpow]
  have he : r ^ n * r ^ (1 - (n : ℤ)) = r := by
    rw [← zpow_natCast, ← zpow_add₀ hr.ne']
    simp
  calc
    _ = (r ^ n * r ^ (1 - (n : ℤ))) *
        (determinant (Q z.1) z.2 * ‖z.2‖ ^ (1 - (n : ℤ))) := by ring
    _ = _ := by rw [he]

/-- Smoothness of the literal symbol jointly in physical and covector variables,
from smoothness of the actual frame (`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem contDiffAt_normalizedSymbol {n : ℕ}
    {Q : Euclidean n → Fin n → MetricTensor n} {z : Euclidean n × Euclidean n}
    (hQ : ContDiffAt ℝ ∞ Q z.1) (hξ : z.2 ≠ 0) :
    ContDiffAt ℝ ∞ (normalizedSymbol Q) z :=
  (contDiff_determinant.contDiffAt.comp z
    ((hQ.comp z contDiffAt_fst).prodMk contDiffAt_snd)).mul
      ((contDiffAt_determinantNormalization hξ).comp z contDiffAt_snd)

/-- Joint smoothness also includes every external frame parameter. This is the
qualitative parameter regularity needed in `app:ch_seed:prop:seed-actual-menu`,
Step 1; quantitative coefficient-jet bounds are a separate obligation. -/
theorem contDiffAt_normalizedSymbol_family {n : ℕ} {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Q : P × Euclidean n → Fin n → MetricTensor n}
    {z : (P × Euclidean n) × Euclidean n}
    (hQ : ContDiffAt ℝ ∞ Q z.1) (hξ : z.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun w : (P × Euclidean n) × Euclidean n ↦
      normalizedSymbol (fun x ↦ Q (w.1.1, x)) (w.1.2, w.2)) z :=
  (contDiff_determinant.contDiffAt.comp z
    ((hQ.comp z contDiffAt_fst).prodMk contDiffAt_snd)).mul
      ((contDiffAt_determinantNormalization hξ).comp z contDiffAt_snd)

/-- Smoothness on the punctured domain required by the common Hamilton phase
(`app:lem:common-hamilton-phase`). -/
theorem contDiffOn_normalizedSymbol {n : ℕ} {Ω : Set (Euclidean n)}
    (hΩ : IsOpen Ω) {Q : Euclidean n → Fin n → MetricTensor n}
    (hQ : ContDiffOn ℝ ∞ Q Ω) :
    ContDiffOn ℝ ∞ (normalizedSymbol Q) (normalizedSymbolDomain Ω) := by
  intro z hz
  exact (contDiffAt_normalizedSymbol (hQ.contDiffAt (hΩ.mem_nhds hz.1)) hz.2).contDiffWithinAt

/-- The normalized and determinant characteristic equations coincide off zero
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem normalizedSymbol_eq_zero_iff {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) {z : Euclidean n × Euclidean n}
    (hξ : z.2 ≠ 0) : normalizedSymbol Q z = 0 ↔ determinant (Q z.1) z.2 = 0 := by
  exact mul_eq_zero.trans (or_iff_left (ne_of_gt (determinantNormalization_pos hξ)))

/-- Equality of characteristic zero sets on a physical patch
(`app:ch_seed:prop:seed-actual-menu`, Step 1). -/
theorem normalizedSymbol_zero_set {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) (Ω : Set (Euclidean n)) :
    {z ∈ normalizedSymbolDomain Ω | normalizedSymbol Q z = 0} =
      {z ∈ normalizedSymbolDomain Ω | determinant (Q z.1) z.2 = 0} := by
  ext z
  exact and_congr_right fun hz ↦ normalizedSymbol_eq_zero_iff Q hz.2

end JanetCartan.ActualCarriers
