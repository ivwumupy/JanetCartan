module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.Rescaling

/-!
# No omitted background blocks

The finite enumeration loses no block integral on the compact patch in
`app:ch_waves:eq:background-quadrature`.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.Sampling.BackgroundQuadrature
open SeparatedSampling

/-- A block outside the fixed patch enumeration has zero weighted integrand
at every carrier point (`app:ch_waves:eq:background-quadrature`). -/
theorem patch_mul_blockWeight_eq_zero_outside {p : ℕ} {w : ℝ → ℝ} {M : ℝ}
    (hw : WindowBounds p w M) {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {q : Lattice} (hq : q ∉ integerCube (blockCutoff p B h)) (z : Point) :
    ψ z * blockWeight w h q z = 0 := by
  by_contra hn
  obtain ⟨hψz, hρ⟩ := mul_ne_zero_iff.mp hn
  apply hq
  apply mem_integerCube.mpr
  intro i
  have hs := hw.support _ ((Finset.prod_ne_zero_iff.mp hρ) i (Finset.mem_univ i))
  have hz := abs_le.mp (hψ.support z hψz i)
  have hdist : |z i - h * (q i : ℝ)| ≤ h * windowRadius p := by
    have he : z i - h * (q i : ℝ) = h * (z i / h - (q i : ℝ)) := by field_simp
    rw [he, abs_mul, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left hs hh.le
  have hd := abs_le.mp hdist
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hb : |(q i : ℝ)| ≤ (B + (p : ℝ) + 2) / h := by
    rw [abs_le]
    dsimp [windowRadius] at hd
    constructor
    · rw [neg_le, le_div_iff₀ hh]
      nlinarith [hd.1, hd.2]
    · rw [le_div_iff₀ hh]
      nlinarith [hd.1, hd.2]
  have hceil := hb.trans (Nat.le_ceil ((B + (p : ℝ) + 2) / h))
  exact_mod_cast hceil

/-- The finite block integrals are the full lattice sum, with convergence
proved from patch support (`app:ch_waves:eq:background-quadrature`). -/
theorem hasSum_blockIntegrals {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p : ℕ} {w : ℝ → ℝ} {M : ℝ} (hw : WindowBounds p w M)
    {ψ : Point → ℝ} {B P : ℝ} (hψ : PatchBounds ψ B P)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (H : (Fin 3 → Fin (p + 1)) → Point → V) :
    HasSum (fun q : Lattice ↦ ∫ z : Point, blockWeight w h q z • (ψ z • H (color p q) z))
      (∑ q ∈ integerCube (blockCutoff p B h),
        ∫ z : Point, blockWeight w h q z • (ψ z • H (color p q) z)) := by
  apply hasSum_sum_of_ne_finset_zero
  intro q hq
  have he (z : Point) : blockWeight w h q z • (ψ z • H (color p q) z) = 0 := by
    rw [smul_smul, mul_comm, patch_mul_blockWeight_eq_zero_outside hw hψ hh hh₁ hq z,
      zero_smul]
  simp_rw [he, integral_zero]

end JanetCartan.Sampling.BackgroundQuadrature
