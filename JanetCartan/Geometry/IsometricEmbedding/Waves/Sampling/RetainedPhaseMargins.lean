module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.PhaseMatching
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.PowTwoComparison

/-!
# One retained phase margin for every color and original band

Choose the frequency-to-ceiling constant from the supplied finite geometry,
before the ceiling, radial labels, current fields or histories. The actual
inverse frequencies then satisfy all phase-domain inputs of the retained
product event. The normalization is `2^j`, twice the unchanged dyadic scale;
no band is reindexed and no iteration exponent is changed.
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase NormalComparison RawInputPartition
open MeasuredAmplitude MeasuredAmplitude.ColoredApplication

/-- A single fixed constant supplies the actual retained event's nonzero
inverse frequencies, radial interval and BOTH phase buffers on every band
of the original ceiling, as well as the colored comparison's full-ceiling
buffer and the background's frequency lower bound. The normal buffer belongs to the same supplied
geometry (`app:ch_waves:setup:oscillatory`,
`app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_retained_sampling_phase_margin_constant
    {m : ℕ} {J : Type*} [Fintype J]
    {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (ρ : J → ℝ) (hρ : ∀ a, 0 < ρ a)
    (G : J → UniformNormalGeometry (m + 1) (m + 1))
    {Rmin : ℝ} (hRmin : 0 < Rmin) :
    ∃ Cscale > 0, ∀ Λ : ℝ, 1 ≤ Λ → ∀ lam : ℝ, Cscale * Λ ≤ lam →
      1 ≤ lam ∧ 1 ≤ Rmin * lam ∧
        (∀ a, 2 * Λ / (Rmin * lam) ≤ (G a).ε₀) ∧
        ∀ (p : ℕ) (R : J → (Fin 3 → Fin (p + 1)) → ℝ),
        (∀ a color, Rmin ≤ R a color) → ∀ a color,
        (R a color * lam)⁻¹ ∈ Icc (-1 : ℝ) 1 ∧ (R a color * lam)⁻¹ ≠ 0 ∧
        ∀ j : Fin (cutoffCount Λ),
          |(R a color * lam)⁻¹| * (2 : ℝ) ^ j.val ≤ measuredPhaseRadius T hP (ρ := ρ a) ∧
          (R a color * lam)⁻¹ * (2 : ℝ) ^ j.val ∈ Icc 0 (G a).ε₀ := by
  classical
  let δ := fun a ↦ min (measuredPhaseRadius T hP (ρ := ρ a)) (G a).ε₀
  have hδ (a : J) : 0 < δ a :=
    lt_min (measuredPhaseRadius_pos T (hρ a) hP) (G a).ε₀_pos
  let D := fun a ↦ 2 / (Rmin * δ a)
  have hD (a : J) : 0 ≤ D a :=
    div_nonneg (by norm_num) (mul_pos hRmin (hδ a)).le
  let Cscale := 1 + Rmin⁻¹ + ∑ a, D a
  have hsum : 0 ≤ ∑ a, D a := Finset.sum_nonneg fun a _ ↦ hD a
  have hC₁ : 1 ≤ Cscale := by dsimp [Cscale]; linarith [inv_pos.mpr hRmin]
  have hCR : Rmin⁻¹ ≤ Cscale := by dsimp [Cscale]; linarith
  have hCD (a : J) : D a ≤ Cscale := by
    have ha := Finset.single_le_sum (fun b _ ↦ hD b) (Finset.mem_univ a)
    dsimp only [Cscale]
    linarith [inv_pos.mpr hRmin]
  refine ⟨Cscale, zero_lt_one.trans_le hC₁, ?_⟩
  intro Λ hΛ lam hlam
  have hClam : Cscale ≤ lam :=
    (le_mul_of_one_le_right (zero_le_one.trans hC₁) hΛ).trans hlam
  have hlam₁ : 1 ≤ lam := hC₁.trans hClam
  have hlampos : 0 < lam := zero_lt_one.trans_le hlam₁
  have hlamR : Rmin⁻¹ ≤ lam := hCR.trans hClam
  have hbuffer (a : J) : 2 * Λ / (Rmin * lam) ≤ δ a := by
    apply (div_le_iff₀ (mul_pos hRmin hlampos)).mpr
    have hDl : D a * Λ ≤ lam :=
      (mul_le_mul_of_nonneg_right (hCD a) (zero_le_one.trans hΛ)).trans hlam
    calc
      2 * Λ = (Rmin * δ a) * (D a * Λ) := by
        dsimp only [D]
        field_simp [hRmin.ne', (hδ a).ne']
      _ ≤ (Rmin * δ a) * lam :=
        mul_le_mul_of_nonneg_left hDl (mul_pos hRmin (hδ a)).le
      _ = δ a * (Rmin * lam) := by ring
  have hRminLam : 1 ≤ Rmin * lam := calc
    1 = Rmin * Rmin⁻¹ := (mul_inv_cancel₀ hRmin.ne').symm
    _ ≤ Rmin * lam := mul_le_mul_of_nonneg_left hlamR hRmin.le
  refine ⟨hlam₁, hRminLam, fun a ↦ (hbuffer a).trans (min_le_right _ _), ?_⟩
  intro p R hR a color
  have hRpos : 0 < R a color := hRmin.trans_le (hR a color)
  have hprod : 0 < R a color * lam := mul_pos hRpos hlampos
  have hprod₁ : 1 ≤ R a color * lam := calc
    1 = Rmin * Rmin⁻¹ := (mul_inv_cancel₀ hRmin.ne').symm
    _ ≤ Rmin * lam := mul_le_mul_of_nonneg_left hlamR hRmin.le
    _ ≤ R a color * lam := mul_le_mul_of_nonneg_right (hR a color) hlampos.le
  refine ⟨⟨le_trans (by norm_num) (inv_pos.mpr hprod).le,
    (inv_le_one₀ hprod).mpr hprod₁⟩, inv_ne_zero hprod.ne', ?_⟩
  intro j
  have hscale : (2 : ℝ) ^ j.val ≤ 2 * Λ := by
    rw [powTwo_eq_twice_dyadicScale]
    exact mul_le_mul_of_nonneg_left ((lt_cutoffCount_iff hΛ j.val).mp j.isLt) (by norm_num)
  have hinv : (R a color * lam)⁻¹ ≤ (Rmin * lam)⁻¹ :=
    inv_anti₀ (mul_pos hRmin hlampos) (mul_le_mul_of_nonneg_right (hR a color) hlampos.le)
  constructor
  · rw [abs_of_pos (inv_pos.mpr hprod)]
    calc
      _ ≤ (Rmin * lam)⁻¹ * (2 * Λ) :=
        mul_le_mul hinv hscale (by positivity) (by positivity)
      _ = 2 * Λ / (Rmin * lam) := by ring
      _ ≤ δ a := hbuffer a
      _ ≤ measuredPhaseRadius T hP (ρ := ρ a) := min_le_left _ _
  · exact radial_powTwo_parameter_mem hRmin (hR a color) hlampos hΛ
      ((hbuffer a).trans (min_le_right _ _)) j.isLt

end JanetCartan.Sampling
