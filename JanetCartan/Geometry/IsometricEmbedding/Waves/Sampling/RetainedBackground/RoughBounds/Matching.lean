module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.RoughBounds.Sampling

/-!
# Physical restriction and matching under the unchanged sample weights

The actual carrier producer orders its variables as `(τ,z,x)`. Its physical
restriction is a contraction. Weighted equality then identifies the literal
sample and colored integral without any extension left in the physical rough
estimate `app:ch_waves:eq:background-quadrature-rough`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.Sampling.RetainedBackground
open SeparatedSampling BackgroundQuadrature
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Physical jets of the carrier-ordered family cost no derivatives or
constants (`app:ch_waves:eq:background-quadrature-rough`). -/
theorem norm_iteratedFDeriv_carrierPhysicalSlice_le
    {H : ℝ → Point → Euclidean n → V}
    (hH : ContDiff ℝ ∞ (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2))
    (τ : ℝ) (z : Point) (x : Euclidean n) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (H τ z) x‖ ≤
      ‖iteratedFDeriv ℝ j (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ := by
  let E : Euclidean n →L[ℝ] ℝ × (Point × Euclidean n) :=
    (0 : Euclidean n →L[ℝ] ℝ).prod ((0 : Euclidean n →L[ℝ] Point).prod
      (ContinuousLinearMap.id ℝ (Euclidean n)))
  have hE : ‖E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp [E, Prod.norm_def]
  have hh := norm_iteratedFDeriv_preAffine_le E (τ, (z, 0)) isOpen_univ
    hH.contDiffOn (x := x) (mem_univ _) j
  have hh' : ‖iteratedFDeriv ℝ j (H τ z) x‖ ≤
      ‖iteratedFDeriv ℝ j (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ * ‖E‖ ^ j := by simpa [E] using hh
  exact hh'.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg E) hE))

/-- Weighted matching preserves the actual sample sum, including its zero
weights (`app:ch_waves:eq:background-quadrature-rough`). -/
theorem background_sample_eq_of_weighted_eq
    {p : ℕ} {ψ : Point → ℝ} (B : ℝ) (window : ℝ → ℝ) (h : ℝ) (U : Lattice → Point)
    {H G : (Fin 3 → Fin (p + 1)) → Point → V}
    (he : ∀ c z, ψ z • H c z = ψ z • G c z) :
    (∑ a ∈ samples p B ψ window h U,
      weight ψ window h U a • H (color p a.1) (node h U a)) =
    ∑ a ∈ samples p B ψ window h U,
      weight ψ window h U a • G (color p a.1) (node h U a) := by
  apply Finset.sum_congr rfl
  intro a _
  have hw : weight ψ window h U a =
      (h ^ 3 * blockWeight window h a.1 (node h U a)) * ψ (node h U a) := by
    unfold weight
    ring
  rw [hw, mul_smul, mul_smul, he]
  simp only [smul_smul, mul_assoc]

/-- Weighted matching preserves the original colored carrier integrals
(`app:ch_waves:eq:background-quadrature-rough`). -/
theorem background_colored_eq_of_weighted_eq
    {p : ℕ} {ψ : Point → ℝ} (s : Finset Lattice) (window : ℝ → ℝ) (h : ℝ)
    {H G : (Fin 3 → Fin (p + 1)) → Point → V}
    (he : ∀ c z, ψ z • H c z = ψ z • G c z) :
    (∑ c, ∫ z : Point, coloredBlockMask p s window h c z • (ψ z • H c z)) =
      ∑ c, ∫ z : Point, coloredBlockMask p s window h c z • (ψ z • G c z) := by
  simp_rw [he]

end JanetCartan.Sampling.RetainedBackground
