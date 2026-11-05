module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CompactTensor
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.TransportComparison.ColoredIntegral

/-!
# The L2 colored-to-transport comparison from classical retained jets

The compact lift and affine parameter restriction prove its joint derivative
bound from the classical profiles. Applying the colored integral comparison
therefore assumes no L2 regularity or L2 derivative package. Consumer: the
comparison following `app:ch_waves:eq:background-quadrature`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.RetainedBackground
open SeparatedSampling LatticeQuadrature BackgroundQuadrature CompactTensor
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

variable {n : ℕ} {J : Set (Euclidean n)} (hJ : IsCompact J)
variable {H : ℝ → Point → Euclidean n → Matrix (Fin n) (Fin n) ℝ}
variable (hH : ContDiff ℝ ∞ (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2))
variable (hS : ∀ τ z x, x ∉ J → H τ z x = 0)

/-- Joint frequency/carrier jets of the literal L2 class follow from the
classical tensor jets, with only the fixed physical support cost. This is
used for the inverse-frequency comparison after
`app:ch_waves:eq:background-quadrature`. -/
theorem norm_iteratedFDeriv_backgroundL2_joint_le
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {L : ℝ} (hL : 1 ≤ L) {rpar : ℕ}
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
      ‖iteratedFDeriv ℝ j (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ ≤ A j * L ^ (j - rpar))
    {τ : ℝ} (hτ : τ ∈ Icc (-1 : ℝ) 1) (z : Point) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (backgroundL2 hJ hH hS) (τ, z)‖ ≤
      (physicalL2Constant hJ * A j) * L ^ (j - rpar) := by
  rw [mul_assoc]
  apply norm_iteratedFDeriv_family_le hJ (contDiff_uncurry_background hH)
    (fun a ↦ hS a.1 a.2) j (τ, z)
    (mul_nonneg (hA j) (pow_nonneg (zero_le_one.trans hL) _))
  intro x _
  let E : (ℝ × Point) →L[ℝ] ℝ × (Point × Euclidean n) :=
    (ContinuousLinearMap.fst ℝ ℝ Point).prod
      ((ContinuousLinearMap.snd ℝ ℝ Point).prod 0)
  have hE : ‖E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp [E, Prod.norm_def]
  have hh := norm_iteratedFDeriv_preAffine_le E (0, (0, x)) isOpen_univ
    hH.contDiffOn (x := (τ, z)) (mem_univ _) j
  have hh' : ‖iteratedFDeriv ℝ j (fun b : ℝ × Point ↦ H b.1 b.2 x) (τ, z)‖ ≤
      ‖iteratedFDeriv ℝ j (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ * ‖E‖ ^ j := by simpa [E] using hh
  exact (hh'.trans (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg E) hE))).trans (hj τ hτ z x j)

/-- The original color weights and radial labels obey the physical L2
`O(λ⁻¹)` comparison. All L2 smoothness and bounds are proved from classical
retained jets and the fixed compact physical support
(`app:ch_waves:eq:background-quadrature`, adjacent comparison). -/
theorem norm_backgroundL2_colored_sub_transport_le
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (hm : ∫ t, κ t = 1) (hn : ∀ t, 0 ≤ κ t)
    (hk : Function.support κ ⊆ Icc (-(1 / 4)) (1 / 4))
    {p : ℕ} (hp : 0 < p) {ψ : Point → ℝ} {B P : ℝ}
    (hψ : PatchBounds ψ B P) (hψc : Continuous ψ)
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {L : ℝ} (hL : 1 ≤ L)
    {rpar : ℕ} (hrpar : 1 ≤ rpar)
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
      ‖iteratedFDeriv ℝ j (fun q : ℝ × (Point × Euclidean n) ↦ H q.1 q.2.1 q.2.2)
        (τ, (z, x))‖ ≤ A j * L ^ (j - rpar))
    (R : (Fin 3 → Fin (p + 1)) → ℝ) (hR : ∀ c, 1 ≤ R c)
    {lam : ℝ} (hlam : 1 ≤ lam) {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) :
    ‖(∑ c, ∫ z : Point,
        coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p) h c z •
          (ψ z • backgroundL2 hJ hH hS ((R c * lam)⁻¹, z))) -
      ∫ z : Point, ψ z • backgroundL2 hJ hH hS (0, z)‖ ≤
        ((∫ z, ψ z) * (physicalL2Constant hJ * A 1)) * lam⁻¹ := by
  exact norm_colored_integral_sub_transport_le hc hs hm hn hk hp hψ hψc
    (contDiff_infty_backgroundL2 hJ hH hS)
    (mul_nonneg (physicalL2Constant_nonneg hJ) (hA 1)) hrpar
    (fun τ hτ z j ↦ norm_iteratedFDeriv_backgroundL2_joint_le hJ hH hS hA hL hj hτ z j)
    R hR hlam hh hh₁

end JanetCartan.Sampling.RetainedBackground
