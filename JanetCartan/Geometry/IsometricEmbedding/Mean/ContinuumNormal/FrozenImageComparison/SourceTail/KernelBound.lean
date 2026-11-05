module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.Model
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.KernelEnergy
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.CommutatorNormal.Tail.Realization

/-!
# Source tails for the frozen image comparison

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, specialize the existing
off-diagonal Bessel kernel calculus to the defect of the original source square.
The auxiliary endpoint mask has a proved positive separation from that defect.
The resulting double kernel is continuous and compactly supported; its energy
is absolutely convergent and bounded by the squared L¹ norm of a supported L²
input. Identifying it with the literal channel normal difference is separate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
open JanetCartan.PeriodicLocalL2
open JanetCartan.ContinuumRow
open JanetCartan.ContinuumNormalReduction.ImageNormal

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R²" => EuclideanL2 n E

/-- Real matrix action for the source-tail kernel in
`app:ch_background:prop:bg-frame`. -/
noncomputable def sourceTailMatrixCLM (M : Matrix (Fin n) (Fin n) ℝ) : E →L[ℝ] E :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

private theorem continuous_sourceTailMatrixCLM :
    Continuous (@sourceTailMatrixCLM n) := by
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] E →L[ℝ] E :=
    { toFun := sourceTailMatrixCLM
      map_add' := by
        intro M N
        ext x
        simp [sourceTailMatrixCLM]
      map_smul' := by
        intro c M
        ext x
        simp [sourceTailMatrixCLM] }
  exact L.continuous_of_finiteDimensional

/-- A supported Euclidean (L^2) field is Bochner integrable.  The support
condition is only almost everywhere, as it is for the zero-extension maps.
This is the (L^2)-to-(L^1) input for the fixed source-tail kernel
(`app:ch_background:prop:bg-frame`). -/
theorem integrable_supported_euclideanL2
    {R : ℝ} (_hR : 0 < R) (u : R²)
    (hu : ∀ᵐ x ∂volume, x ∉ ball (0 : E) R → u x = 0) :
    Integrable (u : E → E) := by
  have hball : volume (closedBall (0 : E) R) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hi : IntegrableOn (u : E → E) (closedBall (0 : E) R) :=
    integrableOn_Lp_of_measure_ne_top u (by norm_num) hball
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [hu] with x hx hxc
  exact hx (fun hxb ↦ hxc (ball_subset_closedBall hxb))

/-- The existing two-Bessel tail with constant differential coefficients, for
`app:ch_background:prop:bg-frame`. Its intermediate defect is `1 - β`. -/
noncomputable def frozenSourceTailMatrixKernel
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (χ μ β : E → ℝ)
    (p : E × E) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k ↦ coefficientSourceCommutatorTailKernel
    (fun _ ↦ A) (fun _ ↦ 0) χ μ β i k p

/-- Operator-valued form of the differentiated two-Bessel kernel for
`app:ch_background:prop:bg-frame`. -/
noncomputable def frozenSourceTailKernel
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (χ μ β : E → ℝ) :
    E × E → E →L[ℝ] E :=
  fun p ↦ sourceTailMatrixCLM (frozenSourceTailMatrixKernel A χ μ β p)

private theorem continuous_frozenSourceTailKernel
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (χ μ β : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    {δ : ℝ} (hδ : 0 < δ)
    (hplateau : ∀ x ∈ tsupport χ, ∀ z, dist x z < δ → β z = 1) :
    Continuous (frozenSourceTailKernel A χ μ β) := by
  have hm : Continuous (@sourceTailMatrixCLM n) := continuous_sourceTailMatrixCLM
  have hk : Continuous (frozenSourceTailMatrixKernel A χ μ β) := by
    apply continuous_matrix
    intro i k
    exact (contDiff_coefficientSourceCommutatorTailKernel
      (fun _ ↦ A) (fun _ ↦ 0) χ μ β
      (fun a i j ↦ contDiff_const) (fun i j ↦ contDiff_const)
      hχ hχc hμ hβ hβc hδ hplateau i k).continuous
  exact hm.comp hk

private theorem hasCompactSupport_frozenSourceTailKernel
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (χ μ β : E → ℝ)
    (hμc : HasCompactSupport μ) :
    HasCompactSupport (frozenSourceTailKernel A χ μ β) := by
  apply HasCompactSupport.intro (hμc.isCompact.prod hμc.isCompact)
  intro p hp
  have hz : μ p.1 = 0 ∨ μ p.2 = 0 := by
    by_cases h₁ : p.1 ∈ tsupport μ
    · exact Or.inr (image_eq_zero_of_notMem_tsupport (fun h₂ ↦ hp ⟨h₁, h₂⟩))
    · exact Or.inl (image_eq_zero_of_notMem_tsupport h₁)
  apply ContinuousLinearMap.ext
  intro v
  ext i
  change ((Matrix.toEuclideanLin (frozenSourceTailMatrixKernel A χ μ β p)).toContinuousLinearMap v).ofLp i = 0
  change (frozenSourceTailMatrixKernel A χ μ β p).mulVec v.ofLp i = 0
  have hzero : frozenSourceTailMatrixKernel A χ μ β p = 0 := by
    ext j k
    unfold frozenSourceTailMatrixKernel coefficientSourceCommutatorTailKernel
    rcases hz with hz | hz <;> simp [hz]
  rw [hzero]
  simp

/-- The square of the original source mask, kept between the two Bessel
factors in `app:ch_background:prop:bg-frame`. -/
def fixedSourceSquare {R : ℝ} (hR : 0 < R) (x : E) : ℝ :=
  (FixedCutoffs.physical hR 2 x) ^ 2

/-- The actual source square is smooth (`app:ch_background:prop:bg-frame`). -/
theorem contDiff_fixedSourceSquare {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fixedSourceSquare (n := n) hR) :=
  (FixedCutoffs.physical hR 2).contDiff.pow 2

/-- The actual source square is compactly supported
(`app:ch_background:prop:bg-frame`). -/
theorem hasCompactSupport_fixedSourceSquare {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fixedSourceSquare (n := n) hR) := by
  change HasCompactSupport (fun x : E ↦ (FixedCutoffs.physical hR 2 x) ^ 2)
  simpa only [pow_two, Pi.mul_def] using
    (FixedCutoffs.physical (n := n) hR 2).hasCompactSupport.mul_right
      (f' := (FixedCutoffs.physical hR 2 : E → ℝ))

/-- The radius-`R` gap from the auxiliary endpoint mask to the defect of the
original source square (`app:ch_background:prop:bg-frame`). -/
theorem fixedSourceSquare_plateau {R : ℝ} (hR : 0 < R) :
    ∀ x ∈ tsupport (FixedCutoffs.physical (n := n) hR 0),
      ∀ z, dist x z < R → fixedSourceSquare hR z = 1 := by
  intro x hx z hdist
  have hx' := FixedCutoffs.physical_tsupport hR 0 hx
  have hxnorm : ‖x‖ < 2 * R := by
    simpa using mem_ball_zero_iff.mp hx'
  have hzmem : z ∈ closedBall (0 : E) (3 * R) := by
    rw [mem_closedBall_zero_iff]
    have hzx : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
      calc
        ‖z‖ = ‖x - (x - z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - z‖ := norm_sub_le _ _
        _ = ‖x - z‖ + ‖x‖ := by ring
    rw [dist_eq_norm] at hdist
    linarith
  have hp : FixedCutoffs.physical hR 2 z = 1 := by
    apply interior_subset (FixedCutoffs.physical_plateau hR 2 _)
    convert hzmem using 1; norm_num
  simp only [fixedSourceSquare, hp, one_pow]

/-- Apply the constant differential factors to the scalar tail
`χaux² J (1 - χsrc²) J χsrc²`, with `χaux` at both outer endpoints. All cutoffs
are the original physical cutoffs; their plateaux must still be used to identify
the supported-input energy (`app:ch_background:prop:bg-frame`). -/
def fixedSourceTailKernel {R : ℝ} (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : E × E → E →L[ℝ] E :=
  frozenSourceTailKernel A (FixedCutoffs.physical hR 0)
    (FixedCutoffs.physical hR 0) (fixedSourceSquare hR)

/-- Continuity of the concrete separated-source kernel follows from the
proved off-diagonal Bessel calculus (`app:ch_background:prop:bg-frame`). -/
theorem continuous_fixedSourceTailKernel {R : ℝ} (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fixedSourceTailKernel hR A) :=
  continuous_frozenSourceTailKernel A _ _ _
    (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport
    (FixedCutoffs.physical hR 0).contDiff (contDiff_fixedSourceSquare hR)
    (hasCompactSupport_fixedSourceSquare hR) hR (fixedSourceSquare_plateau hR)

/-- Compactness of both kernel endpoints; the intermediate source defect
itself remains noncompact (`app:ch_background:prop:bg-frame`). -/
theorem hasCompactSupport_fixedSourceTailKernel {R : ℝ} (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    HasCompactSupport (fixedSourceTailKernel hR A) :=
  hasCompactSupport_frozenSourceTailKernel A _ _ _
    (FixedCutoffs.physical hR 0).hasCompactSupport

/-- Every intermediate scalar Bessel integral for the actual source-square
defect is absolutely convergent (`app:ch_background:prop:bg-frame`). -/
theorem integrable_fixedSourceTail_bessel {R : ℝ} (hR : 0 < R) (x y : E) :
    Integrable (fun z ↦
      imageCommutatorTailSection (FixedCutoffs.physical hR 0)
        (fixedSourceSquare hR) (x, z) * imageBesselKernel (z - y)) :=
  integrable_imageCommutatorTailSection_mul_bessel _ _
    (FixedCutoffs.physical hR 0).contDiff (FixedCutoffs.physical hR 0).hasCompactSupport
    (contDiff_fixedSourceSquare hR) (hasCompactSupport_fixedSourceSquare hR)
    hR (fixedSourceSquare_plateau hR) x y

/-- The actual compact source-square kernel has an absolutely convergent
energy bounded by a fixed constant times the squared L¹ norm of any supported
L² input (`app:ch_background:prop:bg-frame`). Identifying this energy with the
channel normal difference remains a separate obligation. -/
theorem exists_fixedSourceTail_kernel_bound
    {R : ℝ} (hR : 0 < R) (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : R²,
      (∀ᵐ x ∂volume, x ∉ ball (0 : E) R → u x = 0) →
      Integrable (fun p : E × E ↦ ⟪u p.1, fixedSourceTailKernel hR A p (u p.2)⟫)
        (volume.prod volume) ∧
      |∫ x, ∫ y, ⟪u x, fixedSourceTailKernel hR A (x, y) (u y)⟫| ≤
        C * (∫ x, ‖u x‖) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_compactKernel_energy_bound (fixedSourceTailKernel hR A)
    (continuous_fixedSourceTailKernel hR A) (hasCompactSupport_fixedSourceTailKernel hR A)
  exact ⟨C, hC, fun u hu ↦ hb u (integrable_supported_euclideanL2 hR u hu)⟩

end JanetCartan.ContinuumNormal.FrozenImageComparison
