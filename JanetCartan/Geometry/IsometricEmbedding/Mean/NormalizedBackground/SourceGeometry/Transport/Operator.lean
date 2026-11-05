module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Phase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.ReferenceStrain
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.FlowAmplitude

/-!
# Source dilation of the literal reduced transport operator

The operator identity in `app:ch_background:eq:bg-Nsigma`, consumed by the
source-scaled positive null transport. Flatness is local on the original open
seed domain. The connection terms vanish by the induced metric identity; the
frame is the actual projected frame, not an independently supplied pullback.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

variable {n N : ℕ}

/-- The scaled connection vanishes on the inverse image of the original flat
domain (`app:ch_background:eq:bg-Nsigma`). -/
theorem christoffel_sourceDilation_eq_zero
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Euclidean n} (hx : ρ • x ∈ U)
    (i j k : Fin n) : christoffel (sourceDilation F ρ) x i j k = 0 := by
  apply PositiveBackground.christoffel_eq_zero_of_inducedMetric_one
    (U := (fun y ↦ ρ • y) ⁻¹' U)
    (hU.preimage (continuous_id.const_smul ρ)) _ hx
  intro y hy
  rw [inducedMetric_sourceDilation hρ
    ((hF.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)), hflat _ hy]

/-- The actual symmetrized covariant derivative scales on a flat seed domain.
The constant `c` is `ρ` for the amplitude and `1` for the selected kernel
(`app:ch_background:eq:bg-Nsigma`). -/
theorem symmCovariantDeriv_sourceDilation_pullback
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Euclidean n} (hx : ρ • x ∈ U)
    {b : Euclidean n → Euclidean n}
    (hb : ∀ j, DifferentiableAt ℝ (fun y ↦ b y j) (ρ • x)) (c : ℝ) :
    symmCovariantDeriv (sourceDilation F ρ) (fun y ↦ c • b (ρ • y)) x =
      (c * ρ) • symmCovariantDeriv F b (ρ • x) := by
  have hd (i j : Fin n) :
      partialDeriv (fun y ↦ (c • b (ρ • y)) j) x i =
        (c * ρ) * partialDeriv (fun y ↦ b y j) (ρ • x) i := by
    have h := (((hb j).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul ρ)).const_mul c).fderiv
    change fderiv ℝ (fun y ↦ c * b (ρ • y) j) x = _ at h
    simp only [partialDeriv, PiLp.smul_apply, smul_eq_mul, h,
      smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.map_smul, ContinuousLinearMap.id_apply]
    ring
  ext i j
  simp only [symmCovariantDeriv, hd, Matrix.smul_apply, smul_eq_mul,
    christoffel_sourceDilation_eq_zero hU hF hflat hρ hx,
    PositiveBackground.christoffel_eq_zero_of_inducedMetric_one hU hflat hx,
    zero_mul, Finset.sum_const_zero, sub_zero]
  ring

/-- Exact dilation of `P_F` with its actual projected frame on the original
flat rank domain (`app:ch_background:eq:bg-Nsigma`). The published projected
frame theorem uses the globally smooth seed map; flatness and rank remain local. -/
theorem reducedOperator_sourceDilation_pullback
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiff ℝ ∞ F)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Euclidean n} (hx : ρ • x ∈ U)
    (hrank : Set.range (normalMap F (ρ • x)) =
      (normalSpace F (ρ • x) : Set (Euclidean N)))
    {b : Euclidean n → Euclidean n}
    (hb : ∀ j, DifferentiableAt ℝ (fun y ↦ b y j) (ρ • x)) (c : ℝ) :
    NullTransport.reducedOperator (sourceDilation F ρ)
      (ProjectedStressFrame.projectedStress (sourceDilation F ρ))
      (fun y ↦ c • b (ρ • y)) x =
      (c * ρ) • NullTransport.reducedOperator F
        (ProjectedStressFrame.projectedStress F) b (ρ • x) := by
  ext i
  simp only [NullTransport.reducedOperator,
    ProjectedStressFrame.projectedStress_sourceDilation hρ hF x hrank,
    symmCovariantDeriv_sourceDilation_pullback hU hF.contDiffOn hflat hρ hx hb c,
    tensorPairing, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The manuscript's `P_{Gρ}[ρ b̂(ρx)] = ρ²(P_{F₀}b̂)(ρx)`, with carrier
labels held fixed (`app:ch_background:eq:bg-Nsigma`). -/
theorem reducedOperator_sourceAmplitude {Z : Type}
    {F : Euclidean n → Euclidean N} {U : Set (Euclidean n)}
    (hU : IsOpen U) (hF : ContDiff ℝ ∞ F)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Euclidean n} (hx : ρ • x ∈ U)
    (hrank : Set.range (normalMap F (ρ • x)) =
      (normalSpace F (ρ • x) : Set (Euclidean N)))
    {b : Euclidean n × Z → Euclidean n} {z : Z}
    (hb : ∀ j, DifferentiableAt ℝ (fun y ↦ b (y, z) j) (ρ • x)) :
    NullTransport.reducedOperator (sourceDilation F ρ)
      (ProjectedStressFrame.projectedStress (sourceDilation F ρ))
      (fun y ↦ sourceAmplitude b ρ (y, z)) x =
      ρ ^ 2 • NullTransport.reducedOperator F
        (ProjectedStressFrame.projectedStress F) (fun y ↦ b (y, z)) (ρ • x) := by
  simpa only [sourceAmplitude, pow_two] using
    reducedOperator_sourceDilation_pullback hU hF hflat hρ hx hrank hb ρ

end JanetCartan.NormalizedBackground.SourceGeometry
