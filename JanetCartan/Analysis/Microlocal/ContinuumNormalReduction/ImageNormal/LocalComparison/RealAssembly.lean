module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.BoundedComparison
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RealVector
/-!
# The actual real periodic inverse in the local chart

The bounded scalar comparison is instantiated with the constructed complex
periodic multiplier, then transferred coordinatewise to
`ContinuumRow.periodicBesselInverse`. The actual cell restriction and zero
extension preserve their respective torus and Euclidean measures. The error
is the explicit nonzero-lattice kernel, not an exact equality of periodic and
Euclidean kernels. This supplies `app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound JanetCartan.ContinuumNormal
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "R²" => Lp (EuclideanSpace ℝ I) 2 (volume : Measure E)

private theorem physicalMultiplier_realProjection
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) (f : L²) :
    imageScalarRealProjection.compLpL 2 volume (freezingPhysicalMultiplier χ hχ hχs f) =
      freezingPhysicalMultiplier χ hχ hχs (imageScalarRealProjection.compLpL 2 volume f) := by
  apply Lp.ext
  filter_upwards [imageScalarRealProjection.coeFn_compLpL (freezingPhysicalMultiplier χ hχ hχs f),
    freezingPhysicalMultiplier_coeFn χ hχ hχs f,
    freezingPhysicalMultiplier_coeFn χ hχ hχs (imageScalarRealProjection.compLpL 2 volume f),
    imageScalarRealProjection.coeFn_compLpL f] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, map_smul]

/-- Bounded multiplication by a fixed compact real cutoff on actual vector
Lebesgue L² (`app:ch_background:defn:bg-row`). -/
def realImageCutoffOperator (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) :
    R² →L[ℝ] R² :=
  realImageDiagonalL2Operator (freezingPhysicalMultiplier χ hχ hχs)

/-- The actual real cutoff intertwines with scalar complex multiplication
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexifiedL2Coordinate_realImageCutoffOperator
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) (f : R²) (i : I) :
    complexifiedL2Coordinate volume i (realImageCutoffOperator χ hχ hχs f) =
      freezingPhysicalMultiplier χ hχ hχs (complexifiedL2Coordinate volume i f) :=
  complexifiedL2Coordinate_realImageDiagonalL2Operator _
    (physicalMultiplier_realProjection χ hχ hχs) f i

/-- The real cutoff has its literal pointwise multiplication action
(`app:ch_background:defn:bg-row`). -/
theorem realImageCutoffOperator_coe
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) (f : R²) :
    realImageCutoffOperator χ hχ hχs f =ᵐ[volume] fun x ↦ χ x • f x := by
  have h (i : I) := complexifiedL2Coordinate_realImageCutoffOperator χ hχ hχs f i
  have hc (i : I) : ∀ᵐ x ∂volume,
      (realImageCutoffOperator χ hχ hχs f x i : ℂ) = (χ x * f x i : ℝ) := by
    filter_upwards [complexifiedL2Coordinate_coe volume i (realImageCutoffOperator χ hχ hχs f),
      freezingPhysicalMultiplier_coeFn χ hχ hχs (complexifiedL2Coordinate volume i f),
      complexifiedL2Coordinate_coe volume i f] with x h₁ h₂ h₃
    rw [h i] at h₁
    rw [← h₁, h₂, h₃]
    simp only [Complex.real_smul, Complex.ofReal_mul]
  filter_upwards [ae_all_iff.mpr hc] with x hx
  ext i
  exact Complex.ofReal_injective (hx i)

/-- The real cutoff is literally self-adjoint
(`app:ch_background:defn:bg-row`). -/
theorem realImageCutoffOperator_adjoint
    (χ : E → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ) :
    (realImageCutoffOperator (I := I) χ hχ hχs).adjoint =
      realImageCutoffOperator χ hχ hχs := by
  apply IsSelfAdjoint.adjoint_eq
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro u v
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realImageCutoffOperator_coe χ hχ hχs u,
    realImageCutoffOperator_coe χ hχ hχs v] with x hx hy
  change inner ℝ (realImageCutoffOperator χ hχ hχs u x) (v x) =
    inner ℝ (u x) (realImageCutoffOperator χ hχ hχs v x)
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right]

private theorem adjoint_sandwich_add
    (L B N S Q : R² →L[ℝ] R²) (hL : L.adjoint = L) (hB : B.adjoint = B)
    (hN : N.adjoint = N) (hS : S.adjoint = Q) :
    (L ∘L B ∘L N + S).adjoint = N ∘L B ∘L L + Q := by
  simp only [map_add, ContinuousLinearMap.adjoint_comp, hN, hB, hL, hS,
    ContinuousLinearMap.comp_assoc]

variable {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1 / 2) (χ ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)
local notation "Mχ" => realImageCutoffOperator (I := Fin d) (d := d) χ hχ.continuous
  (hasCompactSupport_of_imageBessel_cube_support χ hχs)
local notation "Mψ" => realImageCutoffOperator (I := Fin d) (d := d) ψ hψ.continuous
  (hasCompactSupport_of_imageBessel_cube_support ψ hψs)
local notation "R" => realLocalizedImageBesselRemainderOperator (I := Fin d) (d := d) hr χ ψ hχ hψ hχs hψs

include hr₀ in
set_option backward.isDefEq.respectTransparency false in
/-- The actual periodic Bessel inverse, localized in one interior cube, equals
the localized Euclidean Bessel multiplier plus the explicit smooth remainder
(`app:ch_background:prop:bg-frame`, Step 1). The Fourier-action premise is
fully discharged by the actual periodic producer, including dimension zero. -/
theorem periodicBesselInverse_localized_eq_add_remainder :
    Mχ ∘L (PeriodicLocalL2.toEuclidean (n := d) (𝕜 := ℝ) (F := E)).toContinuousLinearMap ∘L
      ContinuumRow.periodicBesselInverse ∘L
      PeriodicLocalL2.toTorus (n := d) (𝕜 := ℝ) (F := E) ∘L Mψ =
    Mχ ∘L realImageBesselL2Operator ∘L Mψ + R := by
  ext1 f
  apply eq_of_complexifiedL2Coordinate_eq volume
  intro i
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_add,
    LinearIsometry.coe_toContinuousLinearMap,
    complexifiedL2Coordinate_realImageCutoffOperator,
    complexifiedL2Coordinate_toEuclidean, complexifiedL2Coordinate_periodicBesselInverse,
    complexifiedL2Coordinate_toTorus, complexifiedL2Coordinate_realImageBesselL2Operator,
    complexifiedL2Coordinate_realLocalizedImageBesselRemainderOperator]
  exact congrArg (fun T : L² →L[ℂ] L² ↦ T (complexifiedL2Coordinate volume i f))
    (periodicBessel_localized_L2_eq_add_remainder hr₀ hr χ ψ hχ hψ hχs hψs
      complexPeriodicBesselOperator mFourierCoeff_complexPeriodicBesselOperator)

include hr₀ in
/-- The literal adjoint of the localized real comparison reverses both masks
and the actual remainder kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem periodicBesselInverse_localized_adjoint_eq_add_remainder :
    (Mχ ∘L (PeriodicLocalL2.toEuclidean (n := d) (𝕜 := ℝ) (F := E)).toContinuousLinearMap ∘L
      ContinuumRow.periodicBesselInverse ∘L
      PeriodicLocalL2.toTorus (n := d) (𝕜 := ℝ) (F := E) ∘L Mψ).adjoint =
    Mψ ∘L realImageBesselL2Operator ∘L Mχ +
      realLocalizedImageBesselRemainderOperator hr ψ χ hψ hχ hψs hχs := by
  exact (congrArg ContinuousLinearMap.adjoint
    (periodicBesselInverse_localized_eq_add_remainder hr₀ hr χ ψ hχ hψ hχs hψs)).trans
    (adjoint_sandwich_add Mχ realImageBesselL2Operator Mψ R
      (realLocalizedImageBesselRemainderOperator hr ψ χ hψ hχ hψs hχs)
      (realImageCutoffOperator_adjoint χ hχ.continuous
        (hasCompactSupport_of_imageBessel_cube_support χ hχs))
      realImageBesselL2Operator_adjoint
      (realImageCutoffOperator_adjoint ψ hψ.continuous
        (hasCompactSupport_of_imageBessel_cube_support ψ hψs))
      (realLocalizedImageBesselRemainderOperator_adjoint hr χ ψ hχ hψ hχs hψs))

end JanetCartan.ContinuumNormalReduction.ImageNormal
