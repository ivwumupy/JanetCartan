module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.Localization
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel

/-!
# Concrete frozen image operators and their physical-frequency symbol

Shared objects for the comparison in `paper-v2.tex`,
`app:ch_background:prop:bg-frame`. The periodic and masked Euclidean channels
retain the original fixed outer masks. The uncut Euclidean channel is a finite
matrix of the already constructed bounded differentiated Bessel multipliers.
Its normal symbol is `M(k) M(k)ᵀ / (1 + ‖k‖²)` in radian frequency `k`.
Fourier energy uses complex Euclidean fibers, Mathlib's unit-period transform,
the substitution `k = 2πξ`, and the real part of the complex Hilbert pairing.
These definitions contain no asserted comparison or multiplier identity.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped FourierTransform
open JanetCartan.ContinuumRow JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential
open JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure E)
local notation "R²" => EuclideanL2 n E

/-- Constant periodic principal coefficients and zero connection coefficients
(`app:ch_background:prop:bg-frame`, the limit `σ = 0`). -/
def constantImageCoefficients (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ)
  | .inl (a, i, j) => ContinuousMap.const _ (A a i j)
  | .inr _ => 0

/-- The literal periodic channel with the fixed outer source and measurement
masks, chosen before an inner support radius (`app:ch_background:defn:bg-row`). -/
def fixedPeriodicChannel (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : OutputL2 n →L[ℝ] OutputL2 n :=
  imageChannel (constantImageCoefficients A)
    (FixedCutoffs.periodic hR hcell 1) (FixedCutoffs.periodic hR hcell 2)

/-- Pulling back the actual periodic channel preserves its adjoint norm on
cell zero extensions, with the literal restriction/extension maps
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_fixedPeriodicPullback_adjoint_zeroExtension
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (f : OutputL2 n) :
    ‖(pullback (fixedPeriodicChannel hR hcell A)).adjoint
      (toEuclidean (𝕜 := ℝ) f)‖ = ‖(fixedPeriodicChannel hR hcell A).adjoint f‖ := by
  rw [pullback_adjoint]
  change ‖toEuclidean (𝕜 := ℝ) ((fixedPeriodicChannel hR hcell A).adjoint
    (toTorus (𝕜 := ℝ) (toEuclidean (𝕜 := ℝ) f)))‖ = _
  rw [toTorus_toEuclidean, toEuclidean.norm_map]

/-- The same frozen channel on Lebesgue L² with both fixed physical masks.
The normal retains the source square between two Bessel factors
(`app:ch_background:prop:bg-frame`, Step 1). -/
def fixedEuclideanChannel (hR : 0 < R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : R² →L[ℝ] R² :=
  euclideanChannel (fun _ ↦ A) (fun _ ↦ 0)
    (FixedCutoffs.physical hR 2) (FixedCutoffs.physical hR 1)
    (fun _ _ _ ↦ contDiff_const) (fun _ _ ↦ contDiff_const)
    (FixedCutoffs.physical hR 2).contDiff (FixedCutoffs.physical hR 2).hasCompactSupport
    (FixedCutoffs.physical hR 1).contDiff (FixedCutoffs.physical hR 1).hasCompactSupport

/-- The uncut complex frozen channel, constructed from the actual bounded
`∂ₐ J` factors (`app:ch_background:prop:bg-frame`, the limit `σ = 0`). -/
def uncutComplexChannel (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : C² →L[ℂ] C² :=
  vectorMatrixL2Operator fun i j ↦ ∑ a, (A a i j : ℂ) • imageDerivativeBesselL2Operator a

/-- The real frozen uncut channel uses the existing real compression and
finite-dimensional Hilbert conventions (`app:ch_background:prop:bg-frame`). -/
def uncutRealChannel (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : R² →L[ℝ] R² :=
  realOutputCompression (uncutComplexChannel A)

/-- `M(k) = ∑ₐ kₐ Aₐ` in physical radian frequency; the differential symbol
is `i M(k)` (`app:ch_background:prop:bg-frame`, frozen image contribution). -/
def principalMatrix (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (k : E) :
    Matrix (Fin n) (Fin n) ℝ := ∑ a, k a • A a

/-- The exact real frozen image normal symbol in radian frequency
(`app:ch_background:prop:bg-frame`, frozen image contribution). -/
def normalMatrix (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (k : E) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 + ‖k‖ ^ 2)⁻¹ • (principalMatrix A k * (principalMatrix A k).transpose)

/-- Complex-linear action of the real normal matrix on the existing complex
Euclidean fiber (`app:ch_background:prop:bg-frame`, Plancherel step). -/
def normalComplexAction (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (k : E)
    (v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (((normalMatrix A k).map Complex.ofReal).mulVec v)

/-- The real Fourier energy at physical frequency `2πξ`. The transform is
the L² Fourier transform of the literal real-to-complex inclusion; for L¹
zero extensions it agrees almost everywhere with the ordinary Fourier
integral (`app:ch_background:prop:bg-frame`, Plancherel step). -/
def fourierEnergy (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : R²) : ℝ :=
  let û : C² := 𝓕 (l2ComplexInclusion volume u)
  ∫ ξ, (inner ℂ (û ξ) (normalComplexAction A ((2 * Real.pi) • ξ) (û ξ))).re

end JanetCartan.ContinuumNormal.FrozenImageComparison
