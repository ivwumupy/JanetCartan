module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.Locality
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.FourierEnergy
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.SourceTail

/-!
# The fixed frozen image comparison

The image contribution to `paper-v2.tex`, `app:ch_background:prop:bg-frame`,
for the literal periodic/source-mask channel of `paper.tex`,
`app:ch_background:defn:bg-row`. The two proved normal-kernel estimates and
the uncut Fourier identity apply to the same fixed operators. Their sum gives
one L¹-squared error constant before any inner radius or supported L² input
is chosen. Coefficient agreement is needed only on the measurement plateau.

The periodic estimate includes both cross terms and the remainder square;
the source estimate retains the source square between both Bessel factors.
Their all-data proofs already justify passage from smooth tests to L².
No comparison, kernel bound, or density premise remains in this assembly.
-/

@[expose] public noncomputable section

open MeasureTheory Metric
open scoped FourierTransform
open JanetCartan.ContinuumRow JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual frozen image adjoint differs from its Euclidean Fourier energy
by a fixed L¹-squared error (`app:ch_background:prop:bg-frame`). Both outer
masks and the constant precede the inner radius. The coefficient extension may
vary away from the measurement plateau. This supplies the image comparison
needed by the parent continuum-normal construction, including dimension zero. -/
theorem exists_imageChannel_energyDifference_le_l1_sq
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, r ≤ R →
      ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ k z, FixedCutoffs.periodic hR hcell 1 z = 1 →
          c k z = constantImageCoefficients A k z) →
        ∀ f : OutputL2 n,
          (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : E) r → f z = 0) →
          |‖(imageChannel c (FixedCutoffs.periodic hR hcell 1)
              (FixedCutoffs.periodic hR hcell 2)).adjoint f‖ ^ 2 -
            fourierEnergy A (toEuclidean (𝕜 := ℝ) f)| ≤
              C * (∫ x, ‖toEuclidean (𝕜 := ℝ) f x‖) ^ 2 := by
  obtain ⟨Cper, hCper, hper⟩ := exists_fixedPeriodicEnergyDifference_le_l1_sq hR hcell A
  obtain ⟨Csrc, hCsrc, hsrc⟩ := exists_fixedSourceEnergyDifference_le_l1_sq hR A
  refine ⟨Cper + Csrc, add_nonneg hCper hCsrc, fun r hrR c hc f hf ↦ ?_⟩
  have hu := toEuclidean_supported_innerBall hR hcell hrR f hf
  have huR : ∀ᵐ x ∂volume, x ∉ ball (0 : E) R →
      toEuclidean (𝕜 := ℝ) f x = 0 := by
    filter_upwards [hu] with x hx hxR
    exact hx (fun hxr ↦ hxR (ball_subset_ball hrR hxr))
  rw [imageChannel_adjoint_eq_fixed_of_plateau hR hcell hrR A c hc f hf,
    ← norm_uncutRealChannel_adjoint_sq_eq_fourierEnergy]
  calc
    _ ≤ |‖(fixedPeriodicChannel hR hcell A).adjoint f‖ ^ 2 -
          ‖(fixedEuclideanChannel hR A).adjoint (toEuclidean (𝕜 := ℝ) f)‖ ^ 2| +
        |‖(fixedEuclideanChannel hR A).adjoint (toEuclidean (𝕜 := ℝ) f)‖ ^ 2 -
          ‖(uncutRealChannel A).adjoint (toEuclidean (𝕜 := ℝ) f)‖ ^ 2| :=
      abs_sub_le _ _ _
    _ ≤ Cper * (∫ x, ‖toEuclidean (𝕜 := ℝ) f x‖) ^ 2 +
        Csrc * (∫ x, ‖toEuclidean (𝕜 := ℝ) f x‖) ^ 2 :=
      add_le_add (hper f) (hsrc _ huR)
    _ = _ := by ring

/-- The frozen image comparison with the ordinary Fourier integral of the
actual Euclidean zero extension, together with exact L² norm preservation
(`app:ch_background:prop:bg-frame`). The complex Euclidean pairing is
conjugate-linear in its first argument; its real part is integrated at physical
radian frequency `2πξ`. The matrix action is precisely
`M(k) M(k)ᵀ / (1 + ‖k‖²)`, as defined by `normalComplexAction`.
No input regularity beyond supported real L² is required. -/
theorem exists_imageChannel_fourierIntegral_comparison
    (hR : 0 < R) (hcell : 4 * R < 1 / 2)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, r ≤ R →
      ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ k z, FixedCutoffs.periodic hR hcell 1 z = 1 →
          c k z = constantImageCoefficients A k z) →
        ∀ f : OutputL2 n,
          (∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : E) r → f z = 0) →
          let u := toEuclidean (𝕜 := ℝ) f
          let û := 𝓕 (fun x ↦ euclideanComplexInclusion (u x))
          ‖u‖ = ‖f‖ ∧
            |‖(imageChannel c (FixedCutoffs.periodic hR hcell 1)
                (FixedCutoffs.periodic hR hcell 2)).adjoint f‖ ^ 2 -
              ∫ ξ, (inner ℂ (û ξ)
                (normalComplexAction A ((2 * Real.pi) • ξ) (û ξ))).re| ≤
                  C * (∫ x, ‖u x‖) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_imageChannel_energyDifference_le_l1_sq hR hcell A
  refine ⟨C, hC, fun r hrR c hc f hf ↦ ⟨norm_zeroExtension f, ?_⟩⟩
  simpa only [fourierEnergy_zeroExtension_eq_fourierIntegral] using hbound r hrR c hc f hf

end JanetCartan.ContinuumNormal.FrozenImageComparison
