module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.SmoothFamilyNorms.Sobolev
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Increment

/-!
# The measured Hermitian tensor in real periodic L²

The concrete bilinear map needed by `MeanRecurrence.finite_mean_bounds` in
`main:lem:mean-recurrence`. Its coefficient is the actual measurement field.
The representative is preserved, and the mixed seminorm estimate is proved
from the published zero-order product bound.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean.SmoothPeriodicFamily

variable {d : ℕ} {ι m n G : Type*} [Fintype ι] [Fintype m] [Fintype n]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `main:eq:full-recursion`: the actual Hermitian bilinear tensor as a
singleton smooth family, retaining pointwise values before measurement. -/
def tensorBilinear (μ : ι → ℝ) :
    SmoothPeriodicFamily d ι (Matrix m n ℂ) →ₗ[ℝ]
      SmoothPeriodicFamily d ι (Matrix m n ℂ) →ₗ[ℝ]
        SmoothPeriodicFamily d Unit (Matrix n n ℝ) :=
  LinearMap.mk₂ ℝ
    (fun D E ↦ ⟨fun x _ ↦ weightedHermitianBilinear μ D.val E.val x, fun _ ↦ by
      simpa only [hermitianContinuousBilinear_apply, weightedHermitianBilinear,
        hermitianBilinear, LinearMap.mk₂_apply] using
        isSmoothPeriodic_weightedBilinear hermitianContinuousBilinear D.val E.val μ
          D.property E.property⟩)
    (fun D E F ↦ by
      apply Subtype.ext
      funext x u
      exact congrFun (congrArg (fun L ↦ L F.val)
        ((weightedHermitianBilinear μ).map_add D.val E.val)) x)
    (fun c D E ↦ by
      apply Subtype.ext
      funext x u
      exact congrFun (congrArg (fun L ↦ L E.val)
        ((weightedHermitianBilinear μ).map_smul c D.val)) x)
    (fun D E F ↦ by
      apply Subtype.ext
      funext x u
      exact congrFun ((weightedHermitianBilinear μ D.val).map_add E.val F.val) x)
    (fun c D E ↦ by
      apply Subtype.ext
      funext x u
      exact congrFun ((weightedHermitianBilinear μ D.val).map_smul c E.val) x)

/-- `main:eq:mean-equation`: the diagonal is the complete weighted Hermitian tensor. -/
theorem tensorBilinear_self (μ : ι → ℝ)
    (D : SmoothPeriodicFamily d ι (Matrix m n ℂ)) (x : Torus d) :
    (tensorBilinear μ D D).val x () = weightedHermitianTensor μ D.val x :=
  congrFun (weightedHermitianBilinear_self μ D.val) x

/-- `main:eq:full-recursion`: apply the actual smooth measurement coefficient
pointwise, preserving the smooth output before passing to L². -/
def measurementFamily (C : Torus d → Matrix n n ℝ →L[ℝ] G) (hC : IsSmoothPeriodic C) :
    SmoothPeriodicFamily d Unit (Matrix n n ℝ) →ₗ[ℝ] SmoothPeriodicFamily d Unit G where
  toFun T := ⟨fun x _ ↦ C x (T.val x ()), fun _ ↦
    ⟨hC.1.clm_apply (smooth T ()).1, hC.2.clm_apply (smooth T ()).2⟩⟩
  map_add' T U := by
    apply Subtype.ext
    funext x u
    exact (C x).map_add _ _
  map_smul' c T := by
    apply Subtype.ext
    funext x u
    exact (C x).map_smul c _

/-- `main:eq:full-recursion`: the measurement map into real periodic L².
The original coefficient field is an argument, not an abstract replacement. -/
def measurementL2 (C : Torus d → Matrix n n ℝ →L[ℝ] G) (hC : IsSmoothPeriodic C) :
    SmoothPeriodicFamily d Unit (Matrix n n ℝ) →ₗ[ℝ] PeriodicL2 d G :=
  (componentL2 ()).comp (measurementFamily C hC)

/-- `main:eq:full-recursion`: the actual measured bilinear map in the
precise algebraic type consumed by the abstract recurrence. -/
def measuredHermitianBilinear (μ : ι → ℝ)
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) (hC : IsSmoothPeriodic C) :
    SmoothPeriodicFamily d ι (Matrix m n ℂ) →ₗ[ℝ]
      SmoothPeriodicFamily d ι (Matrix m n ℂ) →ₗ[ℝ] PeriodicL2 d G :=
  (tensorBilinear μ).compr₂ (measurementL2 C hC)

/-- `main:eq:full-recursion`: the L² bilinear map has exactly the actual
pointwise measured Hermitian representative. -/
theorem measuredHermitianBilinear_coe_ae (μ : ι → ℝ)
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) (hC : IsSmoothPeriodic C)
    (D E : SmoothPeriodicFamily d ι (Matrix m n ℂ)) :
    measuredHermitianBilinear μ C hC D E =ᵐ[volume]
      (fun x ↦ C x (weightedHermitianBilinear μ D.val E.val x)) :=
  componentL2_coe_ae () (measurementFamily C hC (tensorBilinear μ D E))

/-- `main:eq:mean-equation`: the diagonal retains the complete measured self tensor. -/
theorem measuredHermitianBilinear_self_coe_ae (μ : ι → ℝ)
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) (hC : IsSmoothPeriodic C)
    (D : SmoothPeriodicFamily d ι (Matrix m n ℂ)) :
    measuredHermitianBilinear μ C hC D D =ᵐ[volume]
      (fun x ↦ C x (weightedHermitianTensor μ D.val x)) := by
  simpa only [weightedHermitianBilinear_self] using
    measuredHermitianBilinear_coe_ae μ C hC D D

/-- `main:lem:mean-recurrence`: realization in L² preserves the literal
periodic integral norm. -/
theorem norm_measuredHermitianBilinear_eq (μ : ι → ℝ)
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) (hC : IsSmoothPeriodic C)
    (D E : SmoothPeriodicFamily d ι (Matrix m n ℂ)) :
    ‖measuredHermitianBilinear μ C hC D E‖ =
      periodicL2Norm (fun x ↦ C x (weightedHermitianBilinear μ D.val E.val x)) :=
  norm_componentL2 () (measurementFamily C hC (tensorBilinear μ D E))

/-- `main:lem:mean-recurrence`: the mixed seminorm bound required by
`MeanRecurrence.finite_mean_bounds`, with no sample-count factor. -/
theorem norm_measuredHermitianBilinear_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) (hC : IsSmoothPeriodic C)
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ x, ‖C x‖ ≤ c)
    (D E : SmoothPeriodicFamily d ι (Matrix m n ℂ)) :
    ‖measuredHermitianBilinear μ C hC D E‖ ≤
      c * cSeminorm μ hμ 0 D * l2Seminorm μ hμ E := by
  rw [norm_measuredHermitianBilinear_eq, cSeminorm_eq, l2Seminorm_eq]
  exact periodicL2Norm_contracted_weightedHermitianBilinear_le μ hμ D.val E.val
    D.property (fun i ↦ (smooth E i).1) C hc hbound

/-- `main:lem:mean-recurrence`: compact smoothness supplies a concrete
measurement bound, so this bilinear estimate has no assumed analytic inequality. -/
theorem norm_measuredHermitianBilinear_le_cNorm (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (C : Torus d → Matrix n n ℝ →L[ℝ] G) (hC : IsSmoothPeriodic C)
    (D E : SmoothPeriodicFamily d ι (Matrix m n ℂ)) :
    ‖measuredHermitianBilinear μ C hC D E‖ ≤
      cNorm (fundamentalCell d) 0 (periodicLift C) * cSeminorm μ hμ 0 D *
        l2Seminorm μ hμ E :=
  norm_measuredHermitianBilinear_le μ hμ C hC (cNorm_nonneg _ _ _)
    hC.norm_le_cNorm_zero D E

end JanetCartan.CurrentMean.SmoothPeriodicFamily
