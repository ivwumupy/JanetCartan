module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Chart

/-!
# Transport of physical kernel operators to the auxiliary torus

For `app:ch_background:defn:bg-row` and Step 1 of
`app:ch_background:prop:bg-frame`, Euclidean boundedness and the literal
Euclidean kernel formula are inputs supplied by the PDO or kernel construction.
The measure comparison and adjoint transport are proved here. No identification
of carrier initial variables with torus variables is made.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open JanetCartan.AmplitudeBound

namespace JanetCartan.PeriodicLocalL2
variable {n : ℕ} {𝕜 F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [NormedAddCommGroup G]

section Normed
variable [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The auxiliary-torus realization of a bounded physical operator
(`app:ch_background:defn:bg-row`). -/
def transferOperator (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G) :
    PeriodicL2 n F →L[𝕜] PeriodicL2 n G :=
  toTorus ∘L A ∘L toEuclidean.toContinuousLinearMap

/-- Euclidean bounds transfer with the same constant
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_transferOperator_le (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G) :
    ‖transferOperator A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖toTorus (𝕜 := 𝕜) (A (toEuclidean (𝕜 := 𝕜) f))‖ ≤ _
  exact (norm_toTorusFun_le _).trans ((A.le_opNorm _).trans_eq (by
    rw [toEuclidean.norm_map]))

/-- On supported physical inputs, the transfer agrees with the original
operator followed by restriction (`app:ch_background:defn:bg-row`). -/
theorem transferOperator_toTorus (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G)
    (f : EuclideanL2 n F) (hf : ∀ᵐ x ∂volume, x ∉ halfOpenCell n → f x = 0) :
    transferOperator A (toTorus (𝕜 := 𝕜) f) = toTorus (𝕜 := 𝕜) (A f) := by
  change toTorus (𝕜 := 𝕜) (A (toEuclidean (𝕜 := 𝕜) (toTorus (𝕜 := 𝕜) f))) = _
  rw [toEuclidean_toTorus f hf]

/-- Compact output support gives exact output-norm equality
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem norm_transferOperator_apply (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G)
    (hA : ∀ f, ∀ᵐ x ∂volume, x ∉ halfOpenCell n → A f x = 0) (f : PeriodicL2 n F) :
    ‖transferOperator A f‖ = ‖A (toEuclidean (𝕜 := 𝕜) f)‖ :=
  norm_toTorus_of_supported (𝕜 := 𝕜) _ (hA _)

variable [NormedSpace ℝ G]

/-- Changing a cell-supported kernel integral to the torus introduces no
Jacobian or Fourier factor (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_kernel_toEuclidean
    (k : EuclideanSpace ℝ (Fin n) → F →L[𝕜] G) (f : PeriodicL2 n F) :
    (∫ y, k y (toEuclidean (𝕜 := 𝕜) f y)) =
      ∫ z : Torus n, k (centeredTorusRepresentative z) (f z) := by
  calc
    (∫ y, k y (toEuclidean (𝕜 := 𝕜) f y)) =
        ∫ y, (halfOpenCell n).indicator (fun y ↦ k y (periodicLift f y)) y := by
      apply integral_congr_ae
      filter_upwards [toEuclidean_coe (𝕜 := 𝕜) f] with y hy
      rw [hy]
      by_cases h : y ∈ halfOpenCell n <;> simp [h]
    _ = ∫ y in halfOpenCell n, k y (periodicLift f y) :=
      integral_indicator measurableSet_halfOpenCell
    _ = ∫ z : Torus n, k (centeredTorusRepresentative z) (f z) := by
      rw [← integral_representative]
      simp only [periodicLift, Function.comp_apply, torusQuotient_centeredTorusRepresentative]

/-- A literal physical kernel becomes the same kernel in the two quotient
charts. The premise is the Euclidean kernel realization, not a torus estimate
(`app:ch_background:defn:bg-row`). -/
theorem transferOperator_kernel
    (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G)
    (k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → F →L[𝕜] G)
    (hA : ∀ f, A f =ᵐ[volume] fun x ↦ ∫ y, k x y (f y)) (f : PeriodicL2 n F) :
    transferOperator A f =ᵐ[volume] fun z ↦
      ∫ w : Torus n, k (centeredTorusRepresentative z) (centeredTorusRepresentative w) (f w) := by
  filter_upwards [toTorus_coe (𝕜 := 𝕜) (A (toEuclidean (𝕜 := 𝕜) f)),
    measurePreserving_representative.quasiMeasurePreserving.ae_eq_comp
      (hA (toEuclidean (𝕜 := 𝕜) f)).restrict] with z hz hAz
  exact hz.trans (hAz.trans (integral_kernel_toEuclidean _ f))

end Normed

section Inner
variable [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G] [CompleteSpace F] [CompleteSpace G]

/-- Taking the Hilbert adjoint commutes literally with physical-to-torus
transport (`app:ch_background:defn:bg-row`). -/
theorem transferOperator_adjoint (A : EuclideanL2 n F →L[𝕜] EuclideanL2 n G) :
    (transferOperator A).adjoint = transferOperator A.adjoint := by
  simp only [transferOperator, ContinuousLinearMap.adjoint_comp, toEuclidean_adjoint,
    toTorus_adjoint, ContinuousLinearMap.comp_assoc]

end Inner
end JanetCartan.PeriodicLocalL2
