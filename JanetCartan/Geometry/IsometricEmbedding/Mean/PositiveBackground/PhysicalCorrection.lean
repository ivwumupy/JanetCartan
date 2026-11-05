module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Synthesis
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.CovectorRaising
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAuxiliary

/-!
# The physical correction from the uncorrected row

For `app:ch_background:eq:bg-current-raising`, use the original image slot,
source multiplier and Bessel inverse to construct the smooth covector. The
positive background uses the FULL tangent lift, twice the preparation lift.
Its reduced strain is twice the original image channel on the measurement
plateau. The same-row all-order adjoint membership is still an input of the
continuum inverse producer; no physical strain identity is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PositiveBackground
open ContinuumRow CurrentMean

variable {n N : ℕ}

/-- The smooth measured image output with the original uncut Bessel covector
(`app:ch_background:eq:bg-current-raising`). -/
def uncutImageRepresentative
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (him : OutputL2 n) : Torus n → Euclidean n :=
  fun x ↦ χmeas x • reducedPeriodicFormula c (preparationCovector χsrc him) x

/-- The smooth image representative is the SAME bounded image channel
(`app:ch_background:eq:bg-current-identity`). -/
theorem uncutImageRepresentative_ae
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (him : OutputL2 n)
    (hmem : ∀ s, him ∈ periodicSobolevLevel n (Euclidean n) s) :
    imageChannel c χmeas χsrc him =ᵐ[volume] uncutImageRepresentative c χmeas χsrc him := by
  have hi := reducedWeakOperator_ofSmooth_ae c (preparationCovector χsrc him)
    (isSmoothPeriodic_preparationCovector χsrc hs him hmem)
  rw [ofSmooth_preparationCovector χsrc hs him hmem] at hi
  filter_upwards [imageChannel_coeFn c χmeas χsrc him, hi] with x hx hi
  exact hx.trans (by rw [hi]; rfl)

/-- Smoothness of that exact image representative
(`app:ch_background:prop:bg-positive`). -/
theorem isSmoothPeriodic_uncutImageRepresentative
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (him : OutputL2 n)
    (hmem : ∀ s, him ∈ periodicSobolevLevel n (Euclidean n) s) :
    IsSmoothPeriodic (uncutImageRepresentative c χmeas χsrc him) := by
  have hi := AuxiliaryRawBand.isSmoothPeriodic_reducedPeriodicFormula c hc _
    (isSmoothPeriodic_preparationCovector χsrc hs him hmem)
  exact ⟨hm.1.smul hi.1, hm.2.smul hi.2⟩

section OriginalInverse

variable {ι : Type*} [Fintype ι]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ θ : C(Torus n, ℝ))
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (residual : OutputL2 n)

/-- The actual physical base from the uncorrected inverse. This is not a
new inverse or the later corrected-positive `Q₀`
(`app:ch_background:eq:bg-current-raising`). -/
def uncorrectedBaseVariation (G : Euclidean n → Euclidean N)
    (X₀ : Euclidean n → Euclidean n) : Euclidean n → Euclidean N :=
  baseVariation G X₀ (periodicLift (preparationCovector χsrc
    (uncorrectedRawCorrection (imageChannel c χmeas χsrc) U ψ θ residual).fst.fst))

/-- The sign is positive and the background lift is twice the uncut
preparation lift (`app:ch_background:eq:bg-current-raising`). -/
theorem uncorrectedBaseVariation_eq (G : Euclidean n → Euclidean N)
    (X₀ : Euclidean n → Euclidean n) :
    uncorrectedBaseVariation c χmeas χsrc ψ θ U residual G X₀ =
      tangentVariation G X₀ + (2 : ℝ) •
        preparationAuxiliaryField χsrc
          (uncorrectedRawCorrection (imageChannel c χmeas χsrc) U ψ θ residual).fst.fst
          G (fun _ ↦ 1) := by
  rw [uncorrectedBaseVariation, baseVariation_eq]
  congr 1
  funext x
  simp [preparationAuxiliaryField, AuxiliaryRealization.tangentialField, smul_smul]

variable (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hreg : ∀ s, uncorrectedRawCorrection (imageChannel c χmeas χsrc) U ψ θ residual ∈
      CarrierSobolev.augmentedInputLevel n ι s)

include hreg in
private theorem original_image_mem (s : ℕ) :
    (uncorrectedRawCorrection (imageChannel c χmeas χsrc) U ψ θ residual).fst.fst ∈
      periodicSobolevLevel n (Euclidean n) s :=
  ((CarrierSobolev.mem_augmentedInputLevel_iff s
    (uncorrectedRawCorrection (imageChannel c χmeas χsrc) U ψ θ residual)).mp (hreg s)).1

include hs hreg in
/-- Smoothness of the actual base variation, using the all-order membership
of its own original adjoint output (`app:ch_background:prop:bg-positive`). -/
theorem contDiffOn_uncorrectedBaseVariation
    {G : Euclidean n → Euclidean N} {X₀ : Euclidean n → Euclidean n}
    {W : Set (Euclidean n)} (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hX₀ : ContDiffOn ℝ ∞ X₀ W) (himm : IsImmersionOn G W) :
    ContDiffOn ℝ ∞ (uncorrectedBaseVariation c χmeas χsrc ψ θ U residual G X₀) W :=
  contDiffOn_baseVariation hW hG hX₀
    (isSmoothPeriodic_preparationCovector χsrc hs _
      (original_image_mem c χmeas χsrc ψ θ U residual hreg)).2.contDiffOn himm

include hs hreg in
/-- The actual reduced physical strain equals the reference strain plus
twice the smooth image output, on the measurement plateau. No exterior
output is equated with physical strain (`app:ch_background:eq:bg-current-identity`). -/
theorem uncorrectedBaseVariation_reduced_strain
    {G : Euclidean n → Euclidean N} {X₀ : Euclidean n → Euclidean n}
    {W : Set (Euclidean n)} (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W)
    (hX₀ : ContDiffOn ℝ ∞ X₀ W) (himm : IsImmersionOn G W)
    {x : Euclidean n} (hx : x ∈ W)
    (hcoeff : ∀ j, c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients G x j)
    (hmeas : χmeas (torusQuotient x) = 1) (i : Fin n) :
    tensorPairing (StressFrame.geometricCubeStress G x i).val
      (linearizedMetric G (uncorrectedBaseVariation c χmeas χsrc ψ θ U residual G X₀) x) =
      tensorPairing (StressFrame.geometricCubeStress G x i).val
        (linearizedMetric G (tangentVariation G X₀) x) +
      2 * uncutImageRepresentative c χmeas χsrc
        (uncorrectedRawCorrection (imageChannel c χmeas χsrc) U ψ θ residual).fst.fst
          (torusQuotient x) i := by
  have hu := isSmoothPeriodic_preparationCovector χsrc hs _
    (original_image_mem c χmeas χsrc ψ θ U residual hreg)
  have hstrain := linearizedMetric_baseVariation hW hG hX₀ hu.2.contDiffOn himm hx
  have hr := congrFun (reducedPeriodicFormula_eq_geometric G c _ hu x hcoeff) i
  change tensorPairing _ (linearizedMetric G (baseVariation G X₀ (periodicLift
    (preparationCovector χsrc
      (uncorrectedRawCorrection (imageChannel c χmeas χsrc) U ψ θ residual).fst.fst))) x) = _
  rw [hstrain]
  simp only [uncutImageRepresentative, hmeas, one_smul, hr]
  simp only [NullTransport.reducedOperator, two_smul, Pi.add_apply, Matrix.add_apply, tensorPairing,
    mul_add, Finset.sum_add_distrib]
  ring

end OriginalInverse
end JanetCartan.PositiveBackground
