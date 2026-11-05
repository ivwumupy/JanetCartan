module

public import JanetCartan.Iteration.PhysicalBackground.Source

/-!
# The v2 physical base field from the current image slot

The v2 base uses ONE image realization, `dF X₀ + J_F h_im`, not the old
factor-two lift. The image representative, source multiplier, Bessel inverse,
and current immersion are retained. Its reduced strain identity is proved
geometrically, before the density-row cancellation is applied.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev CurrentMean PositiveBackground

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The literal v2 field `Vbase=dF X₀+J_F h_image`. The original uncut Bessel
image lift is used with its factor one-half covector raising, exactly once. -/
def baseVariation (χsrc : C(Torus n, ℝ)) (raw : AugmentedInput n ι)
    (F : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n) :
    Euclidean n → Euclidean N :=
  tangentVariation F X₀ + AuxiliaryRealization.tangentialField F
    (periodicLift (preparationCovector χsrc raw.fst.fst))

/-- The base has precisely the existing image-field realization, without an
initial-variable cutoff or an extra factor two. -/
theorem baseVariation_eq (χsrc : C(Torus n, ℝ)) (raw : AugmentedInput n ι)
    (F : Euclidean n → Euclidean N) (X₀ : Euclidean n → Euclidean n) :
    baseVariation χsrc raw F X₀ = tangentVariation F X₀ +
      preparationAuxiliaryField χsrc raw.fst.fst F (fun _ ↦ 1) := by
  funext x
  simp only [baseVariation, Pi.add_apply, preparationAuxiliaryField, one_smul]

/-- All-order raw membership from the uncorrected CURRENT inverse proves
smoothness of the actual base field on the immersion domain. -/
theorem contDiffOn_baseVariation (χsrc : C(Torus n, ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (raw : AugmentedInput n ι) (hraw : ∀ s, raw ∈ augmentedInputLevel n ι s)
    {F : Euclidean n → Euclidean N} {X₀ : Euclidean n → Euclidean n}
    {W : Set (Euclidean n)} (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    (hX₀ : ContDiffOn ℝ ∞ X₀ W) (himm : IsImmersionOn F W) :
    ContDiffOn ℝ ∞ (baseVariation χsrc raw F X₀) W := by
  have him (s : ℕ) : raw.fst.fst ∈ periodicSobolevLevel n (Euclidean n) s :=
    ((mem_augmentedInputLevel_iff s raw).mp (hraw s)).1
  exact (contDiffOn_tangentVariation hW hF hX₀).add
    (AuxiliaryRealization.contDiffOn_tangentialField hW hF
      (isSmoothPeriodic_preparationCovector χsrc hs raw.fst.fst him).2.contDiffOn himm)

/-- The complete reduced strain is the original tangent strain plus ONE image
output, on the measurement plateau (`app:ch_background:eq:bg-current-identity`).
The exterior slot is not interpreted as a physical field. -/
theorem baseVariation_reduced_strain
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (raw : AugmentedInput n ι) (hraw : ∀ s, raw ∈ augmentedInputLevel n ι s)
    {F : Euclidean n → Euclidean N} {X₀ : Euclidean n → Euclidean n}
    {W : Set (Euclidean n)} (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W)
    (hX₀ : ContDiffOn ℝ ∞ X₀ W) (himm : IsImmersionOn F W)
    {x : Euclidean n} (hx : x ∈ W)
    (hcoeff : ∀ j, c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j)
    (hmeas : χmeas (torusQuotient x) = 1) (i : Fin n) :
    tensorPairing (StressFrame.geometricCubeStress F x i).val
      (linearizedMetric F (baseVariation χsrc raw F X₀) x) =
      tensorPairing (StressFrame.geometricCubeStress F x i).val
        (linearizedMetric F (tangentVariation F X₀) x) +
      uncutImageRepresentative c χmeas χsrc raw.fst.fst (torusQuotient x) i := by
  have him (s : ℕ) : raw.fst.fst ∈ periodicSobolevLevel n (Euclidean n) s :=
    ((mem_augmentedInputLevel_iff s raw).mp (hraw s)).1
  have hu := isSmoothPeriodic_preparationCovector χsrc hs raw.fst.fst him
  have ht := contDiffOn_tangentVariation hW hF hX₀
  have hj := AuxiliaryRealization.contDiffOn_tangentialField hW hF hu.2.contDiffOn himm
  have hsum := linearizedMetric_add_apply
    ((ht.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp))
    ((hj.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)) (F := F)
  have hstrain := AuxiliaryRealization.linearizedMetric_tangentialField hW hF hu.2.contDiffOn himm hx
  have hr := congrFun (reducedPeriodicFormula_eq_geometric F c _ hu x hcoeff) i
  rw [baseVariation, hsum, hstrain]
  simp only [uncutImageRepresentative, hmeas, one_smul, hr, NullTransport.reducedOperator,
    tensorPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

end JanetCartan.PhysicalBackground
