module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.CovectorBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.Output

/-!
# Full strain and geometric identification of the fixed raw auxiliary field

These are literal identities for `app:ch_background:prop:bg-mixed-physical`.
The coefficient agreement hypotheses concern the actual Christoffel and reduced
stress arrays on the physical chart, not an assumed image-normal identity.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.AuxiliaryRawBand

open ContinuumRow

variable {n N : ℕ}

/-- Full periodic strain formula, including the zeroth-order derivative of the
final cutoff (`app:ch_background:prop:bg-mixed-physical`). The array `Γ` must
agree with the actual induced Christoffel coefficients on the physical chart. -/
def periodicFullStrain (χ : Torus n → ℝ)
    (Γ : Fin n → Fin n → Fin n → Torus n → ℝ)
    (u : Torus n → Euclidean n) : Torus n → MetricTensor n :=
  fun x i j ↦ χ x * ((periodicCoordinateDeriv i u x j +
    periodicCoordinateDeriv j u x i) / 2 - ∑ k, Γ i j k x * u x k) +
    (periodicCoordinateDeriv i χ x * u x j +
      periodicCoordinateDeriv j χ x * u x i) / 2

/-- Smoothness of the actual fixed half tangent lift on its immersion domain
(`app:ch_background:eq:bg-Vaux`). -/
theorem contDiffOn_physicalField
    {G : Euclidean n → Euclidean N} {W : Set (Euclidean n)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W) (himm : IsImmersionOn G W)
    {χout : Euclidean n → ℝ} (hout : ContDiffOn ℝ ∞ χout W)
    (χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (K : ℝ) (h : OutputL2 n) :
    ContDiffOn ℝ ∞ (physicalField G χout χsrc K h) W :=
  hout.smul (AuxiliaryRealization.contDiffOn_tangentialField hW hG
    (isSmoothPeriodic_rawCovector χsrc hsrc K h).2.contDiffOn himm)

/-- The full strain of the same fixed field, with the final-cutoff error
retained (`app:ch_background:prop:bg-mixed-physical`). -/
theorem physicalStrain_apply
    {G : Euclidean n → Euclidean N} {W : Set (Euclidean n)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W) (himm : IsImmersionOn G W)
    {χout : Euclidean n → ℝ} {x : Euclidean n} (hx : x ∈ W)
    (hout : DifferentiableAt ℝ χout x)
    (χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (K : ℝ) (h : OutputL2 n) (i j : Fin n) :
    physicalStrain G χout χsrc K h x i j =
      χout x * symmCovariantDeriv G (periodicLift (rawCovector χsrc K h)) x i j +
        (partialDeriv χout x i * periodicLift (rawCovector χsrc K h) x j +
          partialDeriv χout x j * periodicLift (rawCovector χsrc K h) x i) / 2 :=
  AuxiliaryRealization.linearizedMetric_cutoff_tangentialField hW hG
    (isSmoothPeriodic_rawCovector χsrc hsrc K h).2.contDiffOn himm hx hout i j

/-- Literal Euclidean/torus full-strain agreement under pointwise agreement
of the primitive Christoffel coefficients. No change of input measure is made
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem physicalStrain_eq_periodicFullStrain
    {G : Euclidean n → Euclidean N} {W : Set (Euclidean n)}
    (hW : IsOpen W) (hG : ContDiffOn ℝ ∞ G W) (himm : IsImmersionOn G W)
    (χout : Torus n → ℝ) (hout : IsSmoothPeriodic χout)
    (Γ : Fin n → Fin n → Fin n → Torus n → ℝ)
    (hΓ : ∀ x ∈ W, ∀ i j k, Γ i j k (torusQuotient x) = christoffel G x i j k)
    (χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (K : ℝ) (h : OutputL2 n) :
    EqOn (physicalStrain G (periodicLift χout) χsrc K h)
      (periodicLift (periodicFullStrain χout Γ (rawCovector χsrc K h))) W := by
  intro x hx
  have hu := isSmoothPeriodic_rawCovector χsrc hsrc K h
  have hd (i j : Fin n) :
      periodicCoordinateDeriv i (rawCovector χsrc K h) (torusQuotient x) j =
        partialDeriv (fun y ↦ periodicLift (rawCovector χsrc K h) y j) x i := by
    have he := congrFun (periodicLift_coordinateDeriv
      (hu.comp_clm (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) j)).2 i) x
    rw [periodicCoordinateDeriv_comp_clm hu] at he
    exact he
  have hc (i : Fin n) : periodicCoordinateDeriv i χout (torusQuotient x) =
      partialDeriv (periodicLift χout) x i :=
    congrFun (periodicLift_coordinateDeriv hout.2 i) x
  ext i j
  rw [physicalStrain_apply hW hG himm hx
    (hout.2.differentiable (by simp)).differentiableAt χsrc hsrc]
  simp only [periodicLift, Function.comp_apply, periodicFullStrain, symmCovariantDeriv,
    hd, hc, hΓ x hx]

/-- The fixed smooth covector gives the very H¹ element used by the image
channel (`app:ch_background:eq:bg-Vaux`). -/
theorem ofSmooth_rawCovector_one (χsrc : C(Torus n, ℝ))
    (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) :
    PeriodicSobolevSpace.ofSmooth 1 (rawCovector χsrc K h)
      (isSmoothPeriodic_rawCovector χsrc hsrc K h) = rawCovectorH1 χsrc K h := by
  apply PeriodicSobolevSpace.toL2_injective 1
  rw [toL2_ofSmooth_rawCovector χsrc hsrc, toL2_rawCovectorH1]

/-- One fixed smooth representative of the original image output, including
its measurement cutoff (`app:ch_background:defn:bg-mixed`). -/
def smoothImageOutput
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) : Torus n → Euclidean n :=
  fun x ↦ χmeas x • reducedPeriodicFormula c (rawCovector χsrc K h) x

/-- The complete representative includes the original exterior component
(`app:ch_background:eq:bg-Vaux-raw-band`). -/
def smoothAuxiliaryOutput
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) (K : ℝ) (him hout : OutputL2 n) :
    Torus n → Euclidean n :=
  smoothImageOutput c χmeas χsrc K him + rawSource (1 - ψ) K hout

/-- The image representative realizes the original image channel in L²
(`app:ch_background:defn:bg-mixed`). -/
theorem imageOutput_coeFn
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (K : ℝ) (h : OutputL2 n) :
    imageOutput c χmeas χsrc K h =ᵐ[volume] smoothImageOutput c χmeas χsrc K h := by
  have hr := reducedWeakOperator_ofSmooth_ae c (rawCovector χsrc K h)
    (isSmoothPeriodic_rawCovector χsrc hsrc K h)
  rw [ofSmooth_rawCovector_one χsrc hsrc] at hr
  filter_upwards [cutoffMultiplier_coeFn χmeas
    (reducedWeakOperator c (rawCovectorH1 χsrc K h)), hr] with x hx hy
  exact hx.trans (congrArg (fun v ↦ χmeas x • v) hy)

/-- Both output components have their literal representatives, without any
regularity assumption on either raw datum (`app:ch_background:eq:bg-Vaux`). -/
theorem auxiliaryOutput_coeFn
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (K : ℝ) (him hout : OutputL2 n) :
    auxiliaryOutput c χmeas χsrc ψ K him hout =ᵐ[volume]
      smoothAuxiliaryOutput c χmeas χsrc ψ K him hout :=
  (Lp.coeFn_add _ _).trans
    ((imageOutput_coeFn c χmeas χsrc hsrc K him).add (exteriorOutput_coeFn ψ K hout))

/-- On the physical core the smooth complete output is the reduced stress
pairing of the actual full strain of the fixed field. Inputs are only the
primitive geometric coefficient agreement and cutoff plateaus
(`app:ch_background:prop:bg-mixed-physical`). -/
theorem smoothAuxiliaryOutput_eq_reduced_physicalStrain_on_core
    {G : Euclidean n → Euclidean N} {W core : Set (Euclidean n)}
    (hW : IsOpen W) (hcore : IsOpen core) (hsub : core ⊆ W)
    (hG : ContDiffOn ℝ ∞ G W) (himm : IsImmersionOn G W)
    {χout : Euclidean n → ℝ} (hout : EqOn χout (fun _ ↦ 1) core)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ x ∈ core, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients G x j)
    (χmeas χsrc ψ : C(Torus n, ℝ)) (hsrc : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hm : ∀ x ∈ core, χmeas (torusQuotient x) = 1)
    (hψ : ∀ x ∈ core, ψ (torusQuotient x) = 1)
    (K : ℝ) (him houtData : OutputL2 n) {x : Euclidean n} (hx : x ∈ core) (i : Fin n) :
    smoothAuxiliaryOutput c χmeas χsrc ψ K him houtData (torusQuotient x) i =
      tensorPairing (StressFrame.geometricCubeStress G x i).val
        (physicalStrain G χout χsrc K him x) := by
  have hs := AuxiliaryRealization.linearizedMetric_cutoff_tangentialField_on_core
    hW hcore hsub hG (isSmoothPeriodic_rawCovector χsrc hsrc K him).2.contDiffOn
    himm hout hx
  have hr := reducedPeriodicFormula_eq_geometric G c (rawCovector χsrc K him)
    (isSmoothPeriodic_rawCovector χsrc hsrc K him) x (hc x hx)
  change _ = tensorPairing _ (linearizedMetric G
    (fun y ↦ χout y • AuxiliaryRealization.tangentialField G
      (periodicLift (rawCovector χsrc K him)) y) x)
  rw [hs]
  simp only [smoothAuxiliaryOutput, Pi.add_apply, smoothImageOutput, rawSource,
    ContinuousMap.coe_sub, ContinuousMap.coe_one, Pi.sub_apply, Pi.one_apply,
    hm x hx, hψ x hx, sub_self, zero_smul, one_smul, add_zero]
  exact congrFun hr i

end JanetCartan.AuxiliaryRawBand
