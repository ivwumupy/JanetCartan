module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PeriodicRepresentative
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Preparation
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.Multipliers.Extension

/-!
# The actual uncut auxiliary preparation update

For `app:ch_mean_pairs:eq:mean-density-recursion`, construct the covector
`J (χ_src h_im)` and its half tangent lift, without a Fourier cutoff. The
complete smooth output retains the exterior component and represents the
original auxiliary normal. Full raw regularity is required only on smooth
sources and for the same fixed `Q₀` used by the density update.

The analytic inverse/adjoint producers still owe that regularity for the
corrected-positive row. No estimate or successful preparation is assumed
as a field of a new interface here.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean

open ContinuumRow PeriodicSobolevSpace
open ContinuumCommutator.ImageChannel.Differential

variable {n N : ℕ}

section RawData

variable (χsrc : C(Torus n, ℝ)) (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (him : OutputL2 n) (himem : ∀ s, him ∈ periodicSobolevLevel n (Euclidean n) s)

include hs himem
/-- The original source multiplier and Bessel inverse give every Sobolev
order of the uncut covector. This follows from their already constructed
Sobolev actions (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationCovector_mem (s : ℕ) :
    periodicBesselInverse (cutoffMultiplier χsrc him) ∈
      periodicSobolevLevel n (Euclidean n) s := by
  have hm := toL2_mem s (cutoffSobolev χsrc hs s (ofL2 s him (himem s)))
  rw [toL2_cutoffSobolev, toL2_ofL2] at hm
  exact antitone_periodicSobolevLevel (Nat.le_succ s)
    (periodicBesselInverse_mem_succ s (ofL2 s _ hm))

/-- The single uncut source/Bessel covector, fixed before derivative orders
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationCovector : Torus n → Euclidean n :=
  preparationFourierRepresentative (periodicBesselInverse (cutoffMultiplier χsrc him))

/-- Smoothness of the SAME uncut covector
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem isSmoothPeriodic_preparationCovector :
    IsSmoothPeriodic (preparationCovector χsrc him) :=
  isSmoothPeriodic_preparationFourierRepresentative _
    (preparationCovector_mem χsrc hs him himem)

/-- The literal smooth covector represents the original Bessel action in
L², with the source multiplier in its original order
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationCovector_ae :
    periodicBesselInverse (cutoffMultiplier χsrc him) =ᵐ[volume]
      preparationCovector χsrc him :=
  preparationFourierRepresentative_ae _ (preparationCovector_mem χsrc hs him himem)

/-- The constructed covector is precisely the H¹ lift used by the image
channel, rather than a separately chosen weak solution
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem ofSmooth_preparationCovector :
    ofSmooth 1 (preparationCovector χsrc him)
      (isSmoothPeriodic_preparationCovector χsrc hs him himem) =
        periodicBesselLift (cutoffMultiplier χsrc him) := by
  apply toL2_injective 1
  rw [toL2_periodicBesselLift]
  apply Lp.ext
  exact (toL2_ofSmooth_ae 1 _ _).trans (preparationCovector_ae χsrc hs him himem).symm

end RawData

section CompleteOutput

variable (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (him hout : OutputL2 n)
    (himem : ∀ s, him ∈ periodicSobolevLevel n (Euclidean n) s)
    (homem : ∀ s, hout ∈ periodicSobolevLevel n (Euclidean n) s)

/-- The complete uncut smooth output, retaining the exterior summand
globally (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def uncutAuxiliaryRepresentative : SmoothResidual n :=
  ⟨fun x _ ↦ χmeas x • reducedPeriodicFormula c (preparationCovector χsrc him) x +
      (1 - ψ x) • preparationFourierRepresentative hout x,
    fun _ ↦ by
      have hi := AuxiliaryRawBand.isSmoothPeriodic_reducedPeriodicFormula c hc _
        (isSmoothPeriodic_preparationCovector χsrc hs him himem)
      have ho := isSmoothPeriodic_preparationFourierRepresentative hout homem
      exact ⟨(hm.1.smul hi.1).add ((continuous_const.sub hψ.1).smul ho.1),
        (hm.2.smul hi.2).add ((contDiff_const.sub hψ.2).smul ho.2)⟩⟩

/-- Exact original L² action of the complete uncut representative. The
exterior-augmented output is never identified globally with physical strain
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem uncutAuxiliaryRepresentative_toL2 :
    smoothResidualToL2 n
      (uncutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ him hout himem homem) =
        imageChannel c χmeas χsrc him + exteriorChannel ψ hout := by
  have hi := reducedWeakOperator_ofSmooth_ae c (preparationCovector χsrc him)
    (isSmoothPeriodic_preparationCovector χsrc hs him himem)
  rw [ofSmooth_preparationCovector χsrc hs him himem] at hi
  simp only [smoothResidualToL2]
  apply Lp.ext
  filter_upwards [SmoothPeriodicFamily.componentL2_coe_ae ()
      (uncutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ him hout himem homem),
    Lp.coeFn_add (imageChannel c χmeas χsrc him) (exteriorChannel ψ hout),
    imageChannel_coeFn c χmeas χsrc him, hi,
    cutoffMultiplier_coeFn (1 - ψ) hout,
    preparationFourierRepresentative_ae hout homem] with x hr ha hm' hi' ho he
  rw [hr, ha]
  change _ = imageChannel c χmeas χsrc him x + cutoffMultiplier (1 - ψ) hout x
  rw [hm', hi', ho, he]
  rfl

/-- The actual physical field, with the fixed final cutoff and literal
one-half tangent lift (`app:ch_mean_pairs:eq:mean-density-recursion`). The
preparation subtracts this field at each update. -/
def preparationAuxiliaryField (F : Euclidean n → Euclidean N)
    (χout : Euclidean n → ℝ) : Euclidean n → Euclidean N :=
  fun x ↦ χout x • AuxiliaryRealization.tangentialField F
    (periodicLift (preparationCovector χsrc him)) x

/-- The actual physical update is supported in its original final cutoff;
the uncut initial datum is not altered to obtain this support
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem support_preparationAuxiliaryField_subset (F : Euclidean n → Euclidean N)
    (χout : Euclidean n → ℝ) :
    Function.support (preparationAuxiliaryField χsrc him F χout) ⊆ Function.support χout := by
  intro x hx
  contrapose! hx
  simp_all only [Function.mem_support, not_not]
  simp [preparationAuxiliaryField, hx]

/-- A compact final physical cutoff makes the SAME uncut update compactly
supported (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem hasCompactSupport_preparationAuxiliaryField (F : Euclidean n → Euclidean N)
    {χout : Euclidean n → ℝ} (hout : HasCompactSupport χout) :
    HasCompactSupport (preparationAuxiliaryField χsrc him F χout) :=
  hout.of_isClosed_subset (isClosed_tsupport _)
    (closure_mono (support_preparationAuxiliaryField_subset χsrc him F χout))

include hs himem

/-- Smoothness of the actual uncut physical update on the immersion domain
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem contDiffOn_preparationAuxiliaryField
    {F : Euclidean n → Euclidean N} {W : Set (Euclidean n)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W) (himm : IsImmersionOn F W)
    {χout : Euclidean n → ℝ} (hout : ContDiffOn ℝ ∞ χout W) :
    ContDiffOn ℝ ∞ (preparationAuxiliaryField χsrc him F χout) W :=
  hout.smul (AuxiliaryRealization.contDiffOn_tangentialField hW hF
    (isSmoothPeriodic_preparationCovector χsrc hs him himem).2.contDiffOn himm)

/-- The full physical strain retains the final-cutoff derivative term
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem linearizedMetric_preparationAuxiliaryField
    {F : Euclidean n → Euclidean N} {W : Set (Euclidean n)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W) (himm : IsImmersionOn F W)
    {χout : Euclidean n → ℝ} {x : Euclidean n} (hx : x ∈ W)
    (hout : DifferentiableAt ℝ χout x) (i j : Fin n) :
    linearizedMetric F (preparationAuxiliaryField χsrc him F χout) x i j =
      χout x * symmCovariantDeriv F (periodicLift (preparationCovector χsrc him)) x i j +
        (partialDeriv χout x i * preparationCovector χsrc him (torusQuotient x) j +
          partialDeriv χout x j * preparationCovector χsrc him (torusQuotient x) i) / 2 :=
  AuxiliaryRealization.linearizedMetric_cutoff_tangentialField hW hF
    (isSmoothPeriodic_preparationCovector χsrc hs him himem).2.contDiffOn himm hx hout i j

/-- Only on the common open plateau is the complete uncut output the
measured physical strain. Exterior output vanishes there exactly
(`app:ch_mean_pairs:eq:mean-prepared-residual`). -/
theorem uncutAuxiliaryRepresentative_eq_strain_on_core
    {F : Euclidean n → Euclidean N} {W core : Set (Euclidean n)}
    (hW : IsOpen W) (hcore : IsOpen core) (hsub : core ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) (himm : IsImmersionOn F W)
    {χout : Euclidean n → ℝ} (hplateau : EqOn χout (fun _ ↦ 1) core)
    (hcoeff : ∀ x ∈ core, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j)
    (hmeas : ∀ x ∈ core, χmeas (torusQuotient x) = 1)
    (hext : ∀ x ∈ core, ψ (torusQuotient x) = 1)
    {x : Euclidean n} (hx : x ∈ core) (i : Fin n) :
    (uncutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ him hout himem homem).val
      (torusQuotient x) () i =
      tensorPairing (StressFrame.geometricCubeStress F x i).val
        (linearizedMetric F (preparationAuxiliaryField χsrc him F χout) x) := by
  have hstrain := AuxiliaryRealization.linearizedMetric_cutoff_tangentialField_on_core
    hW hcore hsub hF
    (isSmoothPeriodic_preparationCovector χsrc hs him himem).2.contDiffOn himm hplateau hx
  have hr := reducedPeriodicFormula_eq_geometric F c (preparationCovector χsrc him)
    (isSmoothPeriodic_preparationCovector χsrc hs him himem) x (hcoeff x hx)
  change _ = tensorPairing _ (linearizedMetric F
    (fun y ↦ χout y • AuxiliaryRealization.tangentialField F
      (periodicLift (preparationCovector χsrc him)) y) x)
  rw [hstrain]
  simp only [uncutAuxiliaryRepresentative, hmeas x hx, hext x hx, sub_self,
    zero_smul, one_smul, add_zero]
  exact congrFun hr i

end CompleteOutput

section FixedRow

variable {ι : Type*} [Fintype ι]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (hreg : ∀ (e : SmoothResidual n) (s : ℕ),
      (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
        (Q₀ (smoothResidualToL2 n e)) ∈ CarrierSobolev.augmentedInputLevel n ι s)

include hreg in
private theorem preparation_image_mem (e : SmoothResidual n) (s : ℕ) :
    (imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) s := by
  rw [← AuxiliaryRawBand.augmentedAdjoint_image (imageChannel c χmeas χsrc) U ψ]
  exact ((CarrierSobolev.mem_augmentedInputLevel_iff s _).mp (hreg e s)).1

include hreg in
private theorem preparation_exterior_mem (e : SmoothResidual n) (s : ℕ) :
    exteriorChannel ψ (Q₀ (smoothResidualToL2 n e)) ∈
      periodicSobolevLevel n (Euclidean n) s := by
  rw [← AuxiliaryRawBand.augmentedAdjoint_exterior (imageChannel c χmeas χsrc) U ψ]
  exact ((CarrierSobolev.mem_augmentedInputLevel_iff s _).mp (hreg e s)).2.2

/-- Restrict the SAME original adjoint and corrected-positive `Q₀` to
smooth sources. Both auxiliary slots are kept, with no raw Fourier cut
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationAuxiliaryRepresentative (e : SmoothResidual n) : SmoothResidual n :=
  uncutAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ
    ((imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n e)))
    (exteriorChannel ψ (Q₀ (smoothResidualToL2 n e)))
    (by exact preparation_image_mem c χmeas χsrc ψ U Q₀ hreg e)
    (by exact preparation_exterior_mem c χmeas χsrc ψ U Q₀ hreg e)

/-- The smooth correction is exactly the original complete auxiliary
normal followed by the original inverse on this source
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
theorem preparationAuxiliaryRepresentative_toL2 (e : SmoothResidual n) :
    smoothResidualToL2 n
      (preparationAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg e) =
        preparationAuxiliaryOutput (imageChannel c χmeas χsrc) ψ
          (Q₀ (smoothResidualToL2 n e)) :=
  uncutAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ _ _ _ _

/-- The uncut auxiliary correction is linear on the actual smooth source
space. It is the operator `B` in `BackgroundPreparation.run`, which is
subtracted in the residual ledger
(`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationAuxiliaryCorrection : SmoothResidual n →ₗ[ℝ] SmoothResidual n where
  toFun := preparationAuxiliaryRepresentative c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg
  map_add' e f := by
    apply smoothResidualToL2_injective n
    simp only [map_add,
      preparationAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg]
  map_smul' a e := by
    apply smoothResidualToL2_injective n
    simp only [map_smul, RingHom.id_apply,
      preparationAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg]

/-- The finite auxiliary sum in the smooth preparation ledger is the
literal finite sum of the original complete normal outputs. No number-of-
steps factor or re-chosen representative occurs
(`app:ch_mean_pairs:eq:mean-prepared-residual`). -/
theorem preparationAuxiliaryCorrection_sum_toL2 (e : ℕ → SmoothResidual n) (J : ℕ) :
    smoothResidualToL2 n
      (∑ i ∈ Finset.range J,
        preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg (e i)) =
      ∑ i ∈ Finset.range J, preparationAuxiliaryOutput (imageChannel c χmeas χsrc) ψ
        (Q₀ (smoothResidualToL2 n (e i))) := by
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact preparationAuxiliaryRepresentative_toL2 c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg (e i)

end FixedRow

end JanetCartan.CurrentMean
