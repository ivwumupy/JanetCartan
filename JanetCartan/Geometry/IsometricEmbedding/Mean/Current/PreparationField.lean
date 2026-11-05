module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationAuxiliary
public import JanetCartan.Geometry.IsometricEmbedding.Response.CurrentStrain

/-!
# The accumulated physical preparation field

The finite preparation in `app:ch_mean_pairs:prop:mean-coarse` subtracts
the literal half tangent lifts of the uncut image adjoints of the SAME `Q₀`.
This file constructs that physical correction, proves its support and
smoothness, and identifies its strain with the complete auxiliary sum only
on the common open plateau. The exterior output remains in the global ledger.
The source sequence can be the already constructed preparation run; no bound
or positivity of that run is assumed in these geometric identities.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CurrentMean
open ContinuumRow

variable {n N : ℕ} {ι : Type*} [Fintype ι]
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc ψ : C(Torus n, ℝ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)
    (e : ℕ → SmoothResidual n)

/-- The actual signed finite physical correction, with the original final
cutoff and fixed inverse (`app:ch_mean_pairs:eq:mean-density-recursion`). -/
def preparationAccumulatedField (F : Euclidean n → Euclidean N)
    (χout : Euclidean n → ℝ) (J : ℕ) : Euclidean n → Euclidean N :=
  -∑ k ∈ Finset.range J, preparationAuxiliaryField χsrc
    ((imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n (e k)))) F χout

/-- The finite correction preserves the original physical support. No
cutoff is inserted into the raw image or density data
(`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem support_preparationAccumulatedField_subset
    (F : Euclidean n → Euclidean N) (χout : Euclidean n → ℝ) (J : ℕ) :
    Function.support (preparationAccumulatedField c χmeas χsrc Q₀ e F χout J) ⊆
      Function.support χout := by
  intro x hx
  contrapose! hx
  have hz : χout x = 0 := by simpa only [Function.mem_support, not_not] using hx
  simp [preparationAccumulatedField, preparationAuxiliaryField, hz]

/-- Compact support of the same accumulated field follows from the single
fixed output cutoff (`app:ch_mean_pairs:prop:mean-coarse`). -/
theorem hasCompactSupport_preparationAccumulatedField
    (F : Euclidean n → Euclidean N) {χout : Euclidean n → ℝ}
    (hout : HasCompactSupport χout) (J : ℕ) :
    HasCompactSupport (preparationAccumulatedField c χmeas χsrc Q₀ e F χout J) :=
  hout.of_isClosed_subset (isClosed_tsupport _)
    (closure_mono (support_preparationAccumulatedField_subset c χmeas χsrc Q₀ e F χout J))

variable (hc : ∀ j, IsSmoothPeriodic (c j : Torus n → ℝ))
    (hm : IsSmoothPeriodic (χmeas : Torus n → ℝ))
    (hs : IsSmoothPeriodic (χsrc : Torus n → ℝ))
    (hψ : IsSmoothPeriodic (ψ : Torus n → ℝ))
    (U : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hreg : ∀ (f : SmoothResidual n) (s : ℕ),
      (augmentedRow (imageChannel c χmeas χsrc) U ψ).adjoint
        (Q₀ (smoothResidualToL2 n f)) ∈ CarrierSobolev.augmentedInputLevel n ι s)

include hreg in
private theorem image_mem (k s : ℕ) :
    (imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n (e k))) ∈
      periodicSobolevLevel n (Euclidean n) s := by
  rw [← AuxiliaryRawBand.augmentedAdjoint_image (imageChannel c χmeas χsrc) U ψ]
  exact ((CarrierSobolev.mem_augmentedInputLevel_iff s _).mp (hreg (e k) s)).1

include hs hreg in
/-- The signed finite sum is smooth on the actual immersion domain. The
input membership concerns the SAME original adjoint on smooth sources
(`app:ch_mean_pairs:eq:mean-coarse-field-profile`). -/
theorem contDiffOn_preparationAccumulatedField
    {F : Euclidean n → Euclidean N} {W : Set (Euclidean n)}
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W) (himm : IsImmersionOn F W)
    {χout : Euclidean n → ℝ} (hout : ContDiffOn ℝ ∞ χout W) (J : ℕ) :
    ContDiffOn ℝ ∞ (preparationAccumulatedField c χmeas χsrc Q₀ e F χout J) W := by
  apply ContDiffOn.neg
  simpa only [← Finset.sum_apply] using
    (ContDiffOn.sum (s := Finset.range J) (fun k _ ↦
      contDiffOn_preparationAuxiliaryField χsrc hs _
        (image_mem c χmeas χsrc ψ Q₀ e U hreg k) hW hF himm hout))

include hc hm hs hψ hreg in
/-- On the common open plateau, the accumulated physical strain is minus
the SAME complete auxiliary output sum. This is proved after smoothness;
the global exterior-augmented row is never declared to be physical strain
(`app:ch_mean_pairs:eq:mean-prepared-residual`). -/
theorem preparationAccumulatedField_strain_on_core
    {F : Euclidean n → Euclidean N} {W core : Set (Euclidean n)}
    (hW : IsOpen W) (hcore : IsOpen core) (hsub : core ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) (himm : IsImmersionOn F W)
    {χout : Euclidean n → ℝ} (hplateau : EqOn χout (fun _ ↦ 1) core)
    (hcoeff : ∀ x ∈ core, ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j)
    (hmeas : ∀ x ∈ core, χmeas (torusQuotient x) = 1)
    (hext : ∀ x ∈ core, ψ (torusQuotient x) = 1)
    (J : ℕ) {x : Euclidean n} (hx : x ∈ core) (i : Fin n) :
    tensorPairing (StressFrame.geometricCubeStress F x i).val
      (linearizedMetric F (preparationAccumulatedField c χmeas χsrc Q₀ e F χout J) x) =
      -∑ k ∈ Finset.range J,
        (preparationAuxiliaryCorrection c hc χmeas χsrc ψ hm hs hψ U Q₀ hreg (e k)).val
          (torusQuotient x) () i := by
  let V := fun k ↦ preparationAuxiliaryField χsrc
    ((imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n (e k)))) F χout
  have hout : ContDiffOn ℝ ∞ χout core := contDiffOn_const.congr hplateau
  have hV (k : ℕ) : DifferentiableAt ℝ (V k) x := by
    have h := contDiffOn_preparationAuxiliaryField χsrc hs _
      (image_mem c χmeas χsrc ψ Q₀ e U hreg k) hcore (hF.mono hsub)
      (fun y hy ↦ himm y (hsub hy)) hout
    exact (h.differentiableOn (by simp) x hx).differentiableAt (hcore.mem_nhds hx)
  have heq (k : ℕ) := uncutAuxiliaryRepresentative_eq_strain_on_core
    c hc χmeas χsrc ψ hm hs hψ
    ((imageChannel c χmeas χsrc).adjoint (Q₀ (smoothResidualToL2 n (e k))))
    (exteriorChannel ψ (Q₀ (smoothResidualToL2 n (e k))))
    (image_mem c χmeas χsrc ψ Q₀ e U hreg k)
    (fun s ↦ by
      rw [← AuxiliaryRawBand.augmentedAdjoint_exterior (imageChannel c χmeas χsrc) U ψ]
      exact ((CarrierSobolev.mem_augmentedInputLevel_iff s _).mp (hreg (e k) s)).2.2)
    hW hcore hsub hF himm hplateau hcoeff hmeas hext hx i
  have hneg := linearizedMetric_smul_apply (F := F)
    (DifferentiableAt.sum (u := Finset.range J) (fun k _ ↦ hV k)) (-1)
  simp only [neg_one_smul] at hneg
  change tensorPairing _ (linearizedMetric F (-(∑ k ∈ Finset.range J, V k)) x) = _
  rw [hneg, linearizedMetric_sum_apply _ V (fun k _ ↦ hV k)]
  have hpair : tensorPairing (StressFrame.geometricCubeStress F x i).val
      (-(∑ k ∈ Finset.range J, linearizedMetric F (V k) x)) =
      -∑ k ∈ Finset.range J, tensorPairing (StressFrame.geometricCubeStress F x i).val
        (linearizedMetric F (V k) x) := by
    simp only [tensorPairing, Matrix.neg_apply, Matrix.sum_apply, mul_neg,
      Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range J)]
  rw [hpair]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (heq k).symm

end JanetCartan.CurrentMean
