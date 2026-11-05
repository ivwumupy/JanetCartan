module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondForm
public import JanetCartan.Geometry.IsometricEmbedding.Normal.StressFrame

/-!
# Second-jet formulas for the actual stress projection

The fixed normal-space comparison in `app:ch_background:defn:bg-geometry`
turns the symmetric stress projection into a smooth rational second-jet
coefficient. Equality with the actual projection holds locally, which is
needed for ambient derivative bounds on closed chart balls.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

open StressFrame
open scoped StressFrame

variable {n N : ℕ}

/-- `app:ch_background:defn:bg-geometry`: the symmetric second form compared
in a fixed reference normal space, written in ambient second-jet variables. -/
def secondJetFixedSymmetricNormalMap (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (J : SecondJet (Euclidean n) (Euclidean N)) :
    SymmetricTensor n →L[ℝ] normalSpace F x :=
  (normalSpace F x).orthogonalProjectionOnto.comp
    ((secondJetNormalMap J).comp (symmetricTensorSubmodule n).subtypeL)

/-- `app:ch_background:eq:bg-frame-tame`: the rational symmetric kernel projector. -/
def secondJetStressProjection (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (J : SecondJet (Euclidean n) (Euclidean N)) :
    SymmetricTensor n →L[ℝ] SymmetricTensor n :=
  NormalInverse.continuousKernelProjection (secondJetFixedSymmetricNormalMap F x J)

/-- `app:ch_background:defn:bg-geometry`: the projected frozen cube tensors,
as functions of the second jet. -/
def secondJetCubeStress (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (J : SecondJet (Euclidean n) (Euclidean N))
    (i : Fin n) : SymmetricTensor n :=
  secondJetStressProjection F x J (cubeSymmetricStress n i)

/-- `app:ch_background:eq:bg-frame-tame`: the fixed-space second form is
smooth wherever the first jet is immersive. -/
theorem contDiffAt_secondJetFixedSymmetricNormalMap
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : Function.Injective J.1) :
    ContDiffAt ℝ ∞ (secondJetFixedSymmetricNormalMap F x) J :=
  contDiffAt_const.clm_comp
    ((contDiffAt_secondJetNormalMap (firstJetMetric_isUnit_of_injective hJ)).clm_comp
      contDiffAt_const)

/-- `app:ch_background:eq:bg-frame-tame`: smoothness follows from the explicit
surjective-operator inverse formula. -/
theorem contDiffAt_secondJetStressProjection
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : Function.Injective J.1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x J)) :
    ContDiffAt ℝ ∞ (secondJetStressProjection F x) J :=
  NormalInverse.contDiffAt_kernelProjection_family
    (contDiffAt_secondJetFixedSymmetricNormalMap F x hJ) hB

/-- `app:ch_background:eq:bg-frame-tame`: smoothness of the specified projected
cube stress follows by evaluating the projector on the frozen tensor. -/
theorem contDiffAt_secondJetCubeStress
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : Function.Injective J.1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x J)) (i : Fin n) :
    ContDiffAt ℝ ∞ (fun K ↦ secondJetCubeStress F x K i) J :=
  (contDiffAt_secondJetStressProjection F x hJ hB).clm_apply contDiffAt_const

/-- `app:ch_background:defn:bg-geometry`: the jet comparison is the existing
geometric fixed normal-space comparison. -/
theorem secondJetFixedSymmetricNormalMap_eq
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y)) :
    secondJetFixedSymmetricNormalMap F x (secondJet G y) =
      fixedSymmetricNormalMap F x G y := by
  rw [secondJetFixedSymmetricNormalMap, secondJetNormalMap_eq hG hi]
  rfl

/-- `app:ch_background:defn:bg-geometry`: equality with the actual symmetric
stress-kernel projector uses injectivity of normal-space comparison. -/
theorem secondJetStressProjection_eq
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - normalProjection G y‖ < 1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y))) :
    secondJetStressProjection F x (secondJet G y) =
      (symmetricNormalMap G y).ker.starProjection := by
  rw [secondJetStressProjection,
    NormalInverse.continuousKernelProjection_eq_starProjection _ hB,
    secondJetFixedSymmetricNormalMap_eq F x hG hi]
  exact congrArg (fun K : Submodule ℝ (SymmetricTensor n) ↦ K.starProjection)
    (fixedSymmetricNormalMap_ker F G x y hp)

/-- `app:ch_background:defn:bg-geometry`: identification of the prescribed
projected cube stress, with no basis hypothesis. -/
theorem secondJetCubeStress_eq
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - normalProjection G y‖ < 1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y)))
    (i : Fin n) :
    secondJetCubeStress F x (secondJet G y) i = geometricCubeStress G y i := by
  rw [secondJetCubeStress, secondJetStressProjection_eq F x hG hi hp hB]
  rfl

/-- `app:ch_background:eq:bg-frame-tame`: the strict low-order conditions
persist locally. Thus identification preserves all ambient derivatives. -/
theorem eventuallyEq_secondJetStressProjection
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - firstJetNormalProjection (fderiv ℝ G y)‖ < 1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y))) :
    (secondJetStressProjection F x ∘ secondJet G) =ᶠ[𝓝 y]
      (fun z ↦ (symmetricNormalMap G z).ker.starProjection) := by
  have hd := hG.fderiv_right (m := ∞) (by simp)
  have hei := hd.continuous.continuousAt.eventually
    (ContinuousLinearMap.isOpen_injective.mem_nhds hi)
  have hproj := (contDiffAt_firstJetNormalProjection
    (firstJetMetric_isUnit_of_injective hi)).continuousAt.comp hd.continuous.continuousAt
  have hep := (continuousAt_const.sub hproj).norm.eventually (gt_mem_nhds hp)
  have heb := ((contDiffAt_secondJetFixedSymmetricNormalMap F x hi).continuousAt.comp
    (contDiff_secondJet hG).continuous.continuousAt).eventually
      (NormalInverse.isOpen_surjective.mem_nhds hB)
  filter_upwards [hei, hep, heb] with z hz hzp hzb
  change ‖normalProjection F x - firstJetNormalProjection (fderiv ℝ G z)‖ < 1 at hzp
  rw [firstJetNormalProjection_eq hz] at hzp
  exact secondJetStressProjection_eq F x hG hz hzp hzb

/-- `app:ch_background:eq:bg-frame-tame`: local identification for each cube stress. -/
theorem eventuallyEq_secondJetCubeStress
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - firstJetNormalProjection (fderiv ℝ G y)‖ < 1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y)))
    (i : Fin n) :
    ((fun J ↦ secondJetCubeStress F x J i) ∘ secondJet G) =ᶠ[𝓝 y]
      (fun z ↦ geometricCubeStress G z i) := by
  filter_upwards [eventuallyEq_secondJetStressProjection F x hG hi hp hB] with z hz
  exact congrArg (fun P : SymmetricTensor n →L[ℝ] SymmetricTensor n ↦
    P (cubeSymmetricStress n i)) hz

end JanetCartan.GeometricProfile
