module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Neighborhood
public import JanetCartan.LinearAlgebra.GramProjection
public import JanetCartan.Analysis.Matrix.InverseBounds

/-!
# The stress Gram matrix in second-jet variables

The inverse Gram coefficient in `app:ch_background:eq:bg-frame-tame` is smooth
on the fixed reference neighborhood. The basis furnished by that neighborhood
proves invertibility. Local identification with the actual geometric frame
also identifies ambient derivatives at boundaries of closed chart balls.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

open StressFrame
open scoped StressFrame

variable {n N : ℕ}

/-- `app:ch_background:defn:bg-geometry`: the Gram matrix of the specified
projected cube stresses, expressed in second-jet variables. The matrix norm
is the Frobenius norm and its entries are the Frobenius tensor contractions. -/
def secondJetCubeStressGram (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (J : SecondJet (Euclidean n) (Euclidean N)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.gram ℝ (secondJetCubeStress F x J)

/-- `app:ch_background:defn:bg-geometry`: the proved kernel basis supplies
independence of the rational jet frame in the ambient symmetric tensor space. -/
theorem linearIndependent_secondJetCubeStress
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} {γ : ℝ}
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x J))
    (hf : HasCubeStressFrame (secondJetFixedSymmetricNormalMap F x J).ker γ) :
    LinearIndependent ℝ (secondJetCubeStress F x J) := by
  obtain ⟨b, hb⟩ := hf.1
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hs : ∑ j, c j • b j = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hb,
      secondJetCubeStress_eq_projectedCubeStress F x hB, projectedCubeStress] using hc
  have he := congrArg (fun z ↦ b.repr z i) hs
  simpa [Finsupp.single_apply] using he

/-- `app:ch_background:defn:bg-geometry`: Gram invertibility follows from
the supplied basis; no inverse or independence hypothesis is needed. -/
theorem secondJetCubeStressGram_isUnit
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} {γ : ℝ}
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x J))
    (hf : HasCubeStressFrame (secondJetFixedSymmetricNormalMap F x J).ker γ) :
    IsUnit (secondJetCubeStressGram F x J) :=
  (Matrix.posDef_gram_of_linearIndependent
    (linearIndependent_secondJetCubeStress F x hB hf)).isUnit

/-- `app:ch_background:eq:bg-frame-tame`: the Gram jet formula is smooth
where the first jet is immersive and the compared second form is surjective. -/
theorem contDiffAt_secondJetCubeStressGram
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} (hJ : Function.Injective J.1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x J)) :
    ContDiffAt ℝ ∞ (secondJetCubeStressGram F x) J := by
  let incl : (Fin n → Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { LinearMap.id with cont := continuous_id }
  apply incl.contDiff.contDiffAt.comp J
  exact contDiffAt_pi.mpr fun i ↦ contDiffAt_pi.mpr fun j ↦
    (contDiffAt_secondJetCubeStress F x hJ hB i).inner ℝ
      (contDiffAt_secondJetCubeStress F x hJ hB j)

/-- `app:ch_background:eq:bg-frame-tame`: inversion of the rational jet
Gram formula is smooth, using the basis to discharge invertibility. -/
theorem contDiffAt_secondJetCubeStressGram_inv
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} {γ : ℝ}
    (hJ : Function.Injective J.1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x J))
    (hf : HasCubeStressFrame (secondJetFixedSymmetricNormalMap F x J).ker γ) :
    ContDiffAt ℝ ∞ (fun K ↦ (secondJetCubeStressGram F x K)⁻¹) J :=
  (contDiffAt_matrix_inv (secondJetCubeStressGram_isUnit F x hB hf)).comp J
    (contDiffAt_secondJetCubeStressGram F x hJ hB)

/-- `app:ch_background:defn:bg-geometry`: the rational jet Gram matrix
agrees locally with the actual frame Gram matrix. -/
theorem eventuallyEq_secondJetCubeStressGram
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - firstJetNormalProjection (fderiv ℝ G y)‖ < 1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y))) :
    (secondJetCubeStressGram F x ∘ secondJet G) =ᶠ[𝓝 y]
      (fun z ↦ Matrix.gram ℝ (geometricCubeStress G z)) := by
  have he := Filter.eventually_all.mpr
    (fun i ↦ eventuallyEq_secondJetCubeStress F x hG hi hp hB i)
  filter_upwards [he] with z hz
  exact congrArg (Matrix.gram ℝ) (funext hz)

/-- `app:ch_background:eq:bg-frame-tame`: local equality of inverse Gram
formulas preserves ambient derivatives, including at closed-ball boundaries. -/
theorem eventuallyEq_secondJetCubeStressGram_inv
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - firstJetNormalProjection (fderiv ℝ G y)‖ < 1)
    (hB : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y))) :
    ((fun J ↦ (secondJetCubeStressGram F x J)⁻¹) ∘ secondJet G) =ᶠ[𝓝 y]
      (fun z ↦ (Matrix.gram ℝ (geometricCubeStress G z))⁻¹) := by
  filter_upwards [eventuallyEq_secondJetCubeStressGram F x hG hi hp hB] with z hz
  exact congrArg Inv.inv hz

end JanetCartan.GeometricProfile
