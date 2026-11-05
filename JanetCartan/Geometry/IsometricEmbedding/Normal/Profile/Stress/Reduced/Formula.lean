module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Stress.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.Reconstruction.Field
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Reduction

/-!
# All coefficients of the actual reduced strain operator

The expansion in `app:ch_waves:eq:reduced-symbol` includes the contraction
of the projected stress with the induced connection. The existing
`secondJetChristoffel` supplies its explicit rational second-jet formula.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.GeometricProfile

open StressFrame
open scoped StressFrame

variable {n N : ℕ}

/-- The zeroth-order matrix of `app:ch_waves:eq:reduced-symbol`, including
the negative contraction with the actual induced Christoffel coefficients. -/
def reducedZerothCoefficient (G : Euclidean n → Euclidean N)
    (Q : Fin n → MetricTensor n) (y : Euclidean n) : MetricTensor n :=
  fun i k ↦ -∑ a, ∑ b, Q i a b * christoffel G y a b k

/-- `app:ch_waves:eq:reduced-symbol`: symmetry removes the factor one half
in the derivative part, while retaining the entire connection term.
This identity is algebraic and requires no regularity of the covector. -/
theorem reducedOperator_eq_coefficients (G : Euclidean n → Euclidean N)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (u : Euclidean n → Euclidean n) (y : Euclidean n)
    (hQ : ∀ i, (Q y i).IsSymm) (i : Fin n) :
    NullTransport.reducedOperator G Q u y i =
      (∑ a, ∑ k, NullTransport.principalCoefficient (Q y) a i k *
        partialDeriv (fun z ↦ u z k) y a) +
      ∑ k, reducedZerothCoefficient G (Q y) y i k * u y k := by
  have hs : (∑ a, ∑ b, Q y i a b * partialDeriv (fun z ↦ u z a) y b) =
      ∑ a, ∑ b, Q y i a b * partialDeriv (fun z ↦ u z b) y a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [(hQ i).apply b a]
  have hz : (∑ a, ∑ b, Q y i a b *
      ∑ k, christoffel G y a b k * u y k) =
      ∑ k, (∑ a, ∑ b, Q y i a b * christoffel G y a b k) * u y k := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact (Finset.sum_congr rfl (fun a _ ↦ Finset.sum_comm)).trans Finset.sum_comm
  simp only [NullTransport.reducedOperator, tensorPairing, symmCovariantDeriv,
    mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_div,
    NullTransport.principalCoefficient, reducedZerothCoefficient,
    neg_mul, Finset.sum_neg_distrib]
  rw [hs, hz]
  ring

/-- Indices for every scalar coefficient of `app:ch_waves:eq:reduced-symbol`:
`inl (a,i,k)` is the coefficient of `∂ₐuₖ` in row `i`, and `inr (i,k)`
is the coefficient of `uₖ`. The function space uses its finite supremum norm. -/
abbrev ReducedCoefficientIndex (n : ℕ) :=
  (Fin n × Fin n × Fin n) ⊕ (Fin n × Fin n)

/-- The full coefficient field of the actual operator with the prescribed
geometric cube stresses (`app:ch_background:defn:bg-geometry`). -/
def geometricReducedCoefficients (G : Euclidean n → Euclidean N)
    (y : Euclidean n) : ReducedCoefficientIndex n → ℝ
  | .inl (a, i, k) =>
      NullTransport.principalCoefficient (fun j ↦ (geometricCubeStress G y j).val) a i k
  | .inr (i, k) =>
      reducedZerothCoefficient G (fun j ↦ (geometricCubeStress G y j).val) y i k

/-- The rational second-jet coefficients of `app:ch_background:eq:bg-frame-tame`.
The zeroth-order entry is exactly `-∑ₐᵦ Qᵢ(a,b) Γₐᵦᵏ`; the Christoffel
formula uses the inverse first-jet metric and the Hessian contraction. -/
def secondJetReducedCoefficients (F : Euclidean n → Euclidean N)
    (x : Euclidean n) (J : SecondJet (Euclidean n) (Euclidean N)) :
    ReducedCoefficientIndex n → ℝ
  | .inl (a, i, k) => (secondJetCubeStress F x J i).val a k
  | .inr (i, k) => -∑ a, ∑ b,
      (secondJetCubeStress F x J i).val a b * secondJetChristoffel J a b k

/-- `app:ch_waves:eq:reduced-symbol`: the coefficient package expands the
existing operator, with precisely its symmetrized covariant derivative convention. -/
theorem reducedOperator_geometricCubeStress_eq (G : Euclidean n → Euclidean N)
    (u : Euclidean n → Euclidean n) (y : Euclidean n) (i : Fin n) :
    NullTransport.reducedOperator G (fun z j ↦ (geometricCubeStress G z j).val) u y i =
      (∑ a, ∑ k, geometricReducedCoefficients G y (.inl (a, i, k)) *
        partialDeriv (fun z ↦ u z k) y a) +
      ∑ k, geometricReducedCoefficients G y (.inr (i, k)) * u y k := by
  apply reducedOperator_eq_coefficients
  intro j
  exact (geometricCubeStress G y j).property

private def stressEntry (a b : Fin n) : SymmetricTensor n →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) b).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) a))).comp
        (symmetricTensorSubmodule n).subtypeL

/-- `app:ch_background:eq:bg-frame-tame`: smoothness of every coefficient
follows from the explicit jet formulas on the immersive, surjective locus. -/
theorem contDiffAt_secondJetReducedCoefficients
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {J : SecondJet (Euclidean n) (Euclidean N)} (hi : Function.Injective J.1)
    (hb : Function.Surjective (secondJetFixedSymmetricNormalMap F x J)) :
    ContDiffAt ℝ ∞ (secondJetReducedCoefficients F x) J := by
  have hq (i a b : Fin n) : ContDiffAt ℝ ∞
      (fun K ↦ (secondJetCubeStress F x K i).val a b) J :=
    (stressEntry a b).contDiff.contDiffAt.comp J (contDiffAt_secondJetCubeStress F x hi hb i)
  apply contDiffAt_pi.mpr
  intro c
  rcases c with ⟨a, i, k⟩ | ⟨i, k⟩
  · exact hq i a k
  · exact (ContDiffAt.sum fun a _ ↦ ContDiffAt.sum fun b _ ↦
      (hq i a b).mul (contDiffAt_secondJetChristoffel
        (firstJetMetric_isUnit_of_injective hi) a b k)).neg

/-- `app:ch_background:defn:bg-geometry`: identification with all actual
coefficients uses the proved stress identification and Hessian connection formula. -/
theorem secondJetReducedCoefficients_eq
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - normalProjection G y‖ < 1)
    (hb : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y))) :
    secondJetReducedCoefficients F x (secondJet G y) = geometricReducedCoefficients G y := by
  funext c
  rcases c with ⟨a, i, k⟩ | ⟨i, k⟩
  · simp only [secondJetReducedCoefficients, geometricReducedCoefficients,
      NullTransport.principalCoefficient, secondJetCubeStress_eq F x hG hi hp hb]
  · simp only [secondJetReducedCoefficients, geometricReducedCoefficients,
      reducedZerothCoefficient, secondJetCubeStress_eq F x hG hi hp hb,
      secondJetChristoffel_eq hG]

/-- `app:ch_background:eq:bg-frame-tame`: local identification preserves
ambient derivatives, including derivatives on the boundary of a closed ball. -/
theorem eventuallyEq_secondJetReducedCoefficients
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - firstJetNormalProjection (fderiv ℝ G y)‖ < 1)
    (hb : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y))) :
    (secondJetReducedCoefficients F x ∘ secondJet G) =ᶠ[𝓝 y]
      geometricReducedCoefficients G := by
  have hq : ∀ᶠ z in 𝓝 y, ∀ i,
      secondJetCubeStress F x (secondJet G z) i = geometricCubeStress G z i :=
    Filter.eventually_all.mpr fun i ↦ eventuallyEq_secondJetCubeStress F x hG hi hp hb i
  filter_upwards [hq] with z hz
  funext c
  rcases c with ⟨a, i, k⟩ | ⟨i, k⟩
  · simp only [Function.comp_apply, secondJetReducedCoefficients,
      geometricReducedCoefficients, NullTransport.principalCoefficient, hz]
  · simp only [Function.comp_apply, secondJetReducedCoefficients,
      geometricReducedCoefficients, reducedZerothCoefficient, hz, secondJetChristoffel_eq hG]

/-- `app:ch_background:eq:bg-frame-tame`: the actual coefficient field is
smooth at every point satisfying the explicit low-order geometric conditions. -/
theorem contDiffAt_geometricReducedCoefficients
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    {G : Euclidean n → Euclidean N} (hG : ContDiff ℝ ∞ G) {y : Euclidean n}
    (hi : Function.Injective (fderiv ℝ G y))
    (hp : ‖normalProjection F x - firstJetNormalProjection (fderiv ℝ G y)‖ < 1)
    (hb : Function.Surjective (secondJetFixedSymmetricNormalMap F x (secondJet G y))) :
    ContDiffAt ℝ ∞ (geometricReducedCoefficients G) y := by
  exact ((contDiffAt_secondJetReducedCoefficients F x hi hb).comp y
    (contDiff_secondJet hG).contDiffAt).congr_of_eventuallyEq
      (eventuallyEq_secondJetReducedCoefficients F x hG hi hp hb).symm

end JanetCartan.GeometricProfile
