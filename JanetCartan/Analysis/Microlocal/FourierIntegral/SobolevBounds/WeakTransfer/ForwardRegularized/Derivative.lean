module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ForwardRegularized.CompactKernel

/-!
# The actual derivative of a compact-frequency forward operator

Combine differentiation of the compact integral with the source transfer from
`Source.lean`. The consumer is the output integration by parts proving the weak
pairing of `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.ForwardRegularized
variable {n r : ℕ}
variable {X Y F : Set (Euclidean n)} {S : Euclidean n → Euclidean n → ℝ}
  {A : FullAmplitude n r} {u : Euclidean n → Fin r → ℂ}

/-- Pointwise differentiation of the full kernel applied to the datum, with no
change to either mask (`app:ch_regular_base:eq:graph-derivative-transfer`). -/
theorem partialDeriv_integrand (x y η : Euclidean n) (i : Fin n)
    (hS : DifferentiableAt ℝ (fun z ↦ S z η) x)
    (hA : DifferentiableAt ℝ (fun z ↦ A z y η) x) :
    partialDeriv (fun z ↦ integrand S A u (z, (η, y))) x i =
      graphOscillation S x y η • (graphFirstOutputAmplitude S A i x y η).mulVec (u y) := by
  have hp : DifferentiableAt ℝ (fun z ↦ graphOscillation S z y η) x := by
    unfold graphOscillation
    fun_prop
  have hd := ResponseTransfer.partialDeriv_matrix_mulVec
    (fun z ↦ graphOscillation S z y η • A z y η) (fun _ ↦ u y) x i
    (hp.smul hA) (differentiableAt_const _)
  rw [partialDeriv_graphOscillation_smul_amplitude S A x y η i hS hA] at hd
  simpa [integrand, Matrix.smul_mulVec, partialDeriv] using hd

/-- Source integration by parts for the differentiated integrand, including
the zero-frequency case where the entire amplitude vanishes.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem integral_partialDeriv_integrand_transfer
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hF0 : (0 : Euclidean n) ∉ F)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hhom : ∀ x η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η))
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (x η : Euclidean n) (i : Fin n) :
    (∫ y, partialDeriv (fun z ↦ integrand S A u (z, (η, y))) x i) =
      (∫ y, integrand S (graphTransferRemainder S i A) u (x, (η, y))) +
        ∑ j, ∫ y, integrand S (graphTransferDatum S i j A)
          (fun y ↦ partialDeriv u y j) (x, (η, y)) := by
  by_cases hη : η = 0
  · subst η
    have ha (z y) : A z y 0 = 0 := hA.support z y 0 (Or.inr (Or.inr hF0))
    have hr (y) : graphTransferRemainder S i A x y 0 = 0 := by
      simp [graphTransferRemainder, ha, partialDeriv]
    simp [integrand, ha, hr, graphTransferDatum, partialDeriv]
  · have hx (z) : DifferentiableAt ℝ (fun z ↦ S z η) z :=
      ((hS z η hη).comp z (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hAxy : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η) :=
      hA.smooth.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
    have hAleft (y) : DifferentiableAt ℝ (fun z ↦ A z y η) x :=
      (hAxy.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x
    have hmixed (j) : DifferentiableAt ℝ
        (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x j) η := by
      have hs : ContDiffAt ℝ ∞ (fun q : Euclidean n × Euclidean n ↦ S q.2 q.1) (η, x) :=
        (hS x η hη).comp (η, x) (contDiffAt_snd.prodMk contDiffAt_fst)
      have ht : ContDiffAt ℝ ∞
          (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x j) η :=
        (hs.fderiv contDiffAt_const (by simp)).clm_apply contDiffAt_const
      exact ht.differentiableAt (by simp)
    simp_rw [partialDeriv_integrand x _ η i (hx x) (hAleft _)]
    exact integral_graphFirstOutputAmplitude_transfer S A u x η i hAxy hu hus
      (hx x) hmixed (hhom x η hη)

/-- The first actual output derivative of a compact-frequency forward graph
is the sum of the complete remainder and datum-derivative branches. This is
proved from the literal integral, not assumed as an operator recurrence.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem partialDeriv_graphOperator_transfer
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F) (hF0 : (0 : Euclidean n) ∉ F)
    (hS : ∀ x η, η ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (x, η))
    (hhom : ∀ x η, η ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
      (fun z ↦ S z (t • η)) =ᶠ[𝓝 x] (fun z ↦ t * S z η))
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hAK : ∀ x y η, η ∉ K → A x y η = 0) (x : Euclidean n) (i : Fin n) :
    partialDeriv (graphOperator S A u) x i =
      graphOperator S (graphTransferRemainder S i A) u x +
        ∑ j, graphOperator S (graphTransferDatum S i j A) (fun y ↦ partialDeriv u y j) x := by
  have hR := hA.graphTransferRemainder hX hY hF hF0 S hS i
  have hP (j) := hA.graphTransferDatum hF hF0 S hS i j
  have hRK : ∀ x y η, η ∉ K → graphTransferRemainder S i A x y η = 0 := by
    intro z y η hη
    have ha (z y) : A z y η = 0 := hAK z y η hη
    simp [graphTransferRemainder, ha, partialDeriv]
  have hPK (j) : ∀ x y η, η ∉ K → graphTransferDatum S i j A x y η = 0 := by
    intro z y η hη
    simp [graphTransferDatum, hAK z y η hη]
  have hu' (j) : ContDiff ℝ ∞ (fun y ↦ partialDeriv u y j) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hus' (j) : HasCompactSupport (fun y ↦ partialDeriv u y j) :=
    hus.fderiv_apply ℝ (EuclideanSpace.single j 1)
  have hiR := (integrable_integrand hR hF hF0 hS hu hus hK hRK x).integral_prod_left
  have hiP (j) := (integrable_integrand (hP j) hF hF0 hS (hu' j) (hus' j)
    hK (hPK j) x).integral_prod_left
  rw [partialDeriv_graphOperator_integral hA hF hF0 hS hu hus hK hAK x i]
  simp_rw [integral_partialDeriv_integrand_transfer hA hF0 hS hhom hu hus x _ i]
  rw [integral_add hiR (integrable_finsetSum Finset.univ (fun j _ ↦ hiP j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hiP j)]
  simp only [graphOperator, integrand, smul_add, Finset.smul_sum]

end JanetCartan.FourierIntegral.ForwardRegularized
