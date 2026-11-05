module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SupportedSobolev.ForwardCompact

/-!
# The actual derivative of a compact-frequency forward operator

Combine differentiation of the compact integral with the source transfer from
`Source.lean`. The consumer is the output integration by parts proving the weak
pairing of `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.SupportedSobolev.ForwardRegularized
open FourierIntegral.ForwardRegularized FullAmplitudePrimitiveBudget.Local
variable {n r : ℕ}
variable {U : Set (Point n)} {X Y F : Set (Euclidean n)} {S : Euclidean n → Euclidean n → ℝ}
  {A : FullAmplitude n r} {u : Euclidean n → Fin r → ℂ}

/-- Differentiation of the supported integrand uses phase jets only where the
closed carrier is present. Off the carrier both sides vanish locally.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem partialDeriv_integrand
    (hA : ForwardAmplitudeAdmissible X Y F A) (hX : IsClosed X)
    (hF0 : (0 : Euclidean n) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (x y η : Euclidean n) (i : Fin n) :
    partialDeriv (fun z ↦ integrand S A u (z, (η, y))) x i =
      graphOscillation S x y η • (graphFirstOutputAmplitude S A i x y η).mulVec (u y) := by
  by_cases hc : ((x, y), η) ∈ (X ×ˢ Y) ×ˢ F
  · have hη : η ≠ 0 := fun hz ↦ hF0 (hz ▸ hc.2)
    have hx := ((hS _ (hcarrier hc) hη).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have ha : DifferentiableAt ℝ (fun z ↦ A z y η) x := (hA.smooth.comp
      (contDiff_id.prodMk (contDiff_const.prodMk contDiff_const))).differentiable (by simp) x
    exact FourierIntegral.ForwardRegularized.partialDeriv_integrand x y η i hx ha
  · have ho : x ∉ X ∨ y ∉ Y ∨ η ∉ F := by
      change ¬ ((x ∈ X ∧ y ∈ Y) ∧ η ∈ F) at hc
      tauto
    have he : (fun z ↦ integrand S A u (z, (η, y))) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      rcases ho with hx | hy | hη
      · filter_upwards [hX.isOpen_compl.mem_nhds hx] with z hz
        simp [integrand, hA.support z y η (Or.inl hz)]
      · exact Filter.Eventually.of_forall fun z ↦ by
          simp [integrand, hA.support z y η (Or.inr (Or.inl hy))]
      · exact Filter.Eventually.of_forall fun z ↦ by
          simp [integrand, hA.support z y η (Or.inr (Or.inr hη))]
    have hd := (hA.outputPartial hX i).support x y η ho
    simp only [partialDeriv, he.fderiv_eq (𝕜 := ℝ)]
    simp [graphFirstOutputAmplitude, hA.support x y η ho, hd]

/-- Source integration by parts at a supported covector; no phase hypothesis is
imposed on the complement of the chart. Source:
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem integral_partialDeriv_integrand_transfer
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F)
    (hF0 : (0 : Euclidean n) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hhom : SupportedPhaseHomogeneity S U)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (x η : Euclidean n) (i : Fin n) :
    (∫ y, partialDeriv (fun z ↦ integrand S A u (z, (η, y))) x i) =
      (∫ y, integrand S (graphTransferRemainder S i A) u (x, (η, y))) +
        ∑ j, ∫ y, integrand S (graphTransferDatum S i j A)
          (fun y ↦ partialDeriv u y j) (x, (η, y)) := by
  simp_rw [partialDeriv_integrand hA hX hF0 hcarrier hS x _ η i]
  by_cases hc : ∃ y, ((x, y), η) ∈ (X ×ˢ Y) ×ˢ F
  · obtain ⟨y, hy⟩ := hc
    have hη : η ≠ 0 := fun hz ↦ hF0 (hz ▸ hy.2)
    have hs := hS _ (hcarrier hy) hη
    have hx := (hs.comp x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hAxy : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η) :=
      hA.smooth.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
    have hmixed (j) : DifferentiableAt ℝ
        (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x j) η := by
      have ht : ContDiffAt ℝ ∞ (fun q : Euclidean n × Euclidean n ↦ S q.2 q.1) (η, x) :=
        hs.comp (η, x) (contDiffAt_snd.prodMk contDiffAt_fst)
      have hd : ContDiffAt ℝ ∞ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x j) η :=
        (ht.fderiv contDiffAt_const (by simp)).clm_apply contDiffAt_const
      exact hd.differentiableAt (by simp)
    exact integral_graphFirstOutputAmplitude_transfer S A u x η i hAxy hu hus
      hx hmixed (hhom _ (hcarrier hy) hη)
  · have ho (y) : x ∉ X ∨ y ∉ Y ∨ η ∉ F := by
      have hn := fun h ↦ hc ⟨y, h⟩
      change ¬ ((x ∈ X ∧ y ∈ Y) ∧ η ∈ F) at hn
      tauto
    have ha (y) := hA.support x y η (ho y)
    have hd (y) := (hA.outputPartial hX i).support x y η (ho y)
    have hr (y) := (hA.graphTransferRemainder_of_supported S hX hY hF hF0 hcarrier hS i).support x y η (ho y)
    simp [integrand, graphFirstOutputAmplitude, graphTransferDatum, ha, hd, hr]

/-- The first actual output derivative of a compact-frequency forward graph
is the sum of the complete remainder and datum-derivative branches. This is
proved from the literal integral, not assumed as an operator recurrence.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem partialDeriv_graphOperator_transfer
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F) (hF0 : (0 : Euclidean n) ∉ F)
    (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U) (hS : SupportedPhaseRegularity S U)
    (hhom : SupportedPhaseHomogeneity S U)
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hAK : ∀ x y η, η ∉ K → A x y η = 0) (x : Euclidean n) (i : Fin n) :
    partialDeriv (graphOperator S A u) x i =
      graphOperator S (graphTransferRemainder S i A) u x +
        ∑ j, graphOperator S (graphTransferDatum S i j A) (fun y ↦ partialDeriv u y j) x := by
  have hR := hA.graphTransferRemainder_of_supported S hX hY hF hF0 hcarrier hS i
  have hP (j) := hA.graphTransferDatum_of_supported S hX hY hF hF0 hcarrier hS i j
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
  have hiR := (integrable_integrand hR hX hY hF hF0 hcarrier hS hu hus hK hRK x).integral_prod_left
  have hiP (j) := (integrable_integrand (hP j) hX hY hF hF0 hcarrier hS (hu' j) (hus' j)
    hK (hPK j) x).integral_prod_left
  rw [partialDeriv_graphOperator_integral hA hX hY hF hF0 hcarrier hS hu hus hK hAK x i]
  simp_rw [integral_partialDeriv_integrand_transfer hA hX hY hF hF0 hcarrier hS hhom hu hus x _ i]
  rw [integral_add hiR (integrable_finsetSum Finset.univ (fun j _ ↦ hiP j)),
    integral_finsetSum Finset.univ (fun j _ ↦ hiP j)]
  simp only [graphOperator, integrand, smul_add, Finset.smul_sum]

end JanetCartan.FourierIntegral.SupportedSobolev.ForwardRegularized
