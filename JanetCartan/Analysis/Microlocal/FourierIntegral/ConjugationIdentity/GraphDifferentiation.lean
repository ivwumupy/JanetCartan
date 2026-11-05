module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation.CompactIntegral
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation.Integrand

/-!
# Differentiating the literal compact-frequency graph operator

This proves the output-differentiation step of
`app:ch_regular_base:eq:direct-graph-identity` in `paper.tex`. Joint smoothness,
a fixed compact frequency carrier, and a smooth compactly supported source
supply integrability, local domination, and differentiation under the integral.
The result retains the literal iterated Euclidean Lebesgue integrals and the
normalization `(2π)⁻ⁿ`. Frequency cutoffs depending only on `η` belong to `b`.

The parent conjugation construction must instantiate the amplitude and prove
the eikonal and transport cancellations; none is assumed or asserted here.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral

/-- Differentiation of the actual compact-frequency graph operator in
`app:ch_regular_base:eq:direct-graph-identity`. The amplitude is independent of
the source coordinate. The output domain is open, and the frequency carrier
is uniform over that domain. No differentiated-integral or domination premise
is required. The coefficients `A, B` need no regularity for this pointwise identity. -/
theorem physicalOperator_graphOperator {n r : ℕ}
    (A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → Euclidean n → ℝ)
    (b : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (v : Euclidean n → Fin r → ℂ)
    {U K : Set (Euclidean n)} (hU : IsOpen U) (hK : IsCompact K)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ univ))
    (hb : ContDiffOn ℝ ∞ (Function.uncurry b) (U ×ˢ univ))
    (hbK : ∀ x ∈ U, ∀ η ∉ K, b x η = 0)
    (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v)
    {x : Euclidean n} (hx : x ∈ U) :
    physicalOperator A B (graphOperator S (fun x _ η ↦ b x η) v) x =
      graphOperator S (fun x _ η ↦
        (∑ j, ((partialDeriv (fun z ↦ S z η) x j : ℝ) : ℂ) • A x j) * b x η +
          transportRemainder (A x) (fun j ↦ partialDeriv (fun z ↦ b z η) x j)
            (B x) (b x η)) v x := by
  let f : Euclidean n × (Euclidean n × Euclidean n) → Fin r → ℂ :=
    fun p ↦ graphOscillation S p.1 p.2.2 p.2.1 • (b p.1 p.2.1).mulVec (v p.2.2)
  let μ : Measure (Euclidean n × Euclidean n) := volume.prod volume
  let c : ℂ := ((2 * Real.pi) ^ n : ℂ)⁻¹
  have hf : ContDiffOn ℝ ∞ f (U ×ˢ univ) :=
    GraphDifferentiation.contDiffOn_integrand hS hb hv
  have hs : ∀ z ∈ U, ∀ p ∉ K ×ˢ tsupport v, f (z, p) = 0 := by
    intro z hz p hp
    by_cases hη : p.1 ∈ K
    · have hy : p.2 ∉ tsupport v := fun hy ↦ hp ⟨hη, hy⟩
      simp [f, image_eq_zero_of_notMem_tsupport hy]
    · simp [f, hbK z hz p.1 hη]
  have hcarrier : IsCompact (K ×ˢ tsupport v) := hK.prod hvK
  have hi (z : Euclidean n) (hz : z ∈ U) : Integrable (fun p ↦ f (z, p)) μ :=
    GraphDifferentiation.integrable_section hcarrier hf.continuousOn hs hz
  have he : graphOperator S (fun z _ η ↦ b z η) v =ᶠ[𝓝 x]
      fun z ↦ c • ∫ p, f (z, p) ∂μ := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact congrArg (c • ·) (integral_prod _ (hi z hz)).symm
  have hd := GraphDifferentiation.hasFDerivAt_integral (μ := μ) hU hcarrier hf hs hx
  have hscale : physicalOperator A B (fun z ↦ c • ∫ p, f (z, p) ∂μ) x =
      c • physicalOperator A B (fun z ↦ ∫ p, f (z, p) ∂μ) x := by
    have h := physicalOperator_cutoff_commutator A B (fun _ ↦ c)
      (fun z ↦ ∫ p, f (z, p) ∂μ) x (differentiableAt_const _) hd.differentiableAt
    simpa [partialDeriv] using sub_eq_zero.mp (by simpa [partialDeriv] using h)
  rw [physicalOperator_congr_of_eventuallyEq A B _ _ x he, hscale,
    GraphDifferentiation.physicalOperator_integral hU hcarrier hf hs A B hx,
    integral_prod _ (GraphDifferentiation.integrable_physicalOperator
      (μ := μ) hU hcarrier hf hs A B hx)]
  unfold graphOperator
  apply congrArg (c • ·)
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with y
  have hSx : DifferentiableAt ℝ (fun z ↦ S z η) x :=
    ((hS.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ η⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hbx : DifferentiableAt ℝ (fun z ↦ b z η) x :=
    ((hb.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ η⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  exact GraphDifferentiation.physicalOperator_integrand A B S b v x y η hSx hbx

end JanetCartan.FourierIntegral
