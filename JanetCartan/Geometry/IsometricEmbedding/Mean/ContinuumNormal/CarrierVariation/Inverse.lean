module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.InverseStability.Assembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.ForwardJets
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Smooth

/-!
# Comparison of the actual carrier inverse points

The inverse step of `paper-v2.tex`, `app:ch_osc:prop:osc-normal`, Step 4'.
The reference, compact convex source, compact target and normalization are fixed
before the comparison constant. The varying inputs are the original augmented
transport map and its genuine inverse. No inverse-jet difference is assumed.

Consumer: the full two-position density comparison in `CarrierVariation`.
The geometric producer must supply common domains, inverse identities and the
normalized differential gap. Jacobian and coefficient comparison are separate
obligations; this module does not assert normal-operator continuity.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation
open ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- Quantitative finite mixed-jet comparison of the literal full inverse
coordinates, from differences of the normalized original transport maps.
Both positions and the spectator remain among the variables. The fixed
reference may use one additional derivative in the constant; the varying
difference is measured only to order `m`.
Source: `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_inverseCoordinates_sub_le
    {Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hQ : IsCompact Q)
    (hW : IsOpen W) (hKW : K ⊆ W) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hY₀ : ContDiffOn ℝ ∞ (augmentedTransportGradient Y₀) W)
    (hu₀ : ContDiffOn ℝ ∞ u₀ Ω)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hrange₀ : MapsTo (inverseCoordinates u₀) Q K)
    (heq₀ : ∀ p ∈ Ω, transportAveragedGradient Y₀ (inverseCoordinates u₀ p) = p.1.2.2)
    (m : ℕ) :
    ∃ C > (0 : ℝ), ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)),
      ContDiffOn ℝ ∞ (augmentedTransportGradient Y) W → ContDiffOn ℝ ∞ u Ω →
      MapsTo (inverseCoordinates u) Q K →
      (∀ p ∈ Ω, transportAveragedGradient Y (inverseCoordinates u p) = p.1.2.2) →
      (∀ q ∈ K,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient Y) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      cNorm K m ((A.symm ∘ augmentedTransportGradient Y) -
        (A.symm ∘ augmentedTransportGradient Y₀)) ≤ 1 →
      cNorm Q m (inverseCoordinates u - inverseCoordinates u₀) ≤
        C * cNorm K m ((A.symm ∘ augmentedTransportGradient Y) -
          (A.symm ∘ augmentedTransportGradient Y₀)) := by
  let L : (Variables n × Euclidean 2) →L[ℝ] InputVariables n := A.symm
  have hright₀ := augmentedTransportGradient_inverseCoordinates Y₀ u₀ heq₀
  obtain ⟨C, hC, hb⟩ := HamiltonPhase.InverseContinuity.exists_normalized_inverse_stability
    hK hconv hQ hW hKW hΩ hQΩ (hY₀.continuousLinearMap_comp L)
    (inverseCoordinates_contDiffOn hu₀) L hrange₀
    (fun p hp ↦ congrArg L (hright₀ hp)) m
  refine ⟨C, hC, ?_⟩
  intro Y u hY hu hrange heq hgap hsmall
  have hright := augmentedTransportGradient_inverseCoordinates Y u heq
  apply hb (L ∘ augmentedTransportGradient Y) (inverseCoordinates u)
    (hY.continuousLinearMap_comp L) (inverseCoordinates_contDiffOn hu) hrange
    (fun p hp ↦ congrArg L (hright hp)) _ hsmall
  intro q hq
  rw [(L.hasFDerivAt.comp q
    ((hY.contDiffAt (hW.mem_nhds (hKW hq))).differentiableAt (by simp)).hasFDerivAt).fderiv]
  exact hgap q hq

/-- The quantitative inverse comparison yields convergence for any parameter
filter, in particular `σ → 0`, once the original normalized transport maps
converge and their common inverse charts have been produced. This is an
implication from primitive convergence, not an assertion that a geometric
family already satisfies those premises.
Source: `app:ch_background:prop:bg-frame`, the limit `σ = 0`. -/
theorem tendsto_inverseCoordinates_sub_cNorm
    {ι : Type*} {l : Filter ι}
    {Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {u₀ : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hQ : IsCompact Q)
    (hW : IsOpen W) (hKW : K ⊆ W) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hY₀ : ContDiffOn ℝ ∞ (augmentedTransportGradient Y₀) W)
    (hu₀ : ContDiffOn ℝ ∞ u₀ Ω)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hrange₀ : MapsTo (inverseCoordinates u₀) Q K)
    (heq₀ : ∀ p ∈ Ω, transportAveragedGradient Y₀ (inverseCoordinates u₀ p) = p.1.2.2)
    (m : ℕ)
    (Y : ι → Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
    (u : ι → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (hfamily : ∀ᶠ t in l,
      ContDiffOn ℝ ∞ (augmentedTransportGradient (Y t)) W ∧
      ContDiffOn ℝ ∞ (u t) Ω ∧ MapsTo (inverseCoordinates (u t)) Q K ∧
      (∀ p ∈ Ω, transportAveragedGradient (Y t) (inverseCoordinates (u t) p) = p.1.2.2) ∧
      (∀ q ∈ K,
        ‖(A.symm : (Variables n × Euclidean 2) →L[ℝ] InputVariables n).comp
          (fderiv ℝ (augmentedTransportGradient (Y t)) q) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2))
    (hlim : Tendsto (fun t ↦ cNorm K m ((A.symm ∘ augmentedTransportGradient (Y t)) -
      (A.symm ∘ augmentedTransportGradient Y₀))) l (𝓝 0)) :
    Tendsto (fun t ↦ cNorm Q m (inverseCoordinates (u t) - inverseCoordinates u₀))
      l (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_inverseCoordinates_sub_le
    hK hconv hQ hW hKW hΩ hQΩ hY₀ hu₀ A hrange₀ heq₀ m
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ cNorm_nonneg _ _ _)
    (hfamily.and hsmall |>.mono fun t ht ↦
      hb (Y t) (u t) ht.1.1 ht.1.2.1 ht.1.2.2.1 ht.1.2.2.2.1 ht.1.2.2.2.2 ht.2.le)
  simpa using hlim.const_mul C

end JanetCartan.ContinuumNormal.CarrierVariation
