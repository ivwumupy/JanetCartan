module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.SmallerInputs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Geometry.Freezing

/-!
# Construct the smaller masks and their frozen supported shell

The original supported-shell refinement gives two caps. A fresh buffered
inverse is then constructed below these caps, the retained outer radii and
the common output radius. The smaller canonical inverse and both original
masks are therefore compatible with inverse enlargement, with no unrestricted
shell premise. Consumer: the primitive frozen realization
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ContinuumNormalReduction TransportSymbol

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Construct smaller canonical inverse inputs and the actual frozen
supported shell together. The only differential premise is the original
half-gap supplied by `exists_frozen_primitive_balls`; the small inverse,
transverse estimate, and all mask inequalities are proved from fixed data.
Source: `new:lem:scaling`, `app:ch_background:eq:bg-Psi`. -/
theorem exists_frozen_supported_refinement {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    {k : Euclidean n} (hk : k ≠ 0) (hinc : incidence k (P.toFun z₀) = 0)
    (hd : fderiv ℝ (fun z ↦ incidence k (P.toFun z)) z₀
      (EuclideanSpace.single 0 1) ≠ 0)
    {r a ρ τ : ℝ} (hr : 0 < r) (ha : 0 < a) (hρ : 0 < ρ) (hτ : 0 < τ) :
    let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
    let p₀ := augmentedInputCenter T (z₀ := z₀) (k := k)
    let q₀ := frozenAugmentedChart T p₀
    let G := FrozenIncidence.referenceEquiv T hP hz₀ hinc hd
    ∃ r' > (0 : ℝ), r' ≤ r ∧ r' ≤ ρ ∧
    ∃ a' > (0 : ℝ), a' ≤ a ∧ 6 * a' ≤ r' ∧ 4 * a' < ρ ∧
      4 * a' < τ ∧ 4 * a' < 1 / 2 ∧
      (closedBall (spectatorCenter z₀) (3 * r') ×ˢ closedBall (z₀ 0) (3 * r') ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) ∧
    ∃ δ > (0 : ℝ), ∃ cJ > (0 : ℝ), ∃ b > (0 : ℝ),
    ∃ V L : Set (ℝ × Euclidean (n - 1)),
      IsOpen V ∧ IsCompact (closure V) ∧ IsCompact L ∧ L ⊆ V ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        (∀ p ∈ closedBall p₀ ρ,
          ‖(augmentedReferenceEquiv T hP hz₀ hinc hd).symm.toContinuousLinearMap.comp
            (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
        ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
          (physicalParameterSet z₀ (6 * a') ×ˢ dataSet z₀ ηb (3 * r')) ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a'), ∀ u ∈ dataBox z₀ ηb (2 * r'),
          ‖G.symm.toContinuousLinearMap.comp
            (fderiv ℝ (adaptedTransportChart T Q p) u) -
            ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) ∧
        BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a'))
          (dataBox z₀ ηb r') (dataSet z₀ ηb (2 * r')) (dataBox z₀ ηb (2 * r')) V L b cJ G ∧
        (∀ p ∈ physicalParameterSet z₀ (6 * a'),
          ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r' (angularWidth ηb r'),
            ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r' / 4) * ‖u.2‖) ∧
        (∀ x : Variables n, ‖x.2.2‖ = ‖k‖ → ∀ v : Euclidean 2,
          (x, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
            conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) := by
  dsimp only
  let ηb := T.data.adapted.embedding.toContinuousLinearMap.adjoint k
  have hηb : ηb ≠ 0 := FrozenIncidence.tangential_direction_ne_zero T hP hz₀ hk hinc
  obtain ⟨r₀, hr₀, hrr₀, hrρ₀, a₀, ha₀, haa₀, har₀, haρ₀, δ₀, hδ₀, hshell⟩ :=
    exists_refined_supported_shell T hP hz₀ hk hinc hd hr ha hρ hτ
  let cap := min a₀ (min ρ (min τ (1 / 2)))
  have hcap : 0 < cap := lt_min ha₀ (lt_min hρ (lt_min hτ (by norm_num)))
  obtain ⟨r', hr', hrr', a', ha', hacap, har', _, _, hcarrier', δ₁, hδ₁,
    cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, hsmall⟩ :=
    exists_smaller_frozen_conic_inputs T hP hz₀ hk hinc hd hr₀ hcap
  have haa' : a' ≤ a₀ := by linarith [hacap.trans_le (min_le_left a₀ _)]
  have hρ' : 4 * a' < ρ := by
    linarith [hacap.trans_le ((min_le_right a₀ _).trans (min_le_left ρ _))]
  have hτ' : 4 * a' < τ := by
    linarith [hacap.trans_le ((min_le_right a₀ _).trans
      ((min_le_right ρ _).trans (min_le_left τ _)))]
  have hcell : 4 * a' < 1 / 2 := by
    linarith [hacap.trans_le ((min_le_right a₀ _).trans
      ((min_le_right ρ _).trans (min_le_right τ _)))]
  refine ⟨r', hr', hrr'.trans hrr₀, hrr'.trans hrρ₀, a', ha', haa'.trans haa₀,
    har', hρ', hτ', hcell, hcarrier', min δ₀ δ₁, lt_min hδ₀ hδ₁,
    cJ, hcJ, b, hb, V, L, hV, hVc, hLc, hLV, ?_⟩
  intro Q hQ hgap
  obtain ⟨hf, hg, hInv, htrans⟩ := hsmall Q (hQ.trans_le (min_le_right _ _))
  refine ⟨hf, hg, hInv, htrans, ?_⟩
  have hshell' : ∀ q : Variables n × Euclidean 2, ‖q.1.2.2‖ = ‖k‖ →
      q ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') →
      q ∈ closedBall ((0, 0, k), spectatorCenter z₀) τ := by
    intro q hqnorm hq
    have hh := hshell Q (hQ.trans_le (min_le_left _ _)) hgap q.1 hqnorm q.2
      (closure_mono (image_mono (conicMaskSupport_mono z₀ ηb hrr' haa')) hq)
    simpa only [frozenAugmentedChart_center T hP hz₀ hinc] using hh
  intro x hx v hv
  have hratio : 6 * a' ≤ 3 * r' := by linarith
  have hh : (x, v) ∈ closedBall ((0, 0, k), spectatorCenter z₀) τ :=
    frozenConicMaskImage_supported_shell T Q hP hηb hr' ha' hratio
      hcarrier' (k := k) (ℓ := ‖k‖) (τ := τ) hτ'.le hshell' hx hv
  simpa only [frozenAugmentedChart_center T hP hz₀ hinc] using hh

end JanetCartan.ContinuumNormal.FrozenModel
