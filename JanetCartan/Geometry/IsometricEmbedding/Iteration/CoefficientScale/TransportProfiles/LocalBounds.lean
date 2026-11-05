module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.TransportProfiles.FrozenMinorCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers

/-!
# Transport thresholds before the reference scale

The transport consumer of `main:prop:current-scale` must choose frame tolerances
before the source dilation, whose normal gap can tend to zero. The literal
principal formulas choose these tolerances without immersion budgets or normal
gaps. Only their high constants use those later geometric data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport
open NullTransport.CoefficientBounds

/-- `main:prop:current-scale`, `app:ch_waves:eq:joint-tame`: choose the actual
minor refinement, coefficient domains, frame tolerance and direction C1 bound
BEFORE the geometric low budget and separate gaps. The high estimate then has
reserve five. This ordering permits one source dilation to supply frame
closeness without assuming a gap uniform as that dilation tends to zero. -/
theorem exists_transport_coefficient_bounds_before_geometry_with_frozen_minors {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ μ κ : ℝ, 0 < δ ∧ 0 < μ ∧ 0 < κ ∧
      ∃ V : Fin n → Fin n → Set (Euclidean 3),
        (∀ r c, IsOpen (V r c)) ∧
        parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c ∧
        (∀ z ∈ parameterCube (3 * P.radius / 2), ∀ r c, z ∈ V r c →
          μ ≤ |(cubePencil (P.toFun z)).adjugate r c|) ∧
        ∀ (r c : Fin n) (a : Euclidean n × Euclidean 3) (ρ : ℝ), 0 < ρ →
          MapsTo Prod.fst (closedBall a ρ)
            (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) →
          closedBall a ρ ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            (parameterInterior (3 * P.radius / 2) ∩ V r c) →
          ∃ η B : ℝ, 0 < η ∧ η ≤ δ ∧ 0 < B ∧
          ∀ (C₀ κmet κnormal : ℝ), 0 < κmet → 0 < κnormal →
          ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
            ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
              (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
              cNorm K 4 F ≤ C₀ →
              (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
              (∀ x ∈ K, ∀ w ∈ normalSpace F x,
                κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
              cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
              ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                  (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
              let Q := ⟨projectedStress F,
                contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
              let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
                (parameterInterior (3 * P.radius / 2) ∩ V r c)
              ContDiffOn ℝ ∞ (carrierNullvector T Q c) Ω ∧
              ContDiffOn ℝ ∞ (carrierConullvector T Q r) Ω ∧
              ContDiffOn ℝ ∞ (carrierTransportDirection T Q r c) Ω ∧
              ContDiffOn ℝ ∞ (carrierTransportPotential T Q F r c) Ω ∧
              (∀ w ∈ Ω,
                carrierNullvector T Q c w ≠ 0 ∧ carrierConullvector T Q r w ≠ 0 ∧
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                  (fun j ↦ carrierNullvector T Q c w j) = 0 ∧
                carrierConullvector T Q r w ᵥ*
                  reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
                μ * κ ≤ |carrierAdaptedDenominator T Q r c w| ∧
                carrierAdaptedDenominator T Q r c w ≠ 0 ∧
                |(carrierAdaptedDenominator T Q r c w)⁻¹| ≤ (μ * κ)⁻¹) ∧
              cNorm (closedBall a ρ) 1 (carrierTransportDirection T Q r c) ≤ B ∧
              ∀ m,
                cNorm (closedBall a ρ) m (carrierNullvector T Q c) +
                cNorm (closedBall a ρ) m (carrierConullvector T Q r) +
                cNorm (closedBall a ρ) m (carrierAdaptedDenominator T Q r c) +
                cNorm (closedBall a ρ) m
                  (fun w ↦ (carrierAdaptedDenominator T Q r c w)⁻¹) +
                cNorm (closedBall a ρ) m (carrierTransportDirection T Q r c) +
                cNorm (closedBall a ρ) m (carrierTransportPotential T Q F r c) ≤
                  A m * (1 + cNorm K (m + 5) F) := by
  obtain ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hfrozen, hcoeff⟩ :=
    exists_projected_transport_coefficients_with_frozen_minors (N := N) hn hP T hK hKU hball
  refine ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hfrozen, ?_⟩
  intro r c a ρ hρ hx hwork
  have hc : closedBall a ρ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius) := by
    intro w hw
    exact ⟨(hwork hw).1.1, fun i ↦ ((hwork hw).2.1 i).trans (by linarith [hP.1])⟩
  obtain ⟨δlow, L, hδlow, hL, hlowInput⟩ :=
    exists_actualInput_low_bound T hP a ρ hx (hball.trans hKU) hc
  obtain ⟨B, A, hB, hA, hformula⟩ := exists_principal_formula_bounds
    a hρ T.data.adapted.normal r c hL (mul_pos hμ hκ)
  refine ⟨min δ δlow, B, lt_min hδ hδlow, min_le_left _ _, hB, ?_⟩
  intro C₀ κmet κnormal hκmet hκnormal
  obtain ⟨D, hD, hhigh⟩ := exists_projected_actualInput_bound (N := N)
    T hP a ρ hx hc hK hKU hball C₀ hκmet hκnormal
  obtain ⟨E, hE, hpotential⟩ := exists_projected_potential_bound (N := N)
    T hP a hρ hx hc hK hKU hball C₀ hκmet hκnormal hL (mul_pos hμ hκ) r c
  refine ⟨fun m ↦ A m * (1 + D m) + E m, fun m ↦
    add_pos (mul_pos (hA m) (by have := hD m; linarith)) (hE m), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hclose
  obtain ⟨hlow, hcoeffF⟩ := hcoeff F hF hi hrank (hclose.trans_le (min_le_left _ _))
  refine ⟨hlow, ?_⟩
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V r c)
  have hlocal : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q.1 - fun _ ↦ cubeStress n) < δlow := by
    apply (cNorm_mono_set_of_contDiffAt hball hK _).trans_lt
      (hclose.trans_le (min_le_right _ _))
    intro x hx
    exact ((Q.2.1.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
  have hgap : ∀ w ∈ Ω, μ * κ ≤ |carrierAdaptedDenominator T Q r c w| :=
    fun w hw ↦ ((hcoeffF r c).2.2.2.2 w hw).2.2.2.2.1
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨⟨hKU (hball (hx hw)), (hc hw).1⟩, (hc hw).2⟩
  obtain ⟨hlowDir, hprincipal⟩ := hformula (inputDomain T) (isOpen_inputDomain T) hdom
    (actualInput T Q) (smooth_actualInput T hP Q) (hlowInput Q hlocal)
      (fun w hw ↦ hgap w (hwork hw))
  refine ⟨(hcoeffF r c).1, (hcoeffF r c).2.1, (hcoeffF r c).2.2.1,
    (hcoeffF r c).2.2.2.1, (hcoeffF r c).2.2.2.2, hlowDir, ?_⟩
  intro m
  have hhighm := hhigh F hF hi hrank hlowF hmet hnormal hlow m
  have horder : cNorm K (m + 4) F ≤ cNorm K (m + 5) F := cNorm_mono_order (by omega)
  have hinner : 1 + cNorm (closedBall a ρ) m (actualInput T Q) ≤
      (1 + D m) * (1 + cNorm K (m + 5) F) := by
    have hh := hhighm.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) horder) (hD m).le)
    nlinarith [cNorm_nonneg K (m + 5) F]
  have hprincipal' := (hprincipal m).trans (mul_le_mul_of_nonneg_left hinner (hA m).le)
  have hpot := hpotential F hF hi hrank hlowF hmet hnormal hlow
    (hlowInput Q hlocal) (fun w hw ↦ hgap w (hwork hw)) m
  exact (add_le_add hprincipal' hpot).trans_eq (by ring)


/-- The original reserve-five coefficient endpoint, projected from the same
construction retaining its frozen minor (`main:prop:current-scale`,
`app:ch_waves:eq:joint-tame`). -/
theorem exists_transport_coefficient_bounds_before_geometry {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ μ κ : ℝ, 0 < δ ∧ 0 < μ ∧ 0 < κ ∧
      ∃ V : Fin n → Fin n → Set (Euclidean 3),
        (∀ r c, IsOpen (V r c)) ∧
        parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c ∧
        ∀ (r c : Fin n) (a : Euclidean n × Euclidean 3) (ρ : ℝ), 0 < ρ →
          MapsTo Prod.fst (closedBall a ρ)
            (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) →
          closedBall a ρ ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
            (parameterInterior (3 * P.radius / 2) ∩ V r c) →
          ∃ η B : ℝ, 0 < η ∧ η ≤ δ ∧ 0 < B ∧
          ∀ (C₀ κmet κnormal : ℝ), 0 < κmet → 0 < κnormal →
          ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
            ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
              (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
              cNorm K 4 F ≤ C₀ →
              (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
              (∀ x ∈ K, ∀ w ∈ normalSpace F x,
                κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
              cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
              ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
                  (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
              let Q := ⟨projectedStress F,
                contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
              let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
                (parameterInterior (3 * P.radius / 2) ∩ V r c)
              ContDiffOn ℝ ∞ (carrierNullvector T Q c) Ω ∧
              ContDiffOn ℝ ∞ (carrierConullvector T Q r) Ω ∧
              ContDiffOn ℝ ∞ (carrierTransportDirection T Q r c) Ω ∧
              ContDiffOn ℝ ∞ (carrierTransportPotential T Q F r c) Ω ∧
              (∀ w ∈ Ω,
                carrierNullvector T Q c w ≠ 0 ∧ carrierConullvector T Q r w ≠ 0 ∧
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                  (fun j ↦ carrierNullvector T Q c w j) = 0 ∧
                carrierConullvector T Q r w ᵥ*
                  reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
                μ * κ ≤ |carrierAdaptedDenominator T Q r c w| ∧
                carrierAdaptedDenominator T Q r c w ≠ 0 ∧
                |(carrierAdaptedDenominator T Q r c w)⁻¹| ≤ (μ * κ)⁻¹) ∧
              cNorm (closedBall a ρ) 1 (carrierTransportDirection T Q r c) ≤ B ∧
              ∀ m,
                cNorm (closedBall a ρ) m (carrierNullvector T Q c) +
                cNorm (closedBall a ρ) m (carrierConullvector T Q r) +
                cNorm (closedBall a ρ) m (carrierAdaptedDenominator T Q r c) +
                cNorm (closedBall a ρ) m
                  (fun w ↦ (carrierAdaptedDenominator T Q r c w)⁻¹) +
                cNorm (closedBall a ρ) m (carrierTransportDirection T Q r c) +
                cNorm (closedBall a ρ) m (carrierTransportPotential T Q F r c) ≤
                  A m * (1 + cNorm K (m + 5) F) := by
  obtain ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, _hfrozen, hcoeff⟩ :=
    exists_transport_coefficient_bounds_before_geometry_with_frozen_minors
      (N := N) hn hP T hK hKU hball
  exact ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hcoeff⟩

end JanetCartan.CurrentCoefficientProfiles
