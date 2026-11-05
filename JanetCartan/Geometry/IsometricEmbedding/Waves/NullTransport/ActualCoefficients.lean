module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualGaps
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.NormalizedCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Smoothness

/-!
# Smooth coefficients for the actual projected-frame transport

This instantiates the fixed-minor regularity proofs with the literal projected
stress frame and the same carrier selected by `PatchQuantitativeFamily`.
The time denominator uses the retained adapted normal. Its gap, and hence all
divisions below, are derived from primitive frame closeness, not postulated.
The consumer is the characteristic construction in `app:ch_waves:thm:leading`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace

namespace JanetCartan.NullTransport
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Selected right nullvector for the same actual carrier
(`app:ch_waves:thm:leading`). -/
def carrierNullvector (c : Fin n)
    (w : Euclidean n × Euclidean 3) : Euclidean n :=
  WithLp.toLp 2 (rightNullvector (reducedSymbol (Q.1 w.1)
    (T.carrierGradient Q w.1 w.2)) c)

/-- Selected left nullvector for the same actual carrier
(`app:ch_waves:thm:leading`). -/
def carrierConullvector (r : Fin n)
    (w : Euclidean n × Euclidean 3) : Fin n → ℝ :=
  leftNullvector (reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2)) r

/-- The time denominator for the actual section, with no coordinate rotation
of the projected frame (`app:ch_waves:thm:leading`). -/
def carrierAdaptedDenominator (r c : Fin n) (w : Euclidean n × Euclidean 3) : ℝ :=
  adaptedTimeCoefficient (Q.1 w.1) (T.carrierGradient Q w.1 w.2)
    r c T.data.adapted.normal

/-- The actual principal field divided by the adapted time coefficient
(`app:ch_waves:thm:leading`). -/
def carrierTransportDirection (r c : Fin n) (w : Euclidean n × Euclidean 3) : Euclidean n :=
  WithLp.toLp 2 (fun a ↦
    transportField (Q.1 w.1) (carrierConullvector T Q r w)
      (fun j ↦ carrierNullvector T Q c w j) a / carrierAdaptedDenominator T Q r c w)

/-- The actual normalized zeroth-order coefficient, including the induced
Christoffel terms (`app:ch_waves:thm:leading`). -/
def carrierTransportPotential (F : Euclidean n → Euclidean N) (r c : Fin n)
    (w : Euclidean n × Euclidean 3) : ℝ :=
  (carrierConullvector T Q r w ⬝ᵥ
    reducedOperator F Q.1 (fun x ↦ carrierNullvector T Q c (x, w.2)) w.1) /
      carrierAdaptedDenominator T Q r c w

/-- The constructed normalized direction has adapted time speed one. The
nonzero denominator is supplied by `exists_projected_null_coefficients`, so
the actual flow uses the original orthogonal section
(`app:ch_waves:thm:leading`). -/
theorem carrierTransportDirection_normal (r c : Fin n)
    (w : Euclidean n × Euclidean 3)
    (hd : carrierAdaptedDenominator T Q r c w ≠ 0) :
    ⟪T.data.adapted.normal, carrierTransportDirection T Q r c w⟫_ℝ = 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    carrierTransportDirection, div_mul_eq_mul_div, ← Finset.sum_div]
  convert div_self hd using 2
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The literal reduced vector equation is equivalent to the scalar equation
along the actual adapted direction. All connection terms remain in the named
potential (`app:ch_waves:thm:leading`). The differentiability and denominator
inputs are supplied by `exists_projected_null_coefficients` on its open patch.
-/
theorem carrier_scalar_reduction_iff (F : Euclidean n → Euclidean N)
    (r c : Fin n) {α : Euclidean n → ℝ} {w : Euclidean n × Euclidean 3}
    (hQ : ∀ i, (Q.1 w.1 i).IsSymm) (hα : DifferentiableAt ℝ α w.1)
    (hk : ∀ j, DifferentiableAt ℝ (fun x ↦ carrierNullvector T Q c (x, w.2) j) w.1)
    (hd : carrierAdaptedDenominator T Q r c w ≠ 0) :
    carrierConullvector T Q r w ⬝ᵥ reducedOperator F Q.1
        (fun x ↦ α x • carrierNullvector T Q c (x, w.2)) w.1 = 0 ↔
      fderiv ℝ α w.1 (carrierTransportDirection T Q r c w) +
        carrierTransportPotential T Q F r c w * α w.1 = 0 := by
  have hs : (∑ a, carrierTransportDirection T Q r c w a * partialDeriv α w.1 a) =
      fderiv ℝ α w.1 (carrierTransportDirection T Q r c w) := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, partialDeriv, smul_eq_mul] using
      congrArg (fderiv ℝ α w.1)
        ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (carrierTransportDirection T Q r c w))
  rw [scalar_reduction F Q.1 hQ hα hk, ← hs]
  simp only [carrierTransportDirection, carrierTransportPotential, PiLp.toLp_apply,
    div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]
  exact (div_eq_zero_iff.trans (or_iff_left hd)).symm

/-- Primitive immersion/normal-rank hypotheses and `C⁶` closeness of the
literal projected frame produce smooth, nonvanishing nullvectors, the actual
adapted denominator gap and its reciprocal bound, and smooth normalized
principal and zeroth-order coefficients. The finite refinement and constants
are chosen before the immersion. No coefficient package or transport solution
is assumed (`app:ch_waves:thm:leading`).

The open physical domain is intersected with `interior K`; callers choose a
compact construction ball containing their working ball. The carrier parameter
domain extends to radius `3 * P.radius / 2`, retaining a buffer around the
original closed cube, and is intersected with the selected refinement member.
-/
theorem exists_projected_null_coefficients (hn : 2 ≤ n) {c₀ C₀ : ℝ}
    (hP : P.IsValid c₀ C₀) (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ μ κ : ℝ, 0 < δ ∧ 0 < μ ∧ 0 < κ ∧
      ∃ V : Fin n → Fin n → Set (Euclidean 3),
        (∀ r c, IsOpen (V r c)) ∧
        parameterCube P.radius ⊆ ⋃ r, ⋃ c, V r c ∧
        ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
          (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
          cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
          ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
          ∀ r c,
            let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
              (parameterInterior (3 * P.radius / 2) ∩ V r c)
            ContDiffOn ℝ ∞ (carrierNullvector T Q c) Ω ∧
              ContDiffOn ℝ ∞ (carrierConullvector T Q r) Ω ∧
              ContDiffOn ℝ ∞ (carrierTransportDirection T Q r c) Ω ∧
              ContDiffOn ℝ ∞ (carrierTransportPotential T Q F r c) Ω ∧
              ∀ w ∈ Ω,
                carrierNullvector T Q c w ≠ 0 ∧ carrierConullvector T Q r w ≠ 0 ∧
                reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
                  (fun j ↦ carrierNullvector T Q c w j) = 0 ∧
                carrierConullvector T Q r w ᵥ*
                  reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
                μ * κ ≤ |carrierAdaptedDenominator T Q r c w| ∧
                carrierAdaptedDenominator T Q r c w ≠ 0 ∧
                |(carrierAdaptedDenominator T Q r c w)⁻¹| ≤ (μ * κ)⁻¹ := by
  obtain ⟨δ, μ, κ, hδ, hμ, hκ, V, hV, hcover, hnull⟩ :=
    exists_actual_nullvectors hn hP T hK hKU hball
  refine ⟨min δ T.family.threshold, μ, κ, lt_min hδ T.family.threshold_pos,
    hμ, hκ, V, hV, hcover, ?_⟩
  intro F hF hi hrank hclose
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    apply (cNorm_mono_set_of_contDiffAt hball hK _).trans_lt
      (hclose.trans_le (min_le_right _ _))
    intro x hx
    exact ((hframe.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
  refine ⟨hlow, ?_⟩
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  change ∀ r c, _
  intro r c
  let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V r c)
  have hΩ : IsOpen Ω := (isOpen_ball.inter isOpen_interior).prod
    ((isOpen_parameterInterior _).inter (hV r c))
  have hxU {w : Euclidean n × Euclidean 3} (hw : w ∈ Ω) : w.1 ∈ U :=
    hKU (interior_subset hw.1.2)
  have hzC {w : Euclidean n × Euclidean 3} (hw : w ∈ Ω) :
      w.2 ∈ parameterCube (3 * P.radius / 2) := fun i ↦ (hw.2.1 i).le
  have hs (x) (hx : x ∈ U) (i) : (Q.1 x i).IsSymm :=
    (projectedStress_mem_stressSpace
      ((hF.contDiffAt (hU.mem_nhds hx)).of_le (by simp)) (hrank x hx) i).1
  have hb (w) (hw : w ∈ Ω) := hnull Q (hclose.trans_le (min_le_left _ _)) hs w.1 hw.1.1
    (interior_subset hw.1.2) w.2 (hzC hw) r c hw.2.2
  have hd (w) (hw : w ∈ Ω) : carrierAdaptedDenominator T Q r c w ≠ 0 :=
    (hb w hw).2.2.2.2.2.2.2.1
  have hQ (i j a : Fin n) :
      ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean 3 ↦ Q.1 w.1 i j a) Ω := by
    exact ((Matrix.entryLinearMap ℝ ℝ j a).toContinuousLinearMap.contDiff.comp_contDiffOn
      (contDiffOn_projectedStress hU hF hi hrank i)).comp
        contDiffOn_fst (fun _ hw ↦ hxU hw)
  have hξ : ContDiffOn ℝ ∞
      (fun w : Euclidean n × Euclidean 3 ↦ T.carrierGradient Q w.1 w.2) Ω :=
    (T.carrierGradient_smooth hP Q).mono fun _ hw ↦
      ⟨hw.1.1, fun i ↦ (hw.2.1 i).trans (by linarith [hP.1])⟩
  have hk := contDiffOn_rightNullvector_reducedSymbol hQ hξ c
  have hl := contDiffOn_leftNullvector_reducedSymbol hQ hξ r
  have hke : ContDiffOn ℝ ∞ (carrierNullvector T Q c) Ω :=
    (contDiffOn_piLp 2).mpr (contDiffOn_pi.mp hk)
  have hden : ContDiffOn ℝ ∞ (carrierAdaptedDenominator T Q r c) Ω := by
    unfold carrierAdaptedDenominator adaptedTimeCoefficient
    exact ContDiffOn.sum fun a _ ↦ contDiffOn_const.mul
      (contDiffOn_transportField hQ hl hk a)
  have hdir : ContDiffOn ℝ ∞ (carrierTransportDirection T Q r c) Ω := by
    apply (contDiffOn_piLp 2).mpr
    intro a
    exact (contDiffOn_transportField hQ hl hk a).div hden hd
  have hpot : ContDiffOn ℝ ∞ (carrierTransportPotential T Q F r c) Ω := by
    apply ContDiffOn.div _ hden hd
    exact ContDiffOn.sum fun i _ ↦ (contDiffOn_pi.mp hl i).mul
      (contDiffOn_reducedOperator_joint hΩ
        (hF.comp contDiffOn_fst (fun _ hw ↦ hxU hw))
        (fun _ hw ↦ hi _ (hxU hw)) hQ hke i)
  refine ⟨hke, hl, hdir, hpot, ?_⟩
  intro w hw
  have hh := hb w hw
  refine ⟨?_, hh.2.2.2.1, hh.2.2.2.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2⟩
  intro hkzero
  apply hh.2.2.1
  exact congrArg (fun v : Euclidean n ↦ fun j ↦ v j) hkzero

end JanetCartan.NullTransport
