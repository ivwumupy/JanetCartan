module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.RawBounds
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.ParameterSupport
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Carrier

/-!
# Strong adjoint comparison on the original raw carrier space

A compact-frequency comparison is used only inside the proof. The actual
uncut adjoints, carrier measure, angular support and both real quadratures are
unchanged. The existing full raw Sobolev norm controls the discarded frequency
tail. The consumer is the fixed-reference raw inverse comparison in
`app:ch_background:prop:bg-normalized`, not operator-norm continuity of moving
Fourier integral rows (which is not asserted).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumRow RawCutoffBounds RawInputPartition CarrierSobolev
open ContinuumAdjoint.DensityMultiplier ContinuumRow.CarrierNormalRealization

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

variable {n N : ℕ}

/-- Pointwise finite-frequency kernel comparison bounds the literal adjoint
integral at that same frequency. Torus volume remains normalized; the column
membership is supplied by the original kernel's primitive measurable bound. -/
theorem norm_carrierAdjointIntegral_sub_le (d d₀ : CarrierData n N)
    (w : ComplexOutputL2 n) (u : CarrierVariable n)
    (hd : MemLp (fun x ↦ carrierKernel d x u) 2 (volume : Measure (Torus n)))
    (hd₀ : MemLp (fun x ↦ carrierKernel d₀ x u) 2 (volume : Measure (Torus n)))
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ∀ x, ‖carrierKernel d x u - carrierKernel d₀ x u‖ ≤ ε) :
    ‖carrierAdjointIntegral d w u - carrierAdjointIntegral d₀ w u‖ ≤ ε * ‖w‖ := by
  let v := hd.toLp (fun x ↦ carrierKernel d x u)
  let v₀ := hd₀.toLp (fun x ↦ carrierKernel d₀ x u)
  have he : carrierAdjointIntegral d w u - carrierAdjointIntegral d₀ w u =
      inner ℂ (v - v₀) w := by
    rw [inner_sub_left, L2.inner_def, L2.inner_def]
    congr 1
    · apply integral_congr_ae
      filter_upwards [hd.coeFn_toLp] with x hx
      exact congrArg (fun z ↦ inner ℂ z (w x)) hx.symm
    · apply integral_congr_ae
      filter_upwards [hd₀.coeFn_toLp] with x hx
      exact congrArg (fun z ↦ inner ℂ z (w x)) hx.symm
  have hb : ∀ᵐ x ∂(volume : Measure (Torus n)), ‖(v - v₀) x‖ ≤ ε := by
    filter_upwards [Lp.coeFn_sub v v₀, hd.coeFn_toLp, hd₀.coeFn_toLp] with x hs hx hx₀
    rw [hs, Pi.sub_apply, show v x = carrierKernel d x u from hx,
      show v₀ x = carrierKernel d₀ x u from hx₀]
    exact hsmall x
  have hv : ‖v - v₀‖ ≤ ε := by
    simpa [measureUnivNNReal, measure_univ] using Lp.norm_le_of_ae_bound hε hb
  rw [he]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))

/-- The literal volume factor of the compact part used only in the continuity
proof. It is independent of the current history and the datum. -/
def carrierBoxFactor (Z : Set CarrierParameter) (K : ℝ) : ℝ :=
  Real.sqrt ((carrierMeasure n).real (Z ×ˢ closedBall 0 (4 * K)))

/-- The exact same rounded raw multiplier controls the compact-frequency
adjoint difference by primitive kernel closeness. No uncut operator-norm
closeness is used or concluded (`app:ch_background:eq:bg-realification`). -/
theorem norm_roundedCarrier_adjoint_sub_le (d d₀ : CarrierData n N)
    (T T₀ : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hT : ∀ w, T.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w)
    (hT₀ : ∀ w, T₀.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d₀ w)
    (hd : ∀ u, MemLp (fun x ↦ carrierKernel d x u) 2 (volume : Measure (Torus n)))
    (hd₀ : ∀ u, MemLp (fun x ↦ carrierKernel d₀ x u) 2 (volume : Measure (Torus n)))
    {Z : Set CarrierParameter} (hZ : IsCompact Z)
    (hs : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    (hs₀ : ∀ z ∉ Z, ∀ η, d₀.angularCutoff z η = 0)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hsmall : ∀ x u, ‖u.2‖ ≤ 4 * K → ‖carrierKernel d x u - carrierKernel d₀ x u‖ ≤ ε)
    (w : ComplexOutputL2 n) :
    ‖carrierSquaredCutoff (roundedCarrierMask n K) (T.adjoint w - T₀.adjoint w)‖ ≤
      (ε * ‖w‖) * carrierBoxFactor (n := n) Z K := by
  let S : Set (CarrierVariable n) := Z ×ˢ closedBall 0 (4 * K)
  have hS : IsCompact S := hZ.prod (isCompact_closedBall _ _)
  let q : CarrierL2 n := indicatorConstLp 2 hS.measurableSet hS.measure_ne_top (1 : ℂ)
  have hpoint : ∀ᵐ u ∂carrierMeasure n,
      ‖carrierSquaredCutoff (roundedCarrierMask n K) (T.adjoint w - T₀.adjoint w) u‖ ≤
        (ε * ‖w‖) * ‖q u‖ := by
    filter_upwards [carrierSquaredCutoff_coeFn (roundedCarrierMask n K)
        (T.adjoint w - T₀.adjoint w),
      Lp.coeFn_sub (T.adjoint w) (T₀.adjoint w), hT w, hT₀ w,
      roundedCarrierMask_mem n K, roundedCarrierMask_eq_zero (n := n) hK,
      (indicatorConstLp_coeFn (p := 2) (hs := hS.measurableSet)
        (hμs := hS.measure_ne_top) (c := (1 : ℂ)))]
        with u hcut hsub hu hu₀ hm hhigh hq
    rw [hcut, hsub, Pi.sub_apply, hu, hu₀, show q u = S.indicator (fun _ ↦ (1 : ℂ)) u from hq]
    by_cases hz : u.1 ∈ Z
    · by_cases hη : ‖u.2‖ ≤ 4 * K
      · have hin : u ∈ S := ⟨hz, by simpa using hη⟩
        rw [Set.indicator_of_mem hin, norm_one, mul_one, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hm2 : (roundedCarrierMask n K u) ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
        have hint := norm_carrierAdjointIntegral_sub_le d d₀ w u (hd u) (hd₀ u) hε
          (fun x ↦ hsmall x u hη)
        exact (mul_le_mul_of_nonneg_right hm2 (norm_nonneg _)).trans
          (by simpa only [one_mul] using hint)
      · rw [hhigh (le_of_lt (lt_of_not_ge hη))]
        simp only [zero_pow (by decide : 2 ≠ 0), zero_smul, norm_zero]
        positivity
    · rw [carrierAdjointIntegral_eq_zero_outside_parameters d hs w u hz,
        carrierAdjointIntegral_eq_zero_outside_parameters d₀ hs₀ w u hz]
      simp only [sub_self, smul_zero, norm_zero]
      positivity
  have hnorm := Lp.norm_le_mul_norm_of_ae_le_mul hpoint
  have hq : ‖q‖ = carrierBoxFactor (n := n) Z K := by
    simp [q, norm_indicatorConstLp, carrierBoxFactor, S, Real.sqrt_eq_rpow]
  rwa [hq] at hnorm

end JanetCartan.PhysicalInverseContinuity
