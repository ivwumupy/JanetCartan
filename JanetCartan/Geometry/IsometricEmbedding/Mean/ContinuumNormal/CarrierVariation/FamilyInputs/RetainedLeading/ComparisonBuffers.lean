module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.PrimitiveComparison

/-!
# Complete supported buffers for the same retained comparison chart

These caps precede source budgets, scalar choices and finite orders. They put
the complete closed mask support in the comparison cylinder, the coefficient
ball and the ORIGINAL scalar domain. Consumer: the direct retained-leading
producer and its primitive comparison (`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier PositiveReference PositiveReference.FlowConstruction
open ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.PhaseExtension

/-- A cap for the complete supported chart, fixed before all source/scalar
budgets. It uses the exact adapted buffer and time bound returned with the
retained maps. In particular no inclusion between `Rc` and `R` is assumed
(`app:ch_background:prop:bg-frame`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_supported_originalScalar_comparison_buffers
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)} (z₀ : Euclidean 3)
    {R Rc B τ Mc : ℝ} (hR : 0 < R) (hRc : 0 < Rc) (hτ : 0 < τ)
    (hMc : 0 < Mc) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc) K) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ}, 0 < a → a < cap →
      MapsTo (densityCoordinates T) (supportedChart z₀ (2 * a))
        (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ) ∧
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
        (supportedChart z₀ (2 * a)) K ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (c : Chart T Ω K ((0 : Euclidean (n - 1)), z₀) Rc B τ row col F),
      cNorm (Icc (-τ) τ ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀) (Rc / 8))
        1 c.forward ≤ Mc →
      MapsTo (densityFootpoint T c.inverse) (supportedChart z₀ (2 * a))
        (ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) := by
  obtain ⟨capI, hcapI, hi⟩ :=
    ContinuumAdjoint.Canonical.RetainedLeading.exists_supportedChart_initialBuffer_before_budgets
      T z₀ hR hRc hτ hMc
  obtain ⟨capO, hcapO, ho⟩ := exists_supportedChart_flowCylinder_cap T z₀
    (half_pos hτ) (half_pos hRc)
  refine ⟨min capI capO / 2, by positivity, ?_⟩
  intro a ha hacap
  have haI : 2 * a < capI := by have := min_le_left capI capO; linarith
  have haO : 2 * a < capO := by have := min_le_right capI capO; linarith
  have hflow : MapsTo (densityCoordinates T) (supportedChart z₀ (2 * a))
      (outputCylinder ((0 : Euclidean (n - 1)), z₀) Rc τ) := by
    intro p hp
    have hh := ho (by positivity : 0 < 2 * a) haO hp
    change densityCoordinates T p ∈ Ioo (-(τ / 2)) (τ / 2) ×ˢ
      ball ((0 : Euclidean (n - 1)), z₀) (Rc / 2 / 32) at hh
    refine ⟨Ioo_subset_Icc_self hh.1, ball_subset_closedBall ?_⟩
    simpa only [div_div, show (2 : ℝ) * 32 = 64 by norm_num] using hh.2
  refine ⟨hflow, ?_, ?_⟩
  · intro p hp
    have hh := hflow hp
    have ht : dist (densityCoordinates T p).1 0 ≤ Rc := by
      rw [Real.dist_eq, sub_zero, abs_le]
      constructor <;> linarith [hh.1.1, hh.1.2]
    have hy : dist (densityCoordinates T p).2 ((0 : Euclidean (n - 1)), z₀) ≤ Rc :=
      (mem_closedBall.mp hh.2).trans (by linarith)
    have hmem : densityCoordinates T p ∈
        closedBall (0, ((0 : Euclidean (n - 1)), z₀)) Rc := by
      rw [mem_closedBall, Prod.dist_eq]
      exact max_le ht hy
    have hb := hbuffer hmem
    change (coordinates (adaptedCoordinates T.data.adapted)).symm
      (coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) ∈ K at hb
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hb
  · intro F row col c hflowBound
    exact (hi (by positivity : 0 < 2 * a) haI c.D c.forward c.inverse c.small_subset
      c.inverse_range c.initial c.forward_inverse c.forward_buffer_smooth hflowBound).2

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
