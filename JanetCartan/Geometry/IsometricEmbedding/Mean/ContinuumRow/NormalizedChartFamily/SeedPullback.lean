module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.RetainedLift
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.UniformDirection

/-!
# Actual source charts from the same seed coefficients

The source coefficients are the literal seed pullbacks. A sharp contraction
estimate retains the original direction bound, and hence the original ODE
radius and existence time. All flow fields are constructed from these actual
coefficients. No coefficient factory or source chart is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius Topology

namespace JanetCartan.ContinuumRow.NormalizedChartFamily
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference.FlowConstruction NormalizedBackground.SourceGeometry

/-- The actual retained coefficient domain is invariant under physical source
contraction. The parameter set, hence the selected minor patch, stays fixed.
This discharges the geometric domain premise of the source chart constructor
on the original product domains (`app:ch_background:eq:bg-Nsigma`,
`app:ch_waves:thm:leading`). -/
theorem retained_coefficient_domain_mapsTo_source_contraction
    {n : ℕ} {a b σ : ℝ} (ha : 0 < a) (hb : 0 < b) (hσ : σ ∈ Icc (0 : ℝ) 1)
    (V : Set (Euclidean 3)) :
    MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2))
      ((ball (0 : Euclidean n) a ∩ interior (closedBall 0 b)) ×ˢ V)
      ((ball (0 : Euclidean n) a ∩ interior (closedBall 0 b)) ×ˢ V) := by
  intro w hw
  exact ⟨⟨(convex_ball _ _).smul_mem_of_zero_mem (mem_ball_self ha) hw.1.1 hσ,
    (convex_closedBall (0 : Euclidean n) b).interior.smul_mem_of_zero_mem
      (ball_subset_interior_closedBall (mem_ball_self hb)) hw.1.2 hσ⟩, hw.2⟩

/-- Summing the individual derivative suprema preserves the original low
bound under a linear contraction. This avoids enlarging the retained `B` in
the source chart construction (`app:ch_background:eq:bg-Nsigma`). -/
private theorem cNorm_comp_contraction_le_same_sum
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f Ω) (hmap : MapsTo L K K) (m : ℕ) :
    cNorm K m (f ∘ L) ≤ cNorm K m f := by
  let A : ℕ → ℝ := fun j ↦ sSup ((fun x ↦ ‖iteratedFDeriv ℝ j f x‖) '' K)
  have hA (j) : 0 ≤ A j := sSup_norm_iteratedFDeriv_nonneg K j f
  apply (cNorm_le_sum_of_bounds (C := A) (fun j _ ↦ hA j) ?_).trans_eq
  · rfl
  · intro j hj x hx
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le L hΩ hf
      (hKΩ (hmap hx)) j).trans
    apply (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hL) (norm_nonneg _)).trans
    rw [mul_one]
    exact le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hK
      (fun y hy ↦ (hf.contDiffAt (hΩ.mem_nhds (hKΩ hy))).of_le (by simp)) hj)
      (mem_image_of_mem _ (hmap hx))

/-- Construct a source chart on the supplied seed's exact cell, minor,
coefficient domain, radius, bound and time. The only domain condition beyond
the original buffers is invariance of the coefficient domain under this
physical contraction; the retained product domains have this property.
Every current coefficient and its bound is proved by the literal source
identities, and the actual smooth lift supplies the new maps. In particular
the original `B` is not replaced by twice its value. Consumer:
`exists_finite_source_charts_with_lifts`
(`app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`,
`app:ch_waves:thm:leading`). -/
theorem exists_source_chart_with_lift_from_seed
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc B τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hΩU : ∀ w ∈ Ω, w.1 ∈ U)
    (hRc : 0 < Rc) (hB : 0 ≤ B)
    (hτ : τ = existenceTime Rc (liftedLowBound T B) / 4)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    (seed : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hΩscale : MapsTo (fun w : Euclidean n × Euclidean 3 ↦ (σ • w.1, w.2)) Ω Ω)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (hQ : Q.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ)) :
    ∃ current : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc B τ row col (sourceDilation F σ),
    ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
        ℝ × (Euclidean (n - 1) × Euclidean 3),
      current.Q = Q ∧
      ODE.IsSmoothFlowOn (liftedDirection T current.Q row col)
        (0, ((0 : Euclidean (n - 1)), zCell)) Rc (Rc / 2)
        (existenceTime Rc (liftedLowBound T B)) Ψ ∧
      current.forward = forwardFromLift Ψ ∧ current.inverse = footpointFromLift Ψ := by
  let L : (Euclidean n × Euclidean 3) →L[ℝ] (Euclidean n × Euclidean 3) :=
    (σ • ContinuousLinearMap.id ℝ (Euclidean n)).prodMap
      (ContinuousLinearMap.id ℝ (Euclidean 3))
  have hLapply (w) : L w = (σ • w.1, w.2) := rfl
  have hnorm (x : Euclidean n) : ‖σ • x‖ ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    exact mul_le_of_le_one_left (norm_nonneg _) hσ1
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    change max ‖σ • w.1‖ ‖w.2‖ ≤ 1 * max ‖w.1‖ ‖w.2‖
    simpa only [one_mul] using max_le_max (hnorm _) le_rfl
  have hLK : MapsTo L (closedBall ((0 : Euclidean n), zCell) ρ)
      (closedBall ((0 : Euclidean n), zCell) ρ) := by
    intro w hw
    change (σ • w.1, w.2) ∈ closedBall (0, zCell) ρ
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff, dist_zero_right] at hw ⊢
    exact ⟨(hnorm _).trans hw.1, hw.2⟩
  have hLΩ : MapsTo L Ω Ω := hΩscale
  have hk : EqOn (carrierNullvector T Q col) (carrierNullvector T seed.Q col ∘ L) Ω := by
    intro w hw
    exact SourceMatching.current_carrierNullvector_source_dilation T seed.Q Q hF hrank
      hphysical seed.frame_eq htrans hσ hσ1 hQ col (hpatch hw).1 (hpatch hw).2
  have hl : EqOn (carrierConullvector T Q row) (carrierConullvector T seed.Q row ∘ L) Ω := by
    intro w hw
    exact SourceMatching.current_carrierConullvector_source_dilation T seed.Q Q hF hrank
      hphysical seed.frame_eq htrans hσ hσ1 hQ row (hpatch hw).1 (hpatch hw).2
  have hd : EqOn (carrierTransportDirection T Q row col)
      (carrierTransportDirection T seed.Q row col ∘ L) Ω := by
    intro w hw
    exact SourceMatching.current_carrierTransportDirection_source_dilation T seed.Q Q hF hrank
      hphysical seed.frame_eq htrans hσ hσ1 hQ row col (hpatch hw).1 (hpatch hw).2
  have hc : EqOn (carrierTransportPotential T Q (sourceDilation F σ) row col)
      (fun w ↦ σ * carrierTransportPotential T seed.Q F row col (L w)) Ω := by
    intro w hw
    apply SourceMatching.current_carrierTransportPotential_source_dilation T seed.Q Q hF hrank
      hphysical seed.frame_eq htrans hσ hσ1 hQ hflat row col (hpatch hw).1 (hpatch hw).2
    intro j
    exact ((contDiffAt_piLp 2).1
      ((seed.null_smooth.contDiffAt (hΩ.mem_nhds (hLΩ hw))).comp (σ • w.1)
        (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
  have hks := (seed.null_smooth.comp L.contDiff.contDiffOn hLΩ).congr hk
  have hls := (seed.conull_smooth.comp L.contDiff.contDiffOn hLΩ).congr hl
  have hds := (seed.direction_smooth.comp L.contDiff.contDiffOn hLΩ).congr hd
  have hcs := (contDiffOn_const.mul
    (seed.potential_smooth.comp L.contDiff.contDiffOn hLΩ)).congr hc
  have hdir : cNorm (closedBall ((0 : Euclidean n), zCell) ρ) 1
      (carrierTransportDirection T Q row col) ≤ B := by
    have heq : cNorm (closedBall ((0 : Euclidean n), zCell) ρ) 1
        (carrierTransportDirection T Q row col) =
        cNorm (closedBall ((0 : Euclidean n), zCell) ρ) 1
          (carrierTransportDirection T seed.Q row col ∘ L) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq
      intro w hw
      exact eventuallyEq_of_mem (hΩ.mem_nhds (hKΩ hw)) (fun v hv ↦ hd hv)
    rw [heq]
    exact (cNorm_comp_contraction_le_same_sum L hL (isCompact_closedBall _ _) hΩ hKΩ
      seed.direction_smooth hLK 1).trans seed.direction_bound
  have hframe (w) (hw : w ∈ Ω) : Q.1 w.1 = seed.Q.1 (σ • w.1) := by
    rw [hQ, seed.frame_eq]
    exact funext (ProjectedStressFrame.projectedStress_sourceDilation hσ hF w.1
      (hrank _ (hΩU _ (hLΩ hw))))
  have hsymm (w) (hw : w ∈ Ω) (j) : (Q.1 w.1 j).IsSymm := by
    rw [hframe w hw]
    exact seed.symm _ (hLΩ hw) j
  have hnull (w) (hw : w ∈ Ω) := seed.null_spec _ (hLΩ hw)
  have hnull' : ∀ w ∈ Ω,
      carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
      reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
        (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
      carrierConullvector T Q row w ᵥ* reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
      carrierAdaptedDenominator T Q row col w ≠ 0 := by
    intro w hw
    have hgrad := SourceMatching.current_carrierGradient_source_dilation T seed.Q Q hF hrank
      hphysical seed.frame_eq htrans hσ hσ1 hQ (hpatch hw).1 (hpatch hw).2
    have hden := SourceMatching.current_carrierAdaptedDenominator_source_dilation T seed.Q Q hF hrank
      hphysical seed.frame_eq htrans hσ hσ1 hQ row col (hpatch hw).1 (hpatch hw).2
    simpa only [hk hw, hl hw, hframe w hw, hgrad, hden, Function.comp_apply,
      hLapply] using hnull w hw
  subst τ
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  obtain ⟨Ψ, hΨ, D, hD, hsmall, hbig, himage, hcoeff, hφ, hy, hφD, hyD,
    hi, hyφ, hφy, hφz, hyz, hode, hφwide, hywide⟩ :=
    exists_buffered_chart_with_lift (hΩ.preimage C.symm.continuous)
      (fun q hq ↦ hKΩ (hbuffer hq)) (contDiffOn_liftedDirection T Q row col hds)
      hRc (liftedLowBound_nonneg T hB)
      (fun q hq ↦ liftedDirection_low_bounds T Q row col hΩ hds (isCompact_closedBall _ _)
        hKΩ hB hdir (hbuffer hq)) (fun _ ↦ rfl) (fun _ ↦ rfl)
  let current : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc B
      (existenceTime Rc (liftedLowBound T B) / 4) row col (sourceDilation F σ) :=
    ⟨Q, hQ, hks, hls, hds, hcs, hdir, hsymm, hnull', D,
      forwardFromLift Ψ, footpointFromLift Ψ, himage, hD, hsmall, hbig, hcoeff,
      hφ, hy, hφD, hyD, hi, hyφ, hφy, hφz, hyz, hode, hφwide, hywide⟩
  exact ⟨current, Ψ, rfl, hΨ, rfl, rfl⟩

end JanetCartan.ContinuumRow.NormalizedChartFamily
