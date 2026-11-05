module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.CommonFlow

/-!
# Identifying the retained seed scalar by its actual transport equation

The consumer is `exists_constructed_flat_seed_matched_mean`. The unit scalar
already used in its mean is identified with the literal adapted exponential
formula, without replacing it by another existential seed transport
(`app:ch_background:eq:bg-Nsigma`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground
open HamiltonPhase ActualCarriers CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open SourceGeometry ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching

/-- Uniqueness of the literal adapted scalar, using its physical transport
PDE and Cauchy value. The flow and coefficient hypotheses are supplied by
`exists_uniform_actual_flow_chart` and the retained seed minor. Consumer:
`exists_retained_scalar_source_flows` (`app:ch_background:eq:bg-Nsigma`). -/
theorem carrierScalarAmplitude_eq_of_transport
    {n N : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    {I : Set ℝ} {L : Set (Euclidean (n - 1) × Euclidean 3)}
    {D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hI : IsOpen I) (hIc : OrdConnected I) (_hL : IsOpen L) (hD : IsOpen D)
    (h0 : (0 : ℝ) ∈ I)
    {α : Euclidean n × Euclidean 3 → ℝ} {a : ℝ}
    (hα : ContDiffOn ℝ ∞ α (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D))
    (hc : ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col)
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D))
    (hden : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      carrierAdaptedDenominator T Q row col w ≠ 0)
    (hpde : ∀ w ∈ coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D,
      fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
        carrierTransportPotential T Q F row col w * α w = 0)
    (hinit : ∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = a)
    {Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    (hΦ : ContDiffOn ℝ ∞ Φ (I ×ˢ L))
    (hΦD : MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D)
    (hΦ₀ : ∀ p ∈ L, Φ (0, p) = p)
    (hYU : MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L))
    (hΦY : ∀ q ∈ D, Φ (q.1, Y q) = q.2)
    (hvelocity : ∀ p ∈ L, ∀ t ∈ I,
      HasDerivAt (fun s ↦ Φ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q row col
          ((coordinates (adaptedCoordinates T.data.adapted)).symm (t, Φ (t, p))))).2, 0) t) :
    EqOn (carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ a)) α
      (coordinates (adaptedCoordinates T.data.adapted) ⁻¹' D) := by
  let e := adaptedCoordinates T.data.adapted
  let C := coordinates (Z := Euclidean 3) e
  let u := fun q ↦ α (C.symm q)
  let c := fun q ↦ carrierTransportPotential T Q F row col (C.symm q)
  have hu : ContDiffOn ℝ ∞ u D := hα.comp C.symm.contDiff.contDiffOn
    (fun q hq ↦ by change C (C.symm q) ∈ D; simpa only [ContinuousLinearEquiv.apply_symm_apply] using hq)
  have hc' : ContDiffOn ℝ ∞ c D := hc.comp C.symm.contDiff.contDiffOn
    (fun q hq ↦ by change C (C.symm q) ∈ D; simpa only [ContinuousLinearEquiv.apply_symm_apply] using hq)
  have hcf := contDiffOn_flowTransportCoefficient hc' hΦ hΦD
  have hsol := transportFromFootpoint_unique hI hIc
    (fun p hp ↦ hcf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht ↦ ⟨ht, hp⟩)) h0 hYU hΦY
    (u := u) (r := fun _ ↦ a) ?_ ?_
  · intro w hw
    exact (hsol hw).symm.trans (congrArg α (C.symm_apply_apply w))
  · intro p hp t ht
    let q := (t, Φ (t, p))
    let w := C.symm q
    have hq : q ∈ D := hΦD (show (t, p) ∈ I ×ˢ L from ⟨ht, hp⟩)
    have hw : C w ∈ D := by simpa only [w, ContinuousLinearEquiv.apply_symm_apply] using hq
    have hdu := (hu.contDiffAt (hD.mem_nhds hq)).differentiableAt (by simp)
    have hd := hdu.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hvelocity p hp t ht))
    have htime : (e (carrierTransportDirection T Q row col w)).1 = 1 :=
      by simpa [e] using carrierTransportDirection_normal T Q row col w (hden w hw)
    have hchain := directional_derivative_coordinates e
      (u := u) (w := w) (by change DifferentiableAt ℝ u (C (C.symm q)); simpa only [ContinuousLinearEquiv.apply_symm_apply] using hdu)
      (carrierTransportDirection T Q row col w)
    have hs : (∑ j, carrierTransportDirection T Q row col w j *
        partialDeriv (fun x ↦ α (x, w.2)) w.1 j) =
        fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) := by
      simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
        EuclideanSpace.basisFun_apply, partialDeriv, smul_eq_mul] using
        congrArg (fderiv ℝ (fun x ↦ α (x, w.2)) w.1)
          ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (carrierTransportDirection T Q row col w))
    change (∑ j, carrierTransportDirection T Q row col w j *
      partialDeriv (fun x ↦ α (C.symm (C (x, w.2)))) w.1 j) =
      fderiv ℝ u (C w) ((e (carrierTransportDirection T Q row col w)).1,
        (e (carrierTransportDirection T Q row col w)).2, 0) at hchain
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hchain
    rw [hs, htime] at hchain
    have hpde' := hpde w hw
    have he : fderiv ℝ u q (1, (e (carrierTransportDirection T Q row col w)).2, 0) =
        -flowTransportCoefficient c Φ (t, p) * u q := by
      rw [← show C w = q from C.apply_symm_apply q, ← hchain]
      simp only [u, ContinuousLinearEquiv.symm_apply_apply]
      dsimp only [flowTransportCoefficient, c, q, w] at hpde' ⊢
      linarith
    exact he ▸ hd
  · intro p hp
    rw [hΦ₀ p hp]
    change α (e.symm (0, p.1), p.2) = a
    simpa [e] using hinit p hp

/-- Construct common positive-scale adapted flows and identify their literal
exponential scalars with the SAME supplied unit seed scalar. Every current
coefficient, flow and matching assertion is proved. The seed data are the
actual outputs retained by `exists_finite_flat_seed_unit_transports`; the
parent discharges the transverse input using its already chosen seed cap.
The common cylinder precedes the scale and every derivative order
(`app:ch_background:eq:bg-Nsigma`). -/
theorem exists_retained_scalar_source_flows
    {n N : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    (row col : Fin n) {z₀ : Euclidean 3} {r : ℝ} (hr : 0 < r)
    (hpatch : ball ((0 : Euclidean n), z₀) r ⊆ ball 0 T.physicalRadius ×ˢ
      FrozenMenu.parameterCube (2 * P.radius))
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q₀ row col) (ball (0, z₀) r))
    (hk : ContDiffOn ℝ ∞ (carrierNullvector T Q₀ col) (ball (0, z₀) r))
    (hc : ContDiffOn ℝ ∞ (carrierTransportPotential T Q₀ F row col) (ball (0, z₀) r))
    (hden : ∀ w ∈ ball (0, z₀) r, carrierAdaptedDenominator T Q₀ row col w ≠ 0)
    {α : Euclidean n × Euclidean 3 → ℝ}
    (hα : ContDiffOn ℝ ∞ α (ball (0, z₀) r))
    (hpde : ∀ w ∈ ball (0, z₀) r,
      fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q₀ row col w) +
        carrierTransportPotential T Q₀ F row col w * α w = 0)
    (hinit : ∀ p : Euclidean (n - 1) × Euclidean 3,
      (T.data.adapted.embedding p.1, p.2) ∈ ball (0, z₀) r →
      α (T.data.adapted.embedding p.1, p.2) = 1) :
    ∃ R τ : ℝ, 0 < R ∧ 0 < τ ∧
      let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
      let I := Ioo (-τ) τ
      let L := ball ((0 : Euclidean (n - 1)), z₀) (R / 8)
      let W := I ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R / 32)
      ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      ∀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
        Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ) →
        ∃ Dσ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen Dσ ∧ W ⊆ Dσ ∧ C ⁻¹' Dσ ⊆ ball (0, z₀) r ∧
          ContDiffOn ℝ ∞ Φσ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Yσ Dσ ∧
          MapsTo (fun q ↦ (q.1, Φσ q)) (I ×ˢ L) Dσ ∧
          MapsTo (fun q ↦ (q.1, Yσ q)) Dσ (I ×ˢ L) ∧
          (∀ p ∈ L, Φσ (0, p) = p) ∧
          (∀ p ∈ L, ∀ t ∈ I, Yσ (t, Φσ (t, p)) = p) ∧
          (∀ q ∈ Dσ, Φσ (q.1, Yσ q) = q.2) ∧
          (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φσ (s, p))
            ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Qσ row col
              (C.symm (t, Φσ (t, p))))).2, 0) t) ∧
          EqOn (carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ))
            (sourceAmplitude α σ) (C ⁻¹' Dσ) := by
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  obtain ⟨ρ, R, _, hR, hwork, _, hbuffer'⟩ :=
    exists_adapted_coefficient_ball T isOpen_ball z₀ (mem_ball_self (half_pos hr))
  have hbuffer : MapsTo C.symm (closedBall (0, (0, z₀)) R)
      (closedBall (0, z₀) (r / 2)) :=
    fun q hq ↦ ball_subset_closedBall (hwork (hbuffer' hq))
  let K := closedBall ((0 : Euclidean n), z₀) (r / 2)
  let M := 2 * cNorm K 1 (carrierTransportDirection T Q₀ row col)
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (cNorm_nonneg _ _ _)
  have hKr : K ⊆ ball (0, z₀) r := closedBall_subset_ball (half_lt_self hr)
  obtain ⟨_, _, hflow⟩ := exists_uniform_actual_flow_chart T isOpen_ball
    (isCompact_closedBall _ _) hKr hM hR hbuffer
  let τ := existenceTime R (liftedLowBound T M) / 4
  have hτ : 0 < τ := div_pos (existenceTime_pos hR (liftedLowBound_nonneg T hM)) (by norm_num)
  refine ⟨R, τ, hR, hτ, ?_⟩
  dsimp only
  intro σ hσ hσ1 Qσ hscaled
  obtain ⟨hdσ, hlowσ⟩ := current_carrierTransportDirection_uniform_bound T Q₀ Qσ
    hF hrank hphysical hseed htrans row col (half_lt_self hr) hpatch hd hσ hσ1 hscaled
  obtain ⟨Dσ, Φσ, Yσ, _, hDσ, hsmallσ, hbigσ, _, hΦσ, hYσ, hdomainσ, hΦDσ, hYUσ,
    hinitσ, hYΦσ, hΦYσ, _, _, hvelocityσ, _, _, _⟩ := hflow Qσ row col hdσ hlowσ
  have hdomain : C ⁻¹' Dσ ⊆ ball (0, z₀) r := by
    intro w hw
    have hh := hdomainσ hw
    change C.symm (C w) ∈ ball (0, z₀) r at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  let L : (Euclidean n × Euclidean 3) →L[ℝ] (Euclidean n × Euclidean 3) :=
    (σ • ContinuousLinearMap.id ℝ (Euclidean n)).prodMap (ContinuousLinearMap.id ℝ (Euclidean 3))
  have hmaps : MapsTo L (ball (0, z₀) r) (ball (0, z₀) r) := by
    intro w hw
    change (σ • w.1, w.2) ∈ ball (0, z₀) r
    simp only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right] at hw ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    exact ⟨(mul_le_of_le_one_left (norm_nonneg w.1) hσ1).trans_lt hw.1, hw.2⟩
  have hcoeff (w) (hw : w ∈ ball (0, z₀) r) :
      carrierTransportPotential T Qσ (sourceDilation F σ) row col w =
        σ * carrierTransportPotential T Q₀ F row col (L w) := by
    apply current_carrierTransportPotential_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled hflat row col (hpatch hw).1 (hpatch hw).2
    intro j
    exact ((contDiffAt_piLp 2).mp ((hk.contDiffAt (isOpen_ball.mem_nhds (hmaps hw))).comp
      (σ • w.1) (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
  have hcσ : ContDiffOn ℝ ∞ (carrierTransportPotential T Qσ (sourceDilation F σ) row col)
      (ball (0, z₀) r) :=
    ((hc.comp L.contDiff.contDiffOn hmaps).const_smul σ).congr (fun w hw ↦ hcoeff w hw)
  have hdenσ (w) (hw : w ∈ ball (0, z₀) r) : carrierAdaptedDenominator T Qσ row col w ≠ 0 := by
    rw [current_carrierAdaptedDenominator_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled row col (hpatch hw).1 (hpatch hw).2]
    exact hden _ (hmaps hw)
  have hασ : ContDiffOn ℝ ∞ (sourceAmplitude α σ) (ball (0, z₀) r) :=
    (hα.comp L.contDiff.contDiffOn hmaps).const_smul σ
  have hpdeσ (w) (hw : w ∈ ball (0, z₀) r) :
      fderiv ℝ (fun x ↦ sourceAmplitude α σ (x, w.2)) w.1
        (carrierTransportDirection T Qσ row col w) +
      carrierTransportPotential T Qσ (sourceDilation F σ) row col w * sourceAmplitude α σ w = 0 := by
    have hdiff : DifferentiableAt ℝ (fun x ↦ α (x, w.2)) (σ • w.1) :=
      ((hα.contDiffAt (isOpen_ball.mem_nhds (hmaps hw))).comp
      (σ • w.1) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hchain := (hdiff.hasFDerivAt.comp w.1 ((hasFDerivAt_id w.1).const_smul σ)).const_smul σ
    change HasFDerivAt (fun x ↦ sourceAmplitude α σ (x, w.2)) _ w.1 at hchain
    rw [hchain.fderiv, current_carrierTransportDirection_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled row col (hpatch hw).1 (hpatch hw).2, hcoeff w hw]
    have he := hpde (L w) (hmaps hw)
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, sourceAmplitude]
    change σ * (σ * _) + σ * _ * (σ * _) = 0
    dsimp [L] at he ⊢
    simp only [Prod.map, smul_apply, ContinuousLinearMap.id_apply, id_eq] at he ⊢
    linear_combination σ ^ 2 * he
  refine ⟨Dσ, Φσ, Yσ, hDσ, hsmallσ, hdomain, hΦσ, hYσ.mono hbigσ,
    hΦDσ, hYUσ, hinitσ, hYΦσ, hΦYσ, hvelocityσ, ?_⟩
  apply carrierScalarAmplitude_eq_of_transport T Qσ (sourceDilation F σ) row col
    isOpen_Ioo ordConnected_Ioo isOpen_ball hDσ ⟨by linarith, hτ⟩
    (hασ.mono hdomain) (hcσ.mono hdomain) (fun w hw ↦ hdenσ w (hdomain hw))
    (fun w hw ↦ hpdeσ w (hdomain hw)) ?_ hΦσ hΦDσ hinitσ hYUσ hΦYσ hvelocityσ
  intro p hp
  have hpoint := hdomainσ (hΦDσ (show (0, p) ∈ Ioo (-τ) τ ×ˢ
      ball ((0 : Euclidean (n - 1)), z₀) (R / 8) from ⟨⟨by linarith, hτ⟩, hp⟩))
  change C.symm (0, Φσ (0, p)) ∈ ball (0, z₀) r at hpoint
  rw [hinitσ p hp] at hpoint
  have hs : (T.data.adapted.embedding (σ • p.1), p.2) ∈ ball (0, z₀) r := by
    simpa [L, C, coordinates_symm_apply, map_smul] using hmaps hpoint
  exact sourceAmplitude_initial_scalar T.data.adapted.embedding.toContinuousLinearMap
    (hinit (σ • p.1, p.2) hs)

end JanetCartan.NormalizedBackground
