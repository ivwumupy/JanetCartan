module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.NullFlow

/-!
# Matching the actual scalar, null amplitude and normal coefficient

The input is the pair of actual adapted ODE constructions on common buffers.
Neither a matching identity nor a scalar PDE is assumed. The coefficient
identity, ODE uniqueness and exponential formula prove the normalization in
`app:ch_background:eq:bg-Nsigma` and `paper-v2.tex`, `new:lem:scaling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
open HamiltonPhase NormalizedBackground.SourceGeometry
open ActualCarriers CurrentFullPhase NullTransport NullTransport.ActualFlow
open NullTransport.FlowAmplitude LeadingWave AmbientResponse

variable {n N : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))

include hF hrank hphysical hseed htrans hσ hσ1 hscaled

local notation "Label" => Euclidean (n - 1) × Euclidean 3
local notation "C" => coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)

/-- The actual positive scalar with initial value `σ`, its selected null
amplitude, and the normalized normal coefficient match the seed source
pullbacks. The hypotheses are the ODE, inverse and buffered regularity outputs
of `exists_projected_local_positive_amplitude`, for the SAME fixed minor and
adapted section. The seed flatness is the literal geometric seed equation.
Consumer: `FamilyInputs` primitive normal-coefficient comparison.
Source: `app:ch_background:eq:bg-Nsigma`, `new:lem:scaling`.

This deduction does not supply a uniform instantiation of those flow buffers
for the genuine seed and every positive scale. -/
theorem current_nullAmplitude_source_dilation (row col : Fin n)
    {z₀ : Euclidean 3} {ρ R τ : ℝ} (hR : 0 < R) (hτ : 0 < τ) (hτR : τ ≤ R / 16)
    (hbuffer : MapsTo (C).symm (closedBall (0, (0, z₀)) R) (closedBall (0, z₀) ρ))
    (hreg : ∀ w ∈ closedBall (0, z₀) ρ,
      ContDiffAt ℝ ∞ (carrierTransportDirection T Q₀ row col) w)
    {Φ₀ Φσ : ℝ × Label → Label}
    (hinit₀ : ∀ p ∈ ball (0, z₀) (R / 8), Φ₀ (0, p) = p)
    (hinitσ : ∀ p ∈ ball (0, z₀) (R / 8), Φσ (0, p) = p)
    (hrange₀ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      Φ₀ (t, p) ∈ ball (0, z₀) (R / 4))
    (hrangeσ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      Φσ (t, p) ∈ ball (0, z₀) (R / 4))
    (hpatchσ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      (C).symm (t, Φσ (t, p)) ∈ ball 0 T.physicalRadius ×ˢ
        FrozenMenu.parameterCube (2 * P.radius))
    (hvelocity₀ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φ₀ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q₀ row col
          ((C).symm (t, Φ₀ (t, p))))).2, 0) t)
    (hvelocityσ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s ↦ Φσ (s, p))
        ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Qσ row col
          ((C).symm (t, Φσ (t, p))))).2, 0) t)
    (hflat : ∀ y ∈ U, inducedMetric F y = 1)
    (hkernel : ∀ w ∈ closedBall (0, z₀) ρ, ContDiffAt ℝ ∞ (carrierNullvector T Q₀ col) w)
    {Y₀ Yσ : ℝ × Label → Label} {Dσ : Set (ℝ × Label)}
    (hYU : MapsTo (fun q ↦ (q.1, Yσ q)) Dσ (Ioo (-τ) τ ×ˢ ball (0, z₀) (R / 8)))
    (hYΦ : ∀ p ∈ ball (0, z₀) (R / 8), ∀ t ∈ Ioo (-τ) τ, Y₀ (t, Φ₀ (t, p)) = p)
    (hΦY : ∀ q ∈ Dσ, Φσ (q.1, Yσ q) = q.2) :
    let α₀ := carrierScalarAmplitude T Q₀ F row col Φ₀ Y₀ (fun _ ↦ 1)
    let ασ := carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ)
    let b₀ := fun w ↦ α₀ w • carrierNullvector T Q₀ col w
    let bσ := fun w ↦ ασ w • carrierNullvector T Qσ col w
    EqOn ασ (sourceAmplitude α₀ σ) (C ⁻¹' Dσ) ∧
    EqOn bσ (sourceAmplitude b₀ σ) (C ⁻¹' Dσ) ∧
    ∀ (measurement : Euclidean n → ℝ)
      (angular : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
      (p : Euclidean n × (ℝ × Euclidean 2)),
      C (p.1, ContinuumRow.CanonicalCarrier.parameter p.2) ∈ Dσ →
      (normalizedSourceCoefficients F
        (fun q ↦ T.carrierGradient Q₀ q.1 (ContinuumRow.CanonicalCarrier.parameter q.2))
        (fun q ↦ b₀ (q.1, ContinuumRow.CanonicalCarrier.parameter q.2))
        measurement angular high σ).normal p =
      principalNormal (canonicalNormalCompletion (sourceDilation F σ) p.1)
        (T.carrierGradient Qσ p.1 (ContinuumRow.CanonicalCarrier.parameter p.2))
        (bσ (p.1, ContinuumRow.CanonicalCarrier.parameter p.2)) := by
  dsimp only
  obtain ⟨hflow, hfoot⟩ := current_nullFlow_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled row col hR hτ hτR hbuffer hreg
    hinit₀ hinitσ hrange₀ hrangeσ hpatchσ hvelocity₀ hvelocityσ
  have hY := hfoot Y₀ Yσ Dσ hYU hYΦ hΦY
  let α₀ := carrierScalarAmplitude T Q₀ F row col Φ₀ Y₀ (fun _ ↦ 1)
  let ασ := carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ)
  let b₀ := fun w ↦ α₀ w • carrierNullvector T Q₀ col w
  let bσ := fun w ↦ ασ w • carrierNullvector T Qσ col w
  have hpatch (w : Euclidean n × Euclidean 3) (hw : C w ∈ Dσ) :
      w ∈ ball 0 T.physicalRadius ×ˢ FrozenMenu.parameterCube (2 * P.radius) := by
    have hp := hYU hw
    have hh := hpatchσ _ hp.2 _ hp.1
    rw [hΦY _ hw, (C).symm_apply_apply] at hh
    exact hh
  have hnorm (x : Euclidean (n - 1)) : ‖σ • x‖ ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    exact mul_le_of_le_one_left (norm_nonneg x) hσ1
  have hscalar : EqOn ασ (sourceAmplitude α₀ σ) (C ⁻¹' Dσ) := by
    intro w hw
    let q := C w
    have hq : q ∈ Dσ := hw
    have hp := hYU hq
    let c₀ := fun v ↦ carrierTransportPotential T Q₀ F row col ((C).symm v)
    let cσ := fun v ↦ carrierTransportPotential T Qσ (sourceDilation F σ) row col ((C).symm v)
    have hy := congrArg (transportLabelDilation σ) (hY hq)
    simp only [sourceTransportFlow, transportLabelDilation_inv hσ.ne'] at hy
    have he : EqOn
        (fun s ↦ flowTransportCoefficient cσ Φσ (s, Yσ q))
        (fun s ↦ σ * flowTransportCoefficient c₀ Φ₀
          (σ * s, Y₀ (transportCoordinateDilation σ q))) (uIcc 0 q.1) := by
      intro s hs
      have hsI : s ∈ Ioo (-τ) τ :=
        ordConnected_Ioo.uIcc_subset (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨by linarith, hτ⟩) hp.1 hs
      have hps := hpatchσ _ hp.2 s hsI
      have hr := hrangeσ _ hp.2 s hsI
      have hcoord : transportCoordinateDilation σ (s, Φσ (s, Yσ q)) ∈
          closedBall (0, (0, z₀)) R := by
        simp only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right] at hr
        simp only [transportCoordinateDilation, transportLabelDilation, mem_closedBall,
          Prod.dist_eq, max_le_iff, dist_zero_right]
        refine ⟨?_, (hnorm _).trans (hr.1.le.trans ?_), hr.2.le.trans ?_⟩
        · rw [Real.norm_eq_abs, abs_mul, abs_of_pos hσ]
          exact (mul_le_of_le_one_left (abs_nonneg s) hσ1).trans
            ((abs_lt.mpr hsI).le.trans (hτR.trans (by linarith [hR])))
        all_goals linarith [hR]
      have hkpoint := hbuffer hcoord
      rw [coordinates_symm_source_dilation] at hkpoint
      have hk (j : Fin n) : DifferentiableAt ℝ
          (fun y ↦ carrierNullvector T Q₀ col (y, ((C).symm (s, Φσ (s, Yσ q))).2) j)
          (σ • ((C).symm (s, Φσ (s, Yσ q))).1) :=
        ((contDiffAt_piLp 2).mp ((hkernel _ hkpoint).comp
          (σ • ((C).symm (s, Φσ (s, Yσ q))).1)
          (contDiffAt_id.prodMk contDiffAt_const)) j).differentiableAt (by simp)
      have hcoeff := current_carrierTransportPotential_source_dilation T Q₀ Qσ hF hrank
        hphysical hseed htrans hσ hσ1 hscaled hflat row col hps.1 hps.2 hk
      have hpath := congrArg (transportLabelDilation σ) (hflow (show
        (s, Yσ q) ∈ Ioo (-τ) τ ×ˢ ball (0, z₀) (R / 8) from ⟨hsI, hp.2⟩))
      simp only [sourceTransportFlow, transportLabelDilation_inv hσ.ne'] at hpath
      change transportLabelDilation σ (Φσ (s, Yσ q)) =
        Φ₀ (σ * s, transportLabelDilation σ (Yσ q)) at hpath
      rw [hy] at hpath
      change carrierTransportPotential T Qσ (sourceDilation F σ) row col
        ((C).symm (s, Φσ (s, Yσ q))) = _
      rw [hcoeff, ← coordinates_symm_source_dilation]
      change σ * c₀ (σ * s, transportLabelDilation σ (Φσ (s, Yσ q))) = _
      rw [hpath]
      rfl
    have hi := intervalIntegral.integral_congr (μ := MeasureTheory.volume) he
    have hformula : ασ w = scalarTransport
        (fun s ↦ σ * flowTransportCoefficient c₀ Φ₀
          (σ * s, Y₀ (transportCoordinateDilation σ q))) 0 σ q.1 := by
      change transportFromFootpoint (flowTransportCoefficient cσ Φσ) 0 (fun _ ↦ σ) Yσ q = _
      simp only [transportFromFootpoint, characteristicTransport, scalarTransport, transportFactor, hi]
    rw [hformula, scalarTransport_source_time
      (fun s ↦ flowTransportCoefficient c₀ Φ₀ (s, Y₀ (transportCoordinateDilation σ q))) σ q.1]
    simp only [sourceAmplitude, smul_eq_mul, α₀, carrierScalarAmplitude,
      coordinates_source_dilation, transportFromFootpoint, characteristicTransport, q, c₀]
    rfl
  have hnull : EqOn bσ (sourceAmplitude b₀ σ) (C ⁻¹' Dσ) := by
    intro w hw
    have hp := hpatch w hw
    rw [sourceAmplitude_smul]
    change ασ w • carrierNullvector T Qσ col w = _
    rw [hscalar hw, current_carrierNullvector_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled col hp.1 hp.2]
  refine ⟨hscalar, hnull, ?_⟩
  intro measurement angular high p hp
  have hw := hpatch (p.1, ContinuumRow.CanonicalCarrier.parameter p.2) hp
  have hsx := (convex_ball (0 : Euclidean n) T.physicalRadius).smul_mem_of_zero_mem
    (mem_ball_self T.physicalRadius_pos) hw.1 ⟨hσ.le, hσ1⟩
  have hxU := (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
    (T.target_contains_closed hsx hw.2)).1
  have hn := (normalizedSourceCoefficients_eq_sourceDilation hF
    (fun q ↦ T.carrierGradient Q₀ q.1 (ContinuumRow.CanonicalCarrier.parameter q.2))
    (fun q ↦ b₀ (q.1, ContinuumRow.CanonicalCarrier.parameter q.2))
    measurement angular high hσ p (hrank _ hxU)).1
  rw [hn, current_carrierGradient_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled hw.1 hw.2]
  exact congrArg _ (hnull hp).symm

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching
