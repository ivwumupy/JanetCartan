module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.RootGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PrimaryCoordinates

/-!
# Primary-root matching for the retained coefficient branch

The root exported with the actual amplitudes is anchored and smooth on its
original coefficient buffer. Its positive minor and transport gaps imply
scalar transversality. Local implicit-function uniqueness then identifies
every nearby characteristic covector with this SAME branch. No independent
root or flow is selected. The neighborhood precedes the varying coefficient
field and primary parameters.

Consumer: retained primary critical geometry in
`app:ch_response:eq:response-exact-phase` and
`app:ch_response:eq:direct-envelope-profile`. This local connection does not
assert whole-patch coverage, evolution compatibility or an envelope estimate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.RetainedFactors
open ActualCarriers RegularSector.Characteristic RootFamily AlgebraicChart
open CompatibleResponse

variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Coeff" => Fin (d + 1) → MetricTensor (d + 1)

/-- The retained transport gap is the nonzero derivative needed for scalar
root uniqueness, in the original coordinate direction
(`app:ch_response:eq:response-exact-phase`). -/
theorem retained_root_transverse
    {i r c : Fin (d + 1)} {A₀ : Coeff} {ξ : E}
    {H : Coeff × Euclidean d → ℝ} {ε L μ ν : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i r c A₀ ξ H ε L μ ν) :
    fderiv ℝ (determinant A₀) ξ ((coordinateSplit i).symm (1, 0)) ≠ 0 := by
  let e := coordinateSplit i
  have hdata := hH.2 (A₀, (e ξ).2)
    ⟨mem_closedBall_self hε.le, mem_closedBall_self (le_min hε.le hL.le)⟩
  have he : coefficientRootPencil e H (A₀, (e ξ).2) = pencil A₀ ξ := by
    change pencil A₀ (e.symm (H (A₀, (e ξ).2), (e ξ).2)) = _
    rw [show H (A₀, (e ξ).2) = (e ξ).1 from hH.1]
    simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  rw [he] at hdata
  have hm : (pencil A₀ ξ).adjugate r c ≠ 0 :=
    abs_pos.mp (hμ.trans_le hdata.2.2.1)
  have ht : minorTransportCoefficient (pencil A₀ ξ) (pencil A₀ (e.symm (1, 0))) r c ≠ 0 :=
    abs_pos.mp (hν.trans_le hdata.2.2.2)
  have hid : (pencil A₀ ξ).adjugate r c *
      fderiv ℝ Matrix.det (pencil A₀ ξ) (pencil A₀ (e.symm (1, 0))) =
        minorTransportCoefficient (pencil A₀ ξ) (pencil A₀ (e.symm (1, 0))) r c :=
    NullTransport.minor_mul_fderiv_det hdata.2.1 hm _
  have hd : fderiv ℝ Matrix.det (pencil A₀ ξ) (pencil A₀ (e.symm (1, 0))) ≠ 0 := by
    intro hz
    apply ht
    rw [← hid, hz, mul_zero]
  rw [(hasFDerivAt_determinant A₀ ξ).fderiv]
  exact hd

/-- On one open coefficient/covector neighborhood of the frozen point,
the actual retained root is the unique characteristic root. This neighborhood
is chosen before histories, primary labels and masks. The only root input is
the `RootBuffer` constructed by `UniformAmplitudes.ConicConstruction`; the
matching equation and uniqueness are conclusions
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_retained_root_characteristic_neighborhood
    {i r c : Fin (d + 1)} {A₀ : Coeff} {ξ : E} (hξ : ξ ≠ 0)
    {H : Coeff × Euclidean d → ℝ} {ε L μ ν : ℝ}
    (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i r c A₀ ξ H ε L μ ν) :
    ∃ V : Set (Coeff × E), IsOpen V ∧ (A₀, ξ) ∈ V ∧
      ∀ p ∈ V, p.2 ≠ 0 ∧
        (p.1, (coordinateSplit i p.2).2) ∈
          ball A₀ ε ×ˢ ball (coordinateSplit i ξ).2 (min ε L) ∧
        (determinant p.1 p.2 = 0 ↔ H (p.1, (coordinateSplit i p.2).2) =
          (coordinateSplit i p.2).1) := by
  let e := coordinateSplit i
  let p₀ : Coeff × Euclidean d := (A₀, (e ξ).2)
  let z₀ : (Coeff × Euclidean d) × ℝ := (p₀, (e ξ).1)
  have hbase : H p₀ = (e ξ).1 := hH.1
  have hdata := hH.2 p₀
    ⟨mem_closedBall_self hε.le, mem_closedBall_self (le_min hε.le hL.le)⟩
  have hdet : determinant A₀ ξ = 0 := by
    have he := hdata.2.1
    change determinant A₀ (e.symm (H p₀, (e ξ).2)) = 0 at he
    simpa only [hbase, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using he
  have hf : ContDiffAt ℝ ∞ (coefficientSymbol e) z₀ :=
    contDiffAt_coefficientSymbol e (by simpa only [z₀, p₀, Prod.mk.eta,
      ContinuousLinearEquiv.symm_apply_apply] using hξ)
  have hf₀ : coefficientSymbol e z₀ = 0 := by
    simp only [coefficientSymbol, z₀, p₀, Prod.mk.eta,
      ContinuousLinearEquiv.symm_apply_apply, hdet, zero_mul]
  have hd : CharacteristicRoot.scalarDerivative (coefficientSymbol e) z₀ ≠ 0 := by
    rw [(CharacteristicRoot.hasDerivAt_scalar (hf.differentiableAt (by simp))).unique
      (hasDerivAt_coefficientSymbol e A₀ (e ξ).2 (e ξ).1
        (by simpa using hξ) (by simpa using hdet))]
    simpa only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using
      mul_ne_zero (determinantNormalization_pos hξ).ne'
        (retained_root_transverse hε hL hμ hν hH)
  have hu := CharacteristicRoot.localRoot_eventually_unique hf hd hf₀
  let proj : Coeff × E → Coeff × Euclidean d := fun p ↦ (p.1, (e p.2).2)
  have hp : ContinuousAt proj (A₀, ξ) :=
    continuousAt_fst.prodMk (e.continuous.continuousAt.comp continuousAt_snd).snd
  have hτ : ContinuousAt (fun p : Coeff × E ↦ (e p.2).1) (A₀, ξ) :=
    (e.continuous.continuousAt.comp continuousAt_snd).fst
  have hroot : ContinuousAt (fun p ↦ H (proj p)) (A₀, ξ) :=
    (show ContinuousAt H (proj (A₀, ξ)) from hdata.1.continuousAt).comp hp
  have hfirst := (hp.prodMk hτ).tendsto.eventually hu
  have hsecond := (show Tendsto (fun p ↦ (proj p, H (proj p)))
      (𝓝 (A₀, ξ)) (𝓝 z₀) by
    convert (hp.prodMk hroot).tendsto using 1
    exact congrArg (fun t ↦ 𝓝 (p₀, t)) hbase.symm).eventually hu
  have hbuffer : ball A₀ ε ×ˢ ball (e ξ).2 (min ε L) ∈ 𝓝 p₀ :=
    (isOpen_ball.prod isOpen_ball).mem_nhds
      ⟨mem_ball_self hε, mem_ball_self (lt_min hε hL)⟩
  have hevent : ∀ᶠ p : Coeff × E in 𝓝 (A₀, ξ), p.2 ≠ 0 ∧
      proj p ∈ ball A₀ ε ×ˢ ball (e ξ).2 (min ε L) ∧
      (determinant p.1 p.2 = 0 ↔ H (proj p) = (e p.2).1) := by
    filter_upwards [hfirst, hsecond, hp.preimage_mem_nhds hbuffer,
      continuousAt_snd.preimage_mem_nhds (isOpen_ne.mem_nhds hξ)] with p hp₁ hp₂ hpB hpne
    have hzero : coefficientSymbol e (proj p, H (proj p)) = 0 := by
      have hdetp := (hH.2 (proj p)
        ⟨ball_subset_closedBall hpB.1, ball_subset_closedBall hpB.2⟩).2.1
      exact mul_eq_zero_of_left hdetp _
    have huH := hp₂.mp hzero
    refine ⟨hpne, hpB, ?_⟩
    have heq : coefficientSymbol e (proj p, (e p.2).1) =
        determinant p.1 p.2 * determinantNormalization p.2 := by
      simp only [coefficientSymbol, proj, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
    rw [← mul_eq_zero_iff_right (determinantNormalization_pos hpne).ne', ← heq, hp₁, huH]
  obtain ⟨V, hV, ho, hv⟩ := _root_.eventually_nhds_iff.mp hevent
  exact ⟨V, ho, hv, hV⟩

end JanetCartan.ResponseTransfer.RetainedFactors

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open FrozenMenu CompatibleResponse ArbitraryAccuracy RegularSector.Characteristic
open RegularSector.Characteristic.RootFamily RegularSector.Characteristic.AlgebraicChart
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open ResponseTransfer.RetainedFactors

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The original primary phase solves the eikonal equation for the retained
amplitude root on its actual coefficient/covector neighborhood. In particular
the coefficient field and inverse chart of the primary construction are not
replaced. The open neighborhood is fixed before `Q`; the domain on the right
is its literal pullback by the original primary gradient. Establishing that a
chosen whole carrier lies in this domain remains a support obligation
(`app:ch_response:eq:response-exact-phase`). -/
theorem exists_retained_primary_root_domain {c C₀ : ℝ} (hP : P.IsValid c C₀)
    {i r c' : Fin (d + 1)}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {ξ : Euclidean (d + 1)}
    (hξ : ξ ≠ 0)
    {H : (Fin (d + 1) → MetricTensor (d + 1)) × Euclidean d → ℝ}
    {ε L μ ν : ℝ} (hε : 0 < ε) (hL : 0 < L) (hμ : 0 < μ) (hν : 0 < ν)
    (hH : RootBuffer i r c' A₀ ξ H ε L μ ν) :
    ∃ V : Set ((Fin (d + 1) → MetricTensor (d + 1)) × Euclidean (d + 1)),
      IsOpen V ∧ (A₀, ξ) ∈ V ∧
      ∀ Q : _,
        let D : Set (Euclidean (d + 1) × Euclidean 3) :=
          {q | (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
            q.2 ∈ parameterInterior (2 * P.radius) ∧
            (Q.1 ((primaryCoordinateChange i).symm q.1),
              T.carrierGradient Q ((primaryCoordinateChange i).symm q.1) q.2) ∈ V}
        IsOpen D ∧
          ContDiffOn ℝ ∞ (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) D ∧
          ∀ q ∈ D,
            rootSuspension (fieldRoot (coordinateSplit i) Q.1 H)
              (q.1, gradient (fun x ↦ T.primaryPhaseInCoordinates i Q x q.2) q.1) = 0 := by
  obtain ⟨V, hV, hv, hmatch⟩ :=
    exists_retained_root_characteristic_neighborhood hξ hε hL hμ hν hH
  refine ⟨V, hV, hv, ?_⟩
  intro Q D
  let F : Euclidean (d + 1) × Euclidean 3 → Euclidean (d + 1) × Euclidean 3 :=
    fun q ↦ ((primaryCoordinateChange i).symm q.1, q.2)
  let O : Set (Euclidean (d + 1) × Euclidean 3) :=
    F ⁻¹' (ball 0 T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
  have hF : ContDiff ℝ ∞ F :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hO : IsOpen O :=
    (isOpen_ball.prod (isOpen_parameterInterior _)).preimage hF.continuous
  have hQphys : ContDiffOn ℝ ∞ (fun q ↦ Q.1 (F q).1) O :=
    Q.2.1.comp (hF.fst.contDiffOn) (fun q hq ↦ (T.primary_state_mem Q hq.1 hq.2).1)
  have hg : ContDiffOn ℝ ∞ (fun q ↦ T.carrierGradient Q (F q).1 q.2) O :=
    (T.carrierGradient_smooth hP Q).comp hF.contDiffOn (fun _ hq ↦ hq)
  have hD : IsOpen D := by
    have ho := (hQphys.continuousOn.prodMk hg.continuousOn).isOpen_inter_preimage hO hV
    convert ho using 1
    ext q
    simp only [D, O, F, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod, and_assoc]
  refine ⟨hD, (T.carrier_smooth hP Q).comp hF.contDiffOn
    (fun q hq ↦ ⟨hq.1, hq.2.1⟩), ?_⟩
  intro q hq
  rw [T.primaryPhaseInCoordinates_gradient hP i Q hq.1 hq.2.1]
  have hm := ((hmatch _ hq.2.2).2.2).mp
    (T.carrier_characteristic Q hq.1 hq.2.1)
  have hstate : spacetimeRootState
      (q.1, primaryCoordinateChange i (T.carrierGradient Q (F q).1 q.2)) =
      adaptedPrimaryRootState (coordinateSplit i) (F q).1 (T.carrierGradient Q (F q).1 q.2) := by
    convert spacetimeRootState_primaryCoordinateChange i (F q).1
      (T.carrierGradient Q (F q).1 q.2) using 1
    simp only [F, ContinuousLinearEquiv.apply_symm_apply]
  change (primaryCoordinateChange i (T.carrierGradient Q (F q).1 q.2)) 0 -
    fieldRoot (coordinateSplit i) Q.1 H _ = 0
  rw [hstate, primaryCoordinateChange_apply, timeSpacePoint_time]
  simp only [fieldRoot, adaptedPrimaryRootState, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]
  simpa only [coordinateSplit_fst, F] using sub_eq_zero.mpr hm.symm

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
