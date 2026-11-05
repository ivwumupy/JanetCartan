module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicChart.ProtectionCertificates.LocalChart
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.AngularGeometry.Elapsed
public import JanetCartan.Geometry.IsometricEmbedding.Reference.RadialSeparation
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAdjointCone
public import JanetCartan.Iteration.PhysicalInitialization.AdmissionRange

/-!
# Original inactive-adjoint graph momentum

The literal adjoint differentiates the SAME elapsed graph at its source. Its
momentum is controlled here by the original coefficient root and Hamilton ODE,
not by a radial comparison or an absolute phase-jet bound. The original chart,
source masks and complete elapsed interval are never reduced or reselected.
Consumer: `app:ch_response:eq:fixed-factor-transfer`, inactive adjoint letters,
and `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPrimary.CharacteristicAdjointMomentum
open RegularSector.Characteristic ConicPhase EvolutionIntegral
open EvolutionIntegral.SymbolBudgets RootFamily AmplitudeBounds AlgebraicChart

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => Euclidean d
local notation "Z" => RootState V
local notation "TC" => RegularSector.Characteristic.TwoTimePoint V
local notation "Coeff" => Fin (d+1) → MetricTensor (d+1)

/-- The exact full elapsed differential, including BOTH Hamiltonian time terms.
It uses the original conic continuation and the same inverse flow chart
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem fderiv_elapsedPhase_apply
    (ℓ : V →L[ℝ] ℝ) (h : Z → ℝ) (Φ : Z × ℝ → Z)
    (C : OpenPartialHomeomorph TC TC) (t : ℝ) (y ξ v : E)
    (hdiff : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C
        (y 0,(y 0-t,(spatialPart y,(ℓ (spatialPart ξ))⁻¹ • spatialPart ξ))))
      (y 0,(y 0-t,(spatialPart y,(ℓ (spatialPart ξ))⁻¹ • spatialPart ξ)))) :
    let q : TC := (y 0,(y 0-t,(spatialPart y,(ℓ (spatialPart ξ))⁻¹ • spatialPart ξ)))
    let p := (twoTimeState Φ (C.symm q)).2.2
    fderiv ℝ (fun w ↦ elapsedPhase (curriedPhase ℓ C) t w ξ) y v =
      ξ 0 * v 0 + ℓ (spatialPart ξ) *
        ((h (y 0,(spatialPart y,p)) - h (y 0-t,((C.symm q).2.2.1,q.2.2.2))) * v 0 +
          ⟪p,spatialPart v⟫_ℝ) := by
  intro q p
  let π : E →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))
  let η := (ℓ (spatialPart ξ))⁻¹ • spatialPart ξ
  let A : E →L[ℝ] TC := π.prod (π.prod (spatialPartCLM.prod 0))
  have hm : HasFDerivAt (fun w : E ↦ (w 0,(w 0-t,(spatialPart w,η)))) A y :=
    π.hasFDerivAt.prodMk ((π.hasFDerivAt.sub_const t).prodMk
      (spatialPartCLM.hasFDerivAt.prodMk (hasFDerivAt_const (𝕜 := ℝ) η y)))
  have hd := ((π.hasFDerivAt.sub_const t).mul_const (ξ 0)).fun_add
    ((hdiff.comp y hm).const_mul (ℓ (spatialPart ξ)))
  have hf : HasFDerivAt (fun w ↦ elapsedPhase (curriedPhase ℓ C) t w ξ)
      (ξ 0 • π + ℓ (spatialPart ξ) •
        (twoTimePhaseDifferential h Φ C q).comp A) y := by
    simpa only [elapsedPhase,curriedPhase,phase,extend,ConicPhase.normalize,
      Function.comp_def,Pi.add_apply,η,π,q,EuclideanSpace.coe_proj] using hd
  have he := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hf.fderiv
  simpa only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    zero_apply,sub_apply,innerSL_apply_apply,inner_zero_right,add_zero,smul_eq_mul,
    twoTimePhaseDifferential,A,π,EuclideanSpace.coe_proj,spatialPartCLM_apply,q,p,sub_mul] using he

/-- The full elapsed graph momentum is close to the original frequency when
its SAME normalized spatial momentum and Hamiltonian values are close. The
actual ODE and coefficient-root estimates below produce those two defects;
this identity never replaces the transported momentum by `ξ`
(`new:eq:carrier-ibp`). -/
theorem norm_gradient_elapsedPhase_sub_le
    (ℓ : V →L[ℝ] ℝ) (h : Z → ℝ) (Φ : Z × ℝ → Z)
    (C : OpenPartialHomeomorph TC TC) (t : ℝ) (y ξ : E)
    (hℓ : ℓ (spatialPart ξ) ≠ 0)
    (hdiff : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C
        (y 0,(y 0-t,(spatialPart y,(ℓ (spatialPart ξ))⁻¹ • spatialPart ξ))))
      (y 0,(y 0-t,(spatialPart y,(ℓ (spatialPart ξ))⁻¹ • spatialPart ξ)))) :
    let q : TC := (y 0,(y 0-t,(spatialPart y,(ℓ (spatialPart ξ))⁻¹ • spatialPart ξ)))
    let p := (twoTimeState Φ (C.symm q)).2.2
    ‖gradient (fun w ↦ elapsedPhase (curriedPhase ℓ C) t w ξ) y - ξ‖ ≤
      (‖ℓ‖ * (|h (y 0,(spatialPart y,p)) - h (y 0-t,((C.symm q).2.2.1,q.2.2.2))| +
        ‖p-q.2.2.2‖)) * ‖ξ‖ := by
  intro q p
  let D := h (y 0,(spatialPart y,p)) - h (y 0-t,((C.symm q).2.2.1,q.2.2.2))
  let η := q.2.2.2
  have hη : ℓ (spatialPart ξ) • η = spatialPart ξ := by
    dsimp [η,q]
    exact smul_inv_smul₀ hℓ _
  rw [← (InnerProductSpace.toDual ℝ E).norm_map
    (gradient (fun w ↦ elapsedPhase (curriedPhase ℓ C) t w ξ) y - ξ),map_sub,toDual_gradient]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : (fderiv ℝ (fun w ↦ elapsedPhase (curriedPhase ℓ C) t w ξ) y -
      (InnerProductSpace.toDual ℝ E) ξ) v =
      ℓ (spatialPart ξ) * (D*v 0 + ⟪p-η,spatialPart v⟫_ℝ) := by
    rw [sub_apply,fderiv_elapsedPhase_apply ℓ h Φ C t y ξ v hdiff]
    simp only [InnerProductSpace.toDual_apply_apply,inner_eq_time_add_spatial,
      inner_sub_left,D,p,η]
    have hi := congrArg (fun z : V ↦ ⟪z,spatialPart v⟫_ℝ) hη
    simp only [real_inner_smul_left] at hi
    dsimp only [η] at hi
    linarith
  rw [he,norm_mul]
  have hlam : ‖ℓ (spatialPart ξ)‖ ≤ ‖ℓ‖*‖ξ‖ :=
    (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_spatialPart_le ξ) (norm_nonneg _))
  have hsum : ‖D*v 0 + ⟪p-η,spatialPart v⟫_ℝ‖ ≤
      (|D|+‖p-η‖)*‖v‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,Real.norm_eq_abs D]
    calc
      |D| *‖v 0‖ + ‖⟪p-η,spatialPart v⟫_ℝ‖ ≤
          |D| *‖v‖ + ‖p-η‖*‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v 0) (abs_nonneg _))
          ((norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (norm_spatialPart_le v) (norm_nonneg _)))
      _ = _ := by ring
  exact (mul_le_mul hlam hsum (norm_nonneg _) (by positivity)).trans_eq (by dsimp [D,η]; ring)

/-- The original Hamilton ODE controls momentum on its entire retained inverse
segment. The endpoint at source time uses the SAME flow initial condition and
inverse coordinates; no smaller time interval is selected
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem norm_twoTime_momentum_sub_le
    (h : Z → ℝ) (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC)
    (z : Z) (R r T : ℝ)
    (hΦ : ODE.IsSmoothFlowOn (rootHamiltonField h) z R r T Φ)
    (hsource : C.source ⊆ twoTimeDomain z r T)
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    {q : TC} (hq : q ∈ C.target)
    (hsegment : ∀ u ∈ uIcc q.2.1 q.1,
      HasDerivAt (fun s ↦ twoTimeState Φ (s,(C.symm q).2))
        (rootHamiltonField h (twoTimeState Φ (u,(C.symm q).2))) u ∧
      twoTimeState Φ (u,(C.symm q).2) ∈ closedBall z R)
    {B : ℝ} (hbound : ∀ w ∈ closedBall z R, ‖rootPositionGradient h w‖ ≤ B) :
    ‖(twoTimeState Φ (C.symm q)).2.2 - q.2.2.2‖ ≤ B * |q.1-q.2.1| := by
  have hc := twoTimeChart_inverse_coordinates hC hq
  have hw : (C.symm q).2 ∈ closedBall z r :=
    ball_subset_closedBall (hsource (C.map_target hq)).1
  let γ : ℝ → V := fun u ↦ (twoTimeState Φ (u,(C.symm q).2)).2.2
  have hi : γ q.2.1 = q.2.2.2 := by
    dsimp [γ,twoTimeState]
    rw [hc.2.1,sub_self,hΦ.initial _ hw]
    exact hc.2.2.1
  have ho : γ q.1 = (twoTimeState Φ (C.symm q)).2.2 := by
    dsimp [γ,twoTimeState]
    rw [hc.1]
  have hder u (hu : u ∈ uIcc q.2.1 q.1) :
      HasDerivAt γ (rootPositionGradient h (twoTimeState Φ (u,(C.symm q).2))) u :=
    ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ ℝ (V × V))).hasFDerivAt.comp_hasDerivAt
      u (hsegment u hu).1
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu ↦ (hder u hu).hasDerivWithinAt)
    (fun u hu ↦ hbound _ (hsegment u hu).2)
    (convex_uIcc q.2.1 q.1) (left_mem_uIcc) (right_mem_uIcc)
  change ‖γ q.1-γ q.2.1‖ ≤ B*‖q.1-q.2.1‖ at hb
  simpa only [hi,ho,Real.norm_eq_abs] using hb

/-- The physical root gradient contains a genuine derivative of the SAME Q.
In particular it vanishes at a constant coefficient field, without selecting a
different root or flow (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem norm_rootPositionGradient_fieldRoot_le
    (e : E ≃L[ℝ] (ℝ × V)) (Q : E → Coeff)
    (H : Coeff × V → ℝ) (w : Z)
    (hQ : DifferentiableAt ℝ Q (rootPhysicalPosition e w))
    (hH : DifferentiableAt ℝ H (Q (rootPhysicalPosition e w),w.2.2)) :
    ‖rootPositionGradient (fieldRoot e Q H) w‖ ≤
      ‖fderiv ℝ H (Q (rootPhysicalPosition e w),w.2.2)‖ *
        ‖fderiv ℝ Q (rootPhysicalPosition e w)‖ * ‖rootPhysicalPosition e‖ := by
  let L := rootPhysicalPosition e
  let Pη : Z →L[ℝ] V := (ContinuousLinearMap.snd ℝ V V).comp
    (ContinuousLinearMap.snd ℝ ℝ (V × V))
  let J : V →L[ℝ] Z := (ContinuousLinearMap.inr ℝ ℝ (V × V)).comp
    (ContinuousLinearMap.inl ℝ V V)
  have hp : HasFDerivAt (fun z : Z ↦ (Q (L z),z.2.2))
      (((fderiv ℝ Q (L w)).comp L).prod Pη) w :=
    (hQ.hasFDerivAt.comp w L.hasFDerivAt).prodMk Pη.hasFDerivAt
  have hd : HasFDerivAt (fieldRoot e Q H)
      ((fderiv ℝ H (Q (L w),w.2.2)).comp
        (((fderiv ℝ Q (L w)).comp L).prod Pη)) w := by
    change HasFDerivAt (fun z : Z ↦ H (Q (e.symm (z.1,z.2.1)),z.2.2)) _ w
    simpa only [Function.comp_def,fieldRoot,L,rootPhysicalPosition,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      ContinuousLinearEquiv.coe_coe] using hH.hasFDerivAt.comp w hp
  change ‖(InnerProductSpace.toDual ℝ V).symm ((fderiv ℝ (fieldRoot e Q H) w).comp J)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [hd.fderiv]
  change ‖fderiv ℝ H (Q (L w),w.2.2) (fderiv ℝ Q (L w) (L (0,(v,0))),0)‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ H (Q (L w),w.2.2)‖ * ‖fderiv ℝ Q (L w) (L (0,(v,0)))‖ := by
      simpa only [Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _)] using
        (fderiv ℝ H (Q (L w),w.2.2)).le_opNorm (fderiv ℝ Q (L w) (L (0,(v,0))),0)
    _ ≤ ‖fderiv ℝ H (Q (L w),w.2.2)‖ *
        (‖fderiv ℝ Q (L w)‖ * (‖L‖*‖v‖)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply ((fderiv ℝ Q (L w)).le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _),
        max_eq_right (norm_nonneg _)] using L.le_opNorm (0,(v,0))
    _ = _ := by dsimp [L]; ring

/-- The original C6 coefficient distance controls values and the actual first
physical derivative; the constant cube contributes no derivative. These are
primitive coefficient inputs, not a graph-momentum hypothesis
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem originalCoefficient_value_fderiv_le
    (Q : E → Coeff) (hQ : ContDiff ℝ ∞ Q) (A₀ : Coeff) (x : E) (R : ℝ)
    {y : E} (hy : y ∈ closedBall x R) :
    ‖Q y-A₀‖ ≤ cNorm (closedBall x R) 6 (Q-fun _ ↦ A₀) ∧
      ‖fderiv ℝ Q y‖ ≤ cNorm (closedBall x R) 6 (Q-fun _ ↦ A₀) := by
  have hs : ∀ z ∈ closedBall x R, ContDiffAt ℝ (6 : ℕ∞ω) (Q-fun _ ↦ A₀) z :=
    fun _ _ ↦ ((hQ.sub contDiff_const).contDiffAt).of_le (by simp)
  constructor
  · simpa only [norm_iteratedFDeriv_zero,Pi.sub_apply] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x R) hs hy
        (by omega : 0 ≤ 6)
  · have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x R) hs hy
      (by omega : 1 ≤ 6)
    rw [norm_iteratedFDeriv_one] at hh
    change ‖fderiv ℝ (fun z ↦ Q z-A₀) y‖ ≤ _ at hh
    simpa only [fderiv_sub_const] using hh

open RegularSector.FiniteMasks.ActualFamily ActualCarriers

/-- A fixed constant controls the original graph momentum by the SAME original
C6 coefficient distance. It precedes Q, its actual flow and inverse chart, and
all frequencies. The ENTIRE original mask-time interval is retained. The only
flow inputs are the original protection certificate's ODE, initial condition,
inverse projection, complete inverse segments and phase differential; no
momentum comparison or radial estimate is assumed
(`app:ch_response:eq:fixed-factor-transfer`, `new:eq:carrier-ibp`). -/
theorem exists_original_graph_momentum_constant
    {Ω : Set E} {x ξc : E} {RQ Mcap : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d+1)) ξc Mcap)
    (hroot : RootBuffer c.index c.row c.col (cubeStress (d+1)) ξc c.root
      c.coefficientRadius c.rootRadius c.minorGap c.transportGap)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotect : LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost) :
    let e := coordinateSplit c.index
    let z : Z := ((e x).1,((e x).2,(e ξc).2))
    ∃ C₀ > (0 : ℝ), ∀ Q : E → Coeff, ContDiff ℝ ∞ Q →
      cNorm (closedBall x RQ) 6 (Q-fun _ ↦ cubeStress (d+1)) ≤ c.coefficientRadius →
    let h := fieldRoot e Q c.root
    ∀ (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      ODE.IsSmoothFlowOn (rootHamiltonField h) z c.rootRadius (c.rootRadius/2) evolutionTime Φ →
      C.source ⊆ twoTimeDomain z (c.rootRadius/2) evolutionTime →
      (C : TC → TC) = twoTimeProjection Φ →
      (∀ q ∈ C.target, ∀ u ∈ uIcc q.2.1 q.1,
        (u,(C.symm q).2) ∈ twoTimeDomain z (c.rootRadius/2) evolutionTime ∧
        HasDerivAt (fun s ↦ twoTimeState Φ (s,(C.symm q).2))
          (rootHamiltonField h (twoTimeState Φ (u,(C.symm q).2))) u ∧
        twoTimeState Φ (u,(C.symm q).2) ∈ closedBall z c.rootRadius ∧
        (twoTimeState Φ (u,(C.symm q).2)).1 = u) →
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      ∀ t ∈ Icc (0 : ℝ) c.maskRadius, ∀ y ξ : E,
      c.radialSection (spatialPart ξ) ≠ 0 →
      (y 0,(y 0-t,(spatialPart y,(c.radialSection (spatialPart ξ))⁻¹ • spatialPart ξ))) ∈ C.target →
      ‖gradient (fun w ↦ elapsedPhase (curriedPhase c.radialSection C) t w ξ) y-ξ‖ ≤
        C₀*cNorm (closedBall x RQ) 6 (Q-fun _ ↦ cubeStress (d+1))*‖ξ‖ := by
  intro e z
  let K : Set (Coeff × V) := closedBall (cubeStress (d+1)) c.coefficientRadius ×ˢ
    closedBall z.2.2 (min c.coefficientRadius c.rootRadius)
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hconv : Convex ℝ K := (convex_closedBall _ _).prod (convex_closedBall _ _)
  have hs : ∀ p ∈ K, ContDiffAt ℝ ∞ c.root p := fun p hp ↦ (hroot.2 p hp).1
  let M := 1+cNorm K 1 c.root
  have hM : 0 < M := by dsimp [M]; linarith [cNorm_nonneg K 1 c.root]
  have hD : ∀ p ∈ K, ‖fderiv ℝ c.root p‖ ≤ M := by
    intro p hp
    have hh := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun p hp ↦ (hs p hp).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)) hp (show 1 ≤ 1 from le_rfl)
    rw [norm_iteratedFDeriv_one] at hh
    exact hh.trans (by dsimp [M]; linarith)
  let L := rootPhysicalPosition e
  let Δ := c.maskRadius
  have hΔ : 0 ≤ Δ := c.maskRadius_pos.le
  let A := ‖c.radialSection‖*(M*(2+Δ*M*‖L‖)+Δ*M*‖L‖)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rcases hprotect with ⟨_,_,_,_,_,_,_,_,hwhole,_⟩
  refine ⟨1+A,by linarith,?_⟩
  intro Q hQ hsmall h Φ C hΦ hsource hC hsegment hdiff t ht y ξ hsec hq
  let δ := cNorm (closedBall x RQ) 6 (Q-fun _ ↦ cubeStress (d+1))
  have hδ : 0 ≤ δ := cNorm_nonneg _ _ _
  have hcoeff w (hw : w ∈ closedBall z c.rootRadius) :
      ‖Q (L w)-cubeStress (d+1)‖ ≤ δ ∧ ‖fderiv ℝ Q (L w)‖ ≤ δ :=
    originalCoefficient_value_fderiv_le Q hQ (cubeStress (d+1)) x RQ (hwhole w hw).2.1
  have hpair w (hw : w ∈ closedBall z c.rootRadius) : (Q (L w),w.2.2) ∈ K := by
    refine ⟨?_,?_⟩
    · exact mem_closedBall_iff_norm.mpr ((hcoeff w hw).1.trans hsmall)
    · have hh : dist w.1 z.1 ≤ c.rootRadius ∧ dist w.2.1 z.2.1 ≤ c.rootRadius ∧
          dist w.2.2 z.2.2 ≤ c.rootRadius := by
        simpa only [mem_closedBall,Prod.dist_eq,max_le_iff] using hw
      exact mem_closedBall.mpr (le_min (hwhole w hw).2.2.1 hh.2.2)
  let B := M*δ*‖L‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrootgrad w (hw : w ∈ closedBall z c.rootRadius) : ‖rootPositionGradient h w‖ ≤ B := by
    have hb := norm_rootPositionGradient_fieldRoot_le e Q c.root w
      ((hQ.contDiffAt).differentiableAt (by simp))
      ((hs _ (hpair w hw)).differentiableAt (by simp))
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (hD _ (hpair w hw)) (hcoeff w hw).2 (norm_nonneg _) hM.le) (norm_nonneg _))
  let q : TC := (y 0,(y 0-t,(spatialPart y,(c.radialSection (spatialPart ξ))⁻¹ • spatialPart ξ)))
  have hc := twoTimeChart_inverse_coordinates hC hq
  let wi := (C.symm q).2
  let wf := twoTimeState Φ (C.symm q)
  have hwi : wi ∈ closedBall z c.rootRadius :=
    closedBall_subset_closedBall (by linarith [c.rootRadius_pos])
      (ball_subset_closedBall (hsource (C.map_target hq)).1)
  have hfinal : twoTimeState Φ (q.1,(C.symm q).2) = wf := by
    dsimp only [wf,twoTimeState]
    rw [hc.1]
  have hwf : wf ∈ closedBall z c.rootRadius :=
    hfinal ▸ (hsegment q hq q.1 right_mem_uIcc).2.2.1
  have hclock : wf.1 = q.1 := by
    rw [← hfinal]
    exact (hsegment q hq q.1 right_mem_uIcc).2.2.2
  have htime : q.1-q.2.1 = t := by dsimp [q]; ring
  have hp₀ := norm_twoTime_momentum_sub_le h Φ C z c.rootRadius (c.rootRadius/2) evolutionTime
    hΦ hsource hC hq (fun u hu ↦ ⟨(hsegment q hq u hu).2.1,(hsegment q hq u hu).2.2.1⟩) hrootgrad
  have hp : ‖wf.2.2-q.2.2.2‖ ≤ B*t := by
    change ‖wf.2.2-q.2.2.2‖ ≤ B*|q.1-q.2.1| at hp₀
    rw [htime,abs_of_nonneg ht.1] at hp₀
    exact hp₀
  have hp' : ‖wf.2.2-wi.2.2‖ ≤ B*t := by
    have hη : (C.symm q).2.2.2 = q.2.2.2 := hc.2.2.1
    change ‖wf.2.2-(C.symm q).2.2.2‖ ≤ B*t
    rw [hη]
    exact hp
  have hQQ : ‖Q (L wf)-Q (L wi)‖ ≤ 2*δ := by
    calc
      _ ≤ ‖Q (L wf)-cubeStress (d+1)‖ + ‖cubeStress (d+1)-Q (L wi)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ+δ := add_le_add (hcoeff wf hwf).1 (by simpa only [norm_sub_rev] using (hcoeff wi hwi).1)
      _ = _ := by ring
  have hpairdiff : ‖(Q (L wf),wf.2.2)-(Q (L wi),wi.2.2)‖ ≤ 2*δ+B*t := by
    change max ‖Q (L wf)-Q (L wi)‖ ‖wf.2.2-wi.2.2‖ ≤ _
    exact max_le (hQQ.trans (le_add_of_nonneg_right (mul_nonneg hB ht.1)))
      (hp'.trans (le_add_of_nonneg_left (by positivity)))
  have henergy : |h wf-h wi| ≤ M*(2*δ+B*t) := by
    have hb := hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun p hp ↦ (hs p hp).differentiableAt (by simp)) hD (hpair wi hwi) (hpair wf hwf)
    change |h wf-h wi| ≤ _ at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hpairdiff hM.le)
  have hew : wf = (y 0,(spatialPart y,wf.2.2)) := by
    apply Prod.ext
    · exact hclock
    · exact Prod.ext hc.2.2.2 rfl
  have hewi : wi = (y 0-t,((C.symm q).2.2.1,q.2.2.2)) :=
    Prod.ext hc.2.1 (Prod.ext rfl hc.2.2.1)
  have hb := norm_gradient_elapsedPhase_sub_le c.radialSection h Φ C t y ξ hsec (hdiff _ hq)
  change ‖gradient (fun w ↦ elapsedPhase (curriedPhase c.radialSection C) t w ξ) y-ξ‖ ≤
    (‖c.radialSection‖*(|h (y 0,(spatialPart y,wf.2.2))-
      h (y 0-t,((C.symm q).2.2.1,q.2.2.2))|+‖wf.2.2-q.2.2.2‖))*‖ξ‖ at hb
  rw [← hew,← hewi] at hb
  have hBt : B*t ≤ B*Δ := mul_le_mul_of_nonneg_left ht.2 hB
  calc
    _ ≤ (‖c.radialSection‖*(|h wf-h wi|+‖wf.2.2-q.2.2.2‖))*‖ξ‖ := hb
    _ ≤ (‖c.radialSection‖*(M*(2*δ+B*Δ)+B*Δ))*‖ξ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact add_le_add (henergy.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hBt) hM.le))
        (hp.trans hBt)
    _ = A*δ*‖ξ‖ := by dsimp [A,B]; ring
    _ ≤ (1+A)*δ*‖ξ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith) hδ

/-- The relative graph-momentum error supplies BOTH angular proximity and the
fixed radial constants. Neither is inferred from an unrelated phase-cost bound
(`new:eq:carrier-ibp`, `app:ch_response:eq:fixed-factor-transfer`). -/
theorem normalized_and_radial_bounds_of_relative_error
    {g ξ : E} {ε : ℝ} (hξ : ξ ≠ 0)
    (herr : ‖g-ξ‖ ≤ min (ε/2) (1/2)*‖ξ‖) :
    dist (NormedSpace.normalize g) (NormedSpace.normalize ξ) ≤ ε ∧
      (1/2 : ℝ)*‖ξ‖ ≤ ‖g‖ ∧ ‖g‖ ≤ (3/2 : ℝ)*‖ξ‖ := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hh : ‖g-ξ‖ ≤ (1/2 : ℝ)*‖ξ‖ :=
    herr.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn.le)
  have he : ‖g-ξ‖ ≤ (ε/2)*‖ξ‖ :=
    herr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn.le)
  have hd : ‖ξ‖*dist (NormedSpace.normalize g) (NormedSpace.normalize ξ) ≤ 2*‖g-ξ‖ := by
    simpa only [dist_eq_norm] using norm_mul_normalize_sub_le g ξ
  have hdir : ‖ξ‖*dist (NormedSpace.normalize g) (NormedSpace.normalize ξ) ≤ ‖ξ‖*ε := by
    calc
      _ ≤ 2*‖g-ξ‖ := hd
      _ ≤ ‖ξ‖*ε := by nlinarith only [he]
  refine ⟨le_of_mul_le_mul_left hdir hn,?_,?_⟩
  · have ht := norm_sub_le_norm_sub_add_norm_sub ξ g 0
    simp only [sub_zero,norm_sub_rev ξ] at ht
    linarith
  · have ht := norm_sub_le_norm_sub_add_norm_sub g ξ 0
    simp only [sub_zero] at ht
    linarith

/-- For any prescribed angular error, choose the positive coefficient margin
BEFORE Q, its native flow and every frequency. The SAME elapsed graph satisfies
a relative error, the requested angular control and the fixed radial constants
on the full original mask-time interval. No mask or chart is changed
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_original_graph_momentum_margin
    {Ω : Set E} {x ξc : E} {RQ Mcap : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d+1)) ξc Mcap)
    (hroot : RootBuffer c.index c.row c.col (cubeStress (d+1)) ξc c.root
      c.coefficientRadius c.rootRadius c.minorGap c.transportGap)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotect : LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost)
    {ε : ℝ} (hε : 0 < ε) :
    let e := coordinateSplit c.index
    let z : Z := ((e x).1,((e x).2,(e ξc).2))
    ∃ δ > (0 : ℝ), ∀ Q : E → Coeff, ContDiff ℝ ∞ Q →
      cNorm (closedBall x RQ) 6 (Q-fun _ ↦ cubeStress (d+1)) < δ →
    let h := fieldRoot e Q c.root
    ∀ (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      ODE.IsSmoothFlowOn (rootHamiltonField h) z c.rootRadius (c.rootRadius/2) evolutionTime Φ →
      C.source ⊆ twoTimeDomain z (c.rootRadius/2) evolutionTime →
      (C : TC → TC) = twoTimeProjection Φ →
      (∀ q ∈ C.target, ∀ u ∈ uIcc q.2.1 q.1,
        (u,(C.symm q).2) ∈ twoTimeDomain z (c.rootRadius/2) evolutionTime ∧
        HasDerivAt (fun s ↦ twoTimeState Φ (s,(C.symm q).2))
          (rootHamiltonField h (twoTimeState Φ (u,(C.symm q).2))) u ∧
        twoTimeState Φ (u,(C.symm q).2) ∈ closedBall z c.rootRadius ∧
        (twoTimeState Φ (u,(C.symm q).2)).1 = u) →
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      ∀ t ∈ Icc (0 : ℝ) c.maskRadius, ∀ y ξ : E,
      c.radialSection (spatialPart ξ) ≠ 0 →
      (y 0,(y 0-t,(spatialPart y,(c.radialSection (spatialPart ξ))⁻¹ • spatialPart ξ))) ∈ C.target →
      let ψ := fun w ↦ elapsedPhase (curriedPhase c.radialSection C) t w ξ
      ‖gradient ψ y-ξ‖ ≤ min (ε/2) (1/2)*‖ξ‖ ∧
      dist (NormedSpace.normalize (gradient ψ y)) (NormedSpace.normalize ξ) ≤ ε ∧
      (1/2 : ℝ)*‖ξ‖ ≤ ‖fderiv ℝ ψ y‖ ∧ ‖fderiv ℝ ψ y‖ ≤ (3/2 : ℝ)*‖ξ‖ := by
  intro e z
  obtain ⟨C₀,hC₀,hbound⟩ := exists_original_graph_momentum_constant c hroot hprotect
  let ρ := min (ε/2) (1/2)
  have hρ : 0 < ρ := lt_min (half_pos hε) (by norm_num)
  let δ := min c.coefficientRadius (ρ/(C₀+1))
  have hδ : 0 < δ := lt_min c.coefficientRadius_pos (div_pos hρ (by linarith))
  refine ⟨δ,hδ,?_⟩
  intro Q hQ hnear h Φ C hΦ hsource hC hsegment hdiff t ht y ξ hsec hq ψ
  have hsmall : cNorm (closedBall x RQ) 6 (Q-fun _ ↦ cubeStress (d+1)) ≤ c.coefficientRadius :=
    hnear.le.trans (min_le_left _ _)
  have herr := hbound Q hQ hsmall Φ C hΦ hsource hC hsegment hdiff t ht y ξ hsec hq
  have hδρ : δ*(C₀+1) ≤ ρ := (le_div_iff₀ (by linarith : 0 < C₀+1)).mp (min_le_right _ _)
  have hprod : C₀*cNorm (closedBall x RQ) 6 (Q-fun _ ↦ cubeStress (d+1)) ≤ ρ := by
    calc
      _ ≤ C₀*δ := mul_le_mul_of_nonneg_left hnear.le hC₀.le
      _ ≤ ρ := by nlinarith [hδ.le]
  have herr' : ‖gradient ψ y-ξ‖ ≤ min (ε/2) (1/2)*‖ξ‖ :=
    herr.trans (mul_le_mul_of_nonneg_right hprod (norm_nonneg _))
  have hξ : ξ ≠ 0 := by
    intro hh
    apply hsec
    rw [hh,← spatialPartCLM_apply,map_zero,map_zero]
  obtain ⟨ha,hl,hu⟩ := normalized_and_radial_bounds_of_relative_error hξ herr'
  refine ⟨herr',ha,?_,?_⟩
  · simpa only [gradient,LinearIsometryEquiv.norm_map] using hl
  · simpa only [gradient,LinearIsometryEquiv.norm_map] using hu

/-- At the literal cube field the SAME original Hamilton flow has zero spatial
momentum variation; the two root-energy terms cancel. Consequently the full
elapsed source gradient is EXACTLY the initial frequency, not merely comparable
to its norm. This is a specialization of the actual ODE/root estimate, not a
reselected flat phase (`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem gradient_elapsedPhase_cube_eq
    {Ω : Set E} {x ξc : E} {RQ Mcap : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d+1)) ξc Mcap)
    (hroot : RootBuffer c.index c.row c.col (cubeStress (d+1)) ξc c.root
      c.coefficientRadius c.rootRadius c.minorGap c.transportGap)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotect : LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost) :
    let e := coordinateSplit c.index
    let z : Z := ((e x).1,((e x).2,(e ξc).2))
    let h := fieldRoot e (fun _ ↦ cubeStress (d+1)) c.root
    ∀ (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      ODE.IsSmoothFlowOn (rootHamiltonField h) z c.rootRadius (c.rootRadius/2) evolutionTime Φ →
      C.source ⊆ twoTimeDomain z (c.rootRadius/2) evolutionTime →
      (C : TC → TC) = twoTimeProjection Φ →
      (∀ q ∈ C.target, ∀ u ∈ uIcc q.2.1 q.1,
        (u,(C.symm q).2) ∈ twoTimeDomain z (c.rootRadius/2) evolutionTime ∧
        HasDerivAt (fun s ↦ twoTimeState Φ (s,(C.symm q).2))
          (rootHamiltonField h (twoTimeState Φ (u,(C.symm q).2))) u ∧
        twoTimeState Φ (u,(C.symm q).2) ∈ closedBall z c.rootRadius ∧
        (twoTimeState Φ (u,(C.symm q).2)).1 = u) →
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      ∀ t ∈ Icc (0 : ℝ) c.maskRadius, ∀ y ξ : E,
      c.radialSection (spatialPart ξ) ≠ 0 →
      (y 0,(y 0-t,(spatialPart y,(c.radialSection (spatialPart ξ))⁻¹ • spatialPart ξ))) ∈ C.target →
      gradient (fun w ↦ elapsedPhase (curriedPhase c.radialSection C) t w ξ) y = ξ := by
  intro e z h Φ C hΦ hsource hC hsegment hdiff t ht y ξ hsec hq
  obtain ⟨C₀,_,hbound⟩ := exists_original_graph_momentum_constant c hroot hprotect
  have hzero : cNorm (closedBall x RQ) 6
      ((fun _ : E ↦ cubeStress (d+1))-(fun _ ↦ cubeStress (d+1))) = 0 := by simp
  have hb := hbound (fun _ ↦ cubeStress (d+1)) contDiff_const
    (by rw [hzero]; exact c.coefficientRadius_pos.le) Φ C hΦ hsource hC hsegment hdiff t ht y ξ hsec hq
  rw [hzero,mul_zero,zero_mul] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

open UniformEvolution

/-- The pre-current momentum margin on the actual retained physical box and
ENTIRE original frequency domain. The same target buffer discharges normalized
point membership; there is no assumed angular certificate. This covers the
original `0 ≤ t ≤ 3*maskRadius/4` operator and the larger original radial window
without modifying either (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem exists_original_retained_graph_momentum_margin
    {Ω : Set E} {x ξc : E} {RQ Mcap : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d+1)) ξc Mcap)
    (hroot : RootBuffer c.index c.row c.col (cubeStress (d+1)) ξc c.root
      c.coefficientRadius c.rootRadius c.minorGap c.transportGap)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotect : LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost)
    {a : ℝ} (ha : 0 < a) (hmask : c.maskRadius ≤ a) (htarget : 4*a ≤ c.targetRadius)
    {ε : ℝ} (hε : 0 < ε) :
    let e := coordinateSplit c.index
    let z : Z := ((e x).1,((e x).2,(e ξc).2))
    ∃ δ > (0 : ℝ), ∀ Q : E → Coeff, ContDiff ℝ ∞ Q →
      cNorm (closedBall x RQ) 6 (Q-fun _ ↦ cubeStress (d+1)) < δ →
    let h := fieldRoot e Q c.root
    ∀ (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
      ODE.IsSmoothFlowOn (rootHamiltonField h) z c.rootRadius (c.rootRadius/2) evolutionTime Φ →
      C.source ⊆ twoTimeDomain z (c.rootRadius/2) evolutionTime →
      (C : TC → TC) = twoTimeProjection Φ →
      (∀ q ∈ C.target, ∀ u ∈ uIcc q.2.1 q.1,
        (u,(C.symm q).2) ∈ twoTimeDomain z (c.rootRadius/2) evolutionTime ∧
        HasDerivAt (fun s ↦ twoTimeState Φ (s,(C.symm q).2))
          (rootHamiltonField h (twoTimeState Φ (u,(C.symm q).2))) u ∧
        twoTimeState Φ (u,(C.symm q).2) ∈ closedBall z c.rootRadius ∧
        (twoTimeState Φ (u,(C.symm q).2)).1 = u) →
      (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
      closedBall (z.1,z) c.targetRadius ⊆ C.target →
      ∀ aperture : ℝ, ∀ t ∈ Icc (0 : ℝ) c.maskRadius,
      ∀ y ∈ elapsedPhysicalBox z (a/2), ∀ ξ ∈ retainedFrequencyDomain c.radialSection z a aperture (1/2),
      let ψ := fun w ↦ elapsedPhase (curriedPhase c.radialSection C) t w ξ
      ‖gradient ψ y-ξ‖ ≤ min (ε/2) (1/2)*‖ξ‖ ∧
      dist (NormedSpace.normalize (gradient ψ y)) (NormedSpace.normalize ξ) ≤ ε ∧
      (1/2 : ℝ)*‖ξ‖ ≤ ‖fderiv ℝ ψ y‖ ∧ ‖fderiv ℝ ψ y‖ ≤ (3/2 : ℝ)*‖ξ‖ := by
  intro e z
  obtain ⟨δ,hδ,hmargin⟩ := exists_original_graph_momentum_margin c hroot hprotect hε
  refine ⟨δ,hδ,?_⟩
  intro Q hQ hnear h Φ C hΦ hsource hC hsegment hdiff hbuffer aperture t ht y hy ξ hξ
  have hq := CharacteristicAdjointInactive.full_elapsedPoint_mem_retained_phase_target
    c.radialSection z C ha hmask htarget hbuffer ht hy hξ
  exact hmargin Q hQ hnear Φ C hΦ hsource hC hsegment hdiff t ht y ξ (ne_of_gt hq.1) hq.2

/-- Enlarging only a proof box contains the unchanged original physical source
box. This does not alter any source mask or operator
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem elapsedPhysicalBox_subset_of_radius_le (z : Z) {a b : ℝ} (hab : a ≤ b) :
    elapsedPhysicalBox z (a/2) ⊆ elapsedPhysicalBox z (b/2) := by
  intro y hy
  exact ⟨ball_subset_ball (by linarith) hy.1,ball_subset_ball (by linarith) hy.2⟩

/-- The same retained frequency domain is monotone in its proof radius; its
original aperture, positive collar and actual frequency multiplier remain
unchanged (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retainedFrequencyDomain_subset_of_radius_le
    (ℓ : V →L[ℝ] ℝ) (z : Z) {a b : ℝ} (hab : a ≤ b) (aperture collar : ℝ) :
    retainedFrequencyDomain ℓ z a aperture collar ⊆ retainedFrequencyDomain ℓ z b aperture collar := by
  intro ξ hξ
  exact ⟨⟨⟨hξ.1.1.1,ball_subset_ball (by linarith) hξ.1.1.2⟩,hξ.1.2⟩,hξ.2⟩

open ProtectedFlow ProjectedStressFrame

/-- Actual physical histories produce the original native graph-momentum
admission. The reference-frame tolerance precedes the final reference; the
initial-scale threshold precedes every history. The SAME globally extended Q,
root, flow, chart, full elapsed interval, physical source box and frequency
collar are retained. The reference tolerance is explicit: increasing the initial
scale alone is NOT claimed to make an arbitrary reference approach the cube.
Consumers: the SAME original final-source selection and both signs of the
inactive adjoint in `app:ch_response:eq:fixed-factor-transfer`. -/
theorem exists_physical_history_graph_momentum_admission
    {Ω : Set E} {x ξc : E} {RQ Mcap : ℝ}
    (c : LocalChart Ω x RQ (cubeStress (d+1)) ξc Mcap)
    (hroot : RootBuffer c.index c.row c.col (cubeStress (d+1)) ξc c.root
      c.coefficientRadius c.rootRadius c.minorGap c.transportGap)
    {evolutionTime speedGap rootSize : ℝ} {rootCost : ℕ → ℝ}
    (hprotect : LocalProtectionCertificate c evolutionTime speedGap rootSize rootCost)
    {a : ℝ} (ha : 0 < a) (hmask : c.maskRadius ≤ a) (htarget : 4*a ≤ c.targetRadius)
    (ext : BallExtension.Parameters E) {r : ℝ}
    (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference (d+1), ∀ R : ℝ,
      0 < r → r < R → R < G.domain.chartRadius →
      (∀ i, cNorm (closedBall (0 : E) r) 6
        (fun v ↦ projectedStress G.map v i-cubeStress (d+1) i) < η) →
      ∀ {Cband : ℝ}, 1 ≤ Cband → ∀ rStar kMin : ℕ, 8 ≤ rStar →
      RevisedScales.displacementLoss (d+1) +
        bandExponent*((rStar : ℝ)+((d+1 : ℕ) : ℝ)/2)+2 < (kMin : ℝ) →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → SchwartzMap E (Euclidean (embeddingDimension (d+1))))
        (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let Q := extendedProjectedStress ext (RevisedGlobal.finiteMap G.map u)
      let e := coordinateSplit c.index
      let z : Z := ((e x).1,((e x).2,(e ξc).2))
      let h := fieldRoot e Q c.root
      ContDiff ℝ ∞ Q ∧ MapsTo Q univ (closedBall (cubeStress (d+1)) c.coefficientRadius) ∧
      ∀ (Φ : Z × ℝ → Z) (C : OpenPartialHomeomorph TC TC),
        ODE.IsSmoothFlowOn (rootHamiltonField h) z c.rootRadius (c.rootRadius/2) evolutionTime Φ →
        C.source ⊆ twoTimeDomain z (c.rootRadius/2) evolutionTime →
        (C : TC → TC) = twoTimeProjection Φ →
        (∀ q ∈ C.target, ∀ v ∈ uIcc q.2.1 q.1,
          (v,(C.symm q).2) ∈ twoTimeDomain z (c.rootRadius/2) evolutionTime ∧
          HasDerivAt (fun w ↦ twoTimeState Φ (w,(C.symm q).2))
            (rootHamiltonField h (twoTimeState Φ (v,(C.symm q).2))) v ∧
          twoTimeState Φ (v,(C.symm q).2) ∈ closedBall z c.rootRadius ∧
          (twoTimeState Φ (v,(C.symm q).2)).1 = v) →
        (∀ q ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C q) q) →
        closedBall (z.1,z) c.targetRadius ⊆ C.target →
        ∀ aperture : ℝ, ∀ t ∈ Icc (0 : ℝ) c.maskRadius,
        ∀ y ∈ elapsedPhysicalBox z (a/2), ∀ ξ ∈ retainedFrequencyDomain c.radialSection z a aperture (1/2),
        let ψ := fun w ↦ elapsedPhase (curriedPhase c.radialSection C) t w ξ
        ‖gradient ψ y-ξ‖ ≤ min (ε/2) (1/2)*‖ξ‖ ∧
        dist (NormedSpace.normalize (gradient ψ y)) (NormedSpace.normalize ξ) ≤ ε ∧
        (1/2 : ℝ)*‖ξ‖ ≤ ‖fderiv ℝ ψ y‖ ∧ ‖fderiv ℝ ψ y‖ ≤ (3/2 : ℝ)*‖ξ‖ := by
  obtain ⟨δ,hδ,hmargin⟩ :=
    exists_original_retained_graph_momentum_margin c hroot hprotect ha hmask htarget hε
  obtain ⟨η,hη,hadmit⟩ :=
    PhysicalInitialization.exists_reference_tolerance_for_physical_frame_admission
      ext hextcenter hextradius c.coefficientRadius_pos hδ
  refine ⟨η,hη,?_⟩
  intro G R hr hrR hR hreference Cband hband rStar kMin hStar horder
  obtain ⟨S,hS,hcurrent⟩ := hadmit G R hr hrR hR hreference hband rStar kMin hStar horder
  refine ⟨S,hS,?_⟩
  intro R₀ hR₀ s u ell hu Q e z h
  obtain ⟨hQ,hQrange,hQclose⟩ := hcurrent R₀ hR₀ s u ell hu
  refine ⟨hQ,hQrange,?_⟩
  exact hmargin Q hQ (hQclose (closedBall x RQ))

end JanetCartan.PhysicalPrimary.CharacteristicAdjointMomentum
