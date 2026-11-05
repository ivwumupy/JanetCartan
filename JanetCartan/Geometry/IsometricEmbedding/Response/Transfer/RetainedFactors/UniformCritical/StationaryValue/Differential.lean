module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.ConicEikonal
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.UniformCritical.SignedCarriers

/-!
# The elapsed-time differential at a retained stationary point

For both literal orientations of `app:ch_response:eq:response-exact-phase`,
derive the vanishing elapsed-time derivative from the stationary equations
and the SAME retained root and chart. These pointwise identities feed the
uniform stationary-value theorem and both integrated-envelope endpoints of
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.ResponseTransfer.RetainedFactors
open RegularSector.Characteristic ConicPhase EvolutionIntegral DirectEvolution
open ArbitraryAccuracy
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => Euclidean d
local notation "TC" => TwoTimePoint V
local notation "W" => CarrierVariables (d + 1)

private theorem twoTime_fderiv_apply {F : TC → ℝ} {q : TC}
    (hf : DifferentiableAt ℝ F q) (v : TC) :
    fderiv ℝ F q v =
      deriv (fun t ↦ F (t, q.2)) q.1 * v.1 +
      deriv (fun s ↦ F (q.1, (s, q.2.2))) q.2.1 * v.2.1 +
      inner ℝ (gradient (fun y ↦ F (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1) v.2.2.1 +
      inner ℝ (gradient (fun η ↦ F (q.1, (q.2.1, (q.2.2.1, η)))) q.2.2.2) v.2.2.2 := by
  let L := fderiv ℝ F q
  have ht := (hf.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))).deriv
  have hs := (hf.hasFDerivAt.comp_hasDerivAt q.2.1
    ((hasDerivAt_const q.2.1 q.1).prodMk
      ((hasDerivAt_id q.2.1).prodMk (hasDerivAt_const q.2.1 q.2.2)))).deriv
  have hy := (hf.hasFDerivAt.comp (f := fun y : V ↦ (q.1, (q.2.1, (y, q.2.2.2)))) q.2.2.1
    ((hasFDerivAt_const q.1 q.2.2.1).prodMk
      ((hasFDerivAt_const q.2.1 q.2.2.1).prodMk
        ((hasFDerivAt_id q.2.2.1).prodMk (hasFDerivAt_const q.2.2.2 q.2.2.1))))).fderiv
  have hη := (hf.hasFDerivAt.comp (f := fun η : V ↦ (q.1, (q.2.1, (q.2.2.1, η)))) q.2.2.2
    ((hasFDerivAt_const q.1 q.2.2.2).prodMk
      ((hasFDerivAt_const q.2.1 q.2.2.2).prodMk
        ((hasFDerivAt_const q.2.2.1 q.2.2.2).prodMk (hasFDerivAt_id q.2.2.2))))).fderiv
  simp only [Function.comp_def, id_eq] at ht hs hy hη
  rw [inner_gradient_left, inner_gradient_left, hy, hη, ht, hs]
  change L v = L (1, 0) * v.1 + L (0, (1, 0)) * v.2.1 +
    L (0, (0, (v.2.2.1, 0))) + L (0, (0, (0, v.2.2.2)))
  have he : v = v.1 • (1, (0 : RootState V)) + v.2.1 • (0, (1, (0 : V × V))) +
      (0, (0, (v.2.2.1, 0))) + (0, (0, (0, v.2.2.2))) := by ext <;> simp
  conv_lhs => rw [he, map_add, map_add, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

private theorem carrier_fderiv_apply
    (adj : Bool) (ℓ : V →L[ℝ] ℝ) (C : OpenPartialHomeomorph TC TC)
    (φ : E → Euclidean 3 → ℝ) (t : ℝ) (q : E × Euclidean 3) (w v : W)
    (hF : DifferentiableAt ℝ (phase ℓ C) (carrierGraphPoint adj ((t, q), w)))
    (hφ : DifferentiableAt ℝ (fun y ↦ φ y q.2) w.fst) :
    fderiv ℝ (fun u ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((t, q), u)) w v =
    (if adj then
      inner ℝ q.1 v.snd -
        (v.fst 0 * w.snd 0 + (w.fst 0 - t) * v.snd 0 +
          fderiv ℝ (phase ℓ C) (carrierGraphPoint adj ((t, q), w))
            (v.fst 0, (v.fst 0, (spatialPart v.fst, spatialPart v.snd))))
    else
      (q.1 0 - t) * v.snd 0 +
        fderiv ℝ (phase ℓ C) (carrierGraphPoint adj ((t, q), w))
          (0, (0, (0, spatialPart v.snd))) -
        (inner ℝ v.fst w.snd + inner ℝ w.fst v.snd)) +
      inner ℝ (gradient (fun y ↦ φ y q.2) w.fst) v.fst := by
  have hy := (WithLp.fstL 2 ℝ E E).hasFDerivAt (x := w)
  have hθ := (WithLp.sndL 2 ℝ E E).hasFDerivAt (x := w)
  have hy0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt.comp w hy
  have hθ0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d + 1))).hasFDerivAt.comp w hθ
  have hys := spatialPartCLM.hasFDerivAt.comp w hy
  have hθs := spatialPartCLM.hasFDerivAt.comp w hθ
  have hp := hφ.hasFDerivAt.comp w hy
  cases adj
  · have hg := (hasFDerivAt_const (q.1 0) w).prodMk
      ((hasFDerivAt_const (q.1 0 - t) w).prodMk
        ((hasFDerivAt_const (spatialPart q.1) w).prodMk hθs))
    have hd := (((((hasFDerivAt_const (q.1 0 - t) w).mul hθ0).add
      (hF.hasFDerivAt.comp w hg)).sub (hy.inner ℝ hθ)).add hp).sub_const (φ q.1 q.2)
    have he := congrArg (fun L : W →L[ℝ] ℝ ↦ L v) hd.fderiv
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, smul_apply, jointRetainedCarrierPhase,
      Bool.false_eq_true, ↓reduceIte,
      elapsedCarrierPhase, carrierPhase, elapsedPhase, curriedPhase,
      Function.comp_def, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply,
      WithLp.fstL_apply, WithLp.sndL_apply,
      PiLp.proj_apply, spatialPartCLM_apply, fderivInnerCLM_apply,
      smul_eq_mul, inner_gradient_left, carrierGraphPoint] at he ⊢
    convert he using 1
    ring
  · have hg := hy0.prodMk ((hy0.sub_const t).prodMk (hys.prodMk hθs))
    have hd := ((((hasFDerivAt_const q.1 w).inner ℝ hθ).sub
      (((hy0.sub_const t).mul hθ0).add (hF.hasFDerivAt.comp w hg))).add hp).sub_const
        (φ q.1 q.2)
    have he := congrArg (fun L : W →L[ℝ] ℝ ↦ L v) hd.fderiv
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, smul_apply, jointRetainedCarrierPhase,
      ↓reduceIte, CompactTransfer.adjointCarrierPhase,
      elapsedPhase, curriedPhase, Function.comp_def, add_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      zero_apply,
      WithLp.fstL_apply, WithLp.sndL_apply, PiLp.proj_apply, spatialPartCLM_apply,
      fderivInnerCLM_apply, inner_zero_left, smul_eq_mul,
      inner_gradient_left, carrierGraphPoint, add_zero] at he ⊢
    convert he using 1
    ring

private theorem carrier_hasDerivAt_time
    (adj : Bool) (ℓ : V →L[ℝ] ℝ) (C : OpenPartialHomeomorph TC TC)
    (φ : E → Euclidean 3 → ℝ) (t : ℝ) (q : E × Euclidean 3) (w : W)
    (hF : DifferentiableAt ℝ (phase ℓ C) (carrierGraphPoint adj ((t, q), w))) :
    HasDerivAt (fun s ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((s, q), w))
      (let b := carrierGraphPoint adj ((t, q), w)
       let B := deriv (fun s ↦ phase ℓ C (b.1, (s, b.2.2))) b.2.1
       if adj then w.snd 0 + B else -w.snd 0 - B) t := by
  let x := if adj then w.fst else q.1
  have hg := (hasDerivAt_const t (x 0)).prodMk
    (((hasDerivAt_id t).const_sub (x 0)).prodMk
      (hasDerivAt_const t (spatialPart x, spatialPart w.snd)))
  have hd := hF.hasFDerivAt.comp_hasDerivAt t hg
  have hv : fderiv ℝ (phase ℓ C) (carrierGraphPoint adj ((t, q), w))
      (0, (-1, (0, 0))) =
      -deriv (fun s ↦ phase ℓ C (x 0, (s, (spatialPart x, spatialPart w.snd))))
        (x 0 - t) := by
    rw [twoTime_fderiv_apply hF]
    simp [carrierGraphPoint, x]
  change HasDerivAt _ (fderiv ℝ (phase ℓ C) (carrierGraphPoint adj ((t, q), w))
    (0, (-1, (0, 0)))) t at hd
  rw [hv] at hd
  have hp := ((hasDerivAt_id t).const_sub (x 0)).mul_const (w.snd 0)
  cases adj
  · convert (((hp.add hd).sub_const (inner ℝ w.fst w.snd)).add_const
      (φ w.fst q.2)).sub_const (φ q.1 q.2) using 1 <;>
      simp [jointRetainedCarrierPhase, elapsedCarrierPhase, carrierPhase,
        elapsedPhase, curriedPhase, carrierGraphPoint, x, Function.comp_def]
    ring
  · convert (((hp.add hd).const_sub (inner ℝ q.1 w.snd)).add_const
      (φ w.fst q.2)).sub_const (φ q.1 q.2) using 1 <;>
      simp [jointRetainedCarrierPhase, CompactTransfer.adjointCarrierPhase,
        elapsedPhase, curriedPhase, carrierGraphPoint, x, Function.comp_def]
    ring

private theorem stationary_time_coefficient
    (adj : Bool) (ℓ : V →L[ℝ] ℝ) (C : OpenPartialHomeomorph TC TC)
    (φ : E → Euclidean 3 → ℝ) (h : RootState V → ℝ)
    (t : ℝ) (q : E × Euclidean 3) (w : W)
    (hF : DifferentiableAt ℝ (phase ℓ C) (carrierGraphPoint adj ((t, q), w)))
    (hφ : DifferentiableAt ℝ (fun y ↦ φ y q.2) w.fst)
    (he : rootSuspension h (w.fst, gradient (fun y ↦ φ y q.2) w.fst) = 0)
    (hHJ : let b := carrierGraphPoint adj ((t, q), w)
      deriv (fun s ↦ phase ℓ C (s, b.2)) b.1 =
        h (b.1, (b.2.2.1, gradient (fun y ↦ phase ℓ C (b.1, (b.2.1, (y, b.2.2.2)))) b.2.2.1)) ∧
      -deriv (fun s ↦ phase ℓ C (b.1, (s, b.2.2))) b.2.1 =
        h (b.2.1, (gradient (fun η ↦ phase ℓ C (b.1, (b.2.1, (b.2.2.1, η)))) b.2.2.2, b.2.2.2)))
    (hstat : gradient (fun u ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((t, q), u)) w = 0) :
    let b := carrierGraphPoint adj ((t, q), w)
    w.snd 0 + deriv (fun s ↦ phase ℓ C (b.1, (s, b.2.2))) b.2.1 = 0 := by
  let b := carrierGraphPoint adj ((t, q), w)
  let A := deriv (fun s ↦ phase ℓ C (s, b.2)) b.1
  let B := deriv (fun s ↦ phase ℓ C (b.1, (s, b.2.2))) b.2.1
  let P := gradient (fun y ↦ phase ℓ C (b.1, (b.2.1, (y, b.2.2.2)))) b.2.2.1
  let Y := gradient (fun η ↦ phase ℓ C (b.1, (b.2.1, (b.2.2.1, η)))) b.2.2.2
  let g := gradient (fun y ↦ φ y q.2) w.fst
  have hzero : fderiv ℝ (fun u ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ
      ((t, q), u)) w = 0 := by
    have hh := congrArg (InnerProductSpace.toDual ℝ W) hstat
    simpa [gradient] using hh
  have hv (v : W) := (carrier_fderiv_apply adj ℓ C φ t q w v hF hφ).symm.trans
    (show fderiv ℝ (fun u ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ
      ((t, q), u)) w v = 0 by rw [hzero]; rfl)
  have hd (v : TC) : fderiv ℝ (phase ℓ C) b v =
      A * v.1 + B * v.2.1 + inner ℝ P v.2.2.1 + inner ℝ Y v.2.2.2 :=
    twoTime_fderiv_apply hF v
  dsimp only [b] at hd
  change g 0 - h (w.fst 0, (spatialPart w.fst, spatialPart g)) = 0 at he
  have hspzero : spatialPart (0 : E) = 0 := map_zero spatialPartCLM
  change w.snd 0 + B = 0
  cases adj
  · have hθ : g = w.snd := by
      apply ext_inner_right ℝ
      intro v
      have hh := hv (WithLp.toLp 2 (v, 0))
      simp [hd, hspzero, -inner_gradient_left] at hh
      rw [real_inner_comm w.snd v] at hh
      linarith
    have ht : w.fst 0 = q.1 0 - t := by
      have hh := hv (WithLp.toLp 2 (0, KernelIdentification.timeSpacePoint 1 (0 : V)))
      simp [hd, inner_eq_time_add_spatial, -inner_gradient_left] at hh
      linarith
    have hy : spatialPart w.fst = Y := by
      apply ext_inner_right ℝ
      intro v
      have hh := hv (WithLp.toLp 2 (0, KernelIdentification.timeSpacePoint 0 v))
      simp [hd, inner_eq_time_add_spatial, -inner_gradient_left] at hh
      linarith
    have hroot : -B = h (w.fst 0, (spatialPart w.fst, spatialPart w.snd)) := by
      have hr : -B = h (q.1 0 - t, (Y, spatialPart w.snd)) := hHJ.2
      rwa [← ht, ← hy] at hr
    rw [hθ] at he
    linarith
  · have ht : g 0 = w.snd 0 + A + B := by
      have hh := hv (WithLp.toLp 2 (KernelIdentification.timeSpacePoint 1 (0 : V), 0))
      simp [hd, hspzero, inner_eq_time_add_spatial, -inner_gradient_left] at hh
      linarith
    have hy : spatialPart g = P := by
      apply ext_inner_right ℝ
      intro v
      have hh := hv (WithLp.toLp 2 (KernelIdentification.timeSpacePoint 0 v, 0))
      simp [hd, hspzero, inner_eq_time_add_spatial, -inner_gradient_left] at hh
      linarith
    have hroot : A = h (w.fst 0, (spatialPart w.fst, spatialPart g)) := by
      have hr : A = h (w.fst 0, (spatialPart w.fst, P)) := hHJ.1
      rwa [← hy] at hr
    linarith

/-- Stationarity and the primary root equation force the elapsed-time derivative
of either literal retained conic carrier to vanish. Both Hamilton--Jacobi
identities are derived from the original chart/root witnesses by
`retained_conic_eikonal_identities`. Consumer: constancy along the uniform
stationary branches in `app:ch_response:eq:response-exact-phase` and the
zero-value input of `app:ch_response:eq:direct-envelope-profile`. -/
theorem retained_conic_stationary_hasDerivAt_zero
    (adj : Bool) (ℓ : V →L[ℝ] ℝ) {h : RootState V → ℝ} {D : Set (RootState V)}
    (hhom : ∀ w ∈ D, ∀ s : ℝ, 0 < s → h (w.1, (w.2.1, s • w.2.2)) = s * h w)
    {Φ : RootState V × ℝ → RootState V} {C : OpenPartialHomeomorph TC TC}
    {z : RootState V} {a L : ℝ}
    (hC : (C : TC → TC) = twoTimeProjection Φ)
    (hsource : C.source = ball (z.1, z) a) (haL : a ≤ L)
    (hLD : closedBall z L ⊆ D)
    (hstate : ∀ b ∈ C.target, twoTimeState Φ (C.symm b) ∈ D ∧
      (twoTimeState Φ (C.symm b)).1 = b.1)
    (hCsm : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hphase : ∀ b ∈ C.target, HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C b) b)
    (φ : E → Euclidean 3 → ℝ) {t : ℝ} {q : E × Euclidean 3} {w : W}
    (hgraph : carrierGraphPoint adj ((t, q), w) ∈ domain ℓ C.target)
    (hφ : DifferentiableAt ℝ (fun y ↦ φ y q.2) w.fst)
    (he : rootSuspension h (w.fst, gradient (fun y ↦ φ y q.2) w.fst) = 0)
    (hstat : gradient (fun u ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ
      ((t, q), u)) w = 0) :
    HasDerivAt (fun s ↦ jointRetainedCarrierPhase adj (curriedPhase ℓ C) φ ((s, q), w)) 0 t := by
  have hF := ((contDiffOn_phase ℓ hCsm).contDiffAt
    ((isOpen_domain ℓ C.open_target).mem_nhds hgraph)).differentiableAt (by simp)
  have hHJ := retained_conic_eikonal_identities ℓ hhom hC hsource haL hLD hstate hphase hgraph
  have hz := stationary_time_coefficient adj ℓ C φ h t q w hF hφ he hHJ hstat
  have hd := carrier_hasDerivAt_time adj ℓ C φ t q w hF
  convert hd using 1
  cases adj <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    dsimp only at hz ⊢ <;> linarith

end JanetCartan.ResponseTransfer.RetainedFactors
