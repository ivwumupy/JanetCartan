module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedPackets

/-! # Local physical discrepancy for the original broad tensor

The original `χsrc` is NOT assumed supported inside the inverse norm ball.
Only restrict the zero extension of the uncut smooth datum to the genuine
`χ₂` inner ball, where the actual original smooth right equation holds. This
leaves exactly the complete real paired-source minus identity on the SAME
native corrected L² field. Consumer: `main:prop:pairs` full-strain lag bound.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory Filter
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius JanetCartan.TensorFrobenius SchwartzMap
namespace JanetCartan.PhysicalPairs.OriginalPacketEquation
open AmbientResponse CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension LocalSobolev SmallSupport
variable {n N : ℕ} {I : Type}
local notation "E" => Euclidean n

/-- The original source slot agrees with the actual broad signed stress on
any measurable subset of W; there is no inclusion of all its support in W. -/
theorem uncut_restricted (Z : I → SchwartzMap E (EuclideanSpace ℂ (Fin N)))
    (θ : I → E → ℝ) (minus : Bool) (i j : I) {U W : Set E} {η : E → ℝ} (hU : IsOpen U)
    (Q : E → Fin n → MetricTensor n) (hQ : ∀ k, ContDiffOn ℝ ∞ (fun x ↦ Q x k) U)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (hW : MeasurableSet W) {V : Set E} (hV : MeasurableSet V) (hVW : V ⊆ W) :
    zeroExtend hW (SampledInput.uncut (W := W) Z θ minus i j hU Q hQ hη hc hηU : LocalL2 W E)
      =ᵐ[volume.restrict V] fun y ↦ WithLp.toLp 2
        (stressSource Q (OriginalSignedPackets.originalTensor Z θ minus i j η) y) := by
  let v : LocalL2 W E := (SampledInput.uncut (W := W) Z θ minus i j hU Q hQ hη hc hηU).val
  have hg := cutoffStressSmoothSource_coeFn (W := W) Q (fun _ ↦ 1) hU hQ contDiff_const hηU
    ⟨_,SampledInput.tensor_admitted Z θ minus i j hη hc⟩
  filter_upwards [ae_restrict_of_ae (zeroExtend_coeFn hW v),ae_restrict_of_ae_restrict_of_subset hVW hg,ae_restrict_mem hV] with y he hv hy
  change zeroExtend hW v y = _
  rw [he,indicator_of_mem (hVW hy)]
  unfold OriginalSignedPackets.originalTensor
  simpa only [v,SampledInput.uncut,euclideanCutoffStressSource,cutoffSource,
    LinearMap.coe_mk,AddHom.coe_mk,one_smul] using hv

theorem inner_subset {c : E} (χ : ContDiffBump c) {W : Set E} (hs : tsupport (χ : E → ℝ) ⊆ W) : ball c χ.rIn ⊆ W := by
  intro y hy
  exact hs (subset_tsupport (χ : E → ℝ) (show χ y ≠ 0 by rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy)]; exact one_ne_zero))

theorem right_minus_original (V : Set E) (r u f a z : E → E) (hr : r =ᵐ[volume.restrict V] u+a-z)
    (hu : u =ᵐ[volume.restrict V] f) : (fun y ↦ r y - f y) =ᵐ[volume.restrict V] a-z := by
  filter_upwards [hr,hu] with x hx he
  rw [hx,← he]
  simp only [Pi.sub_apply,Pi.add_apply]
  abel
end JanetCartan.PhysicalPairs.OriginalPacketEquation
end

public meta section
set_option maxHeartbeats 800000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalPacketEquation
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalPacketEquation
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def src := `JanetCartan.PhysicalPairs.OriginalSignedData
private def pkt := `JanetCartan.PhysicalPairs.OriginalSignedPackets
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
elab "derive_original_packet_equation " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p gf => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let fixed := gf.getAppArgs[:23].toArray
    let χ := a (reg ++ `χ₂) fixed
    let c := (← inferType χ).appArg!
    let W := a (world ++ `W) fixed
    let hW := a (world ++ `W_measurable) fixed
    forallBoundedTelescope (← inferType (a (src ++ `uncut) p)) (some 1) fun ws _ => do
      let v := p ++ ws
      let uncut := a (src ++ `uncut) v
      let raw := ((← getConstInfo (src ++ `uncut)).value! (allowOpaque := true)).beta v
      let some smooth := (← inferType (a (src ++ `solver_representation) v)).find? (fun e => e.isAppOfArity (reg ++ `Current.smoothSolver) 38)
        | throwError "missing native smooth solver38"
      let weak := smooth.getAppArgs
      let right := mkApp (a (reg ++ `Current.fact22) weak) uncut
      let rt := (← inferType right).getAppArgs
      let filter := rt[2]!
      let some V := filter.find? (fun e => e.isAppOf `Metric.ball)
        | throwError "native right equation lost original inside ball"
      if piece.getNat == 0 then
        let hχ ← mkAppM `Set.Subset.trans #[a (mask ++ `χ₂_support_chart) fixed,a (reg ++ `hUW) fixed]
        let hsub := a (ns ++ `inner_subset) #[n,c,χ,W,hχ]
        let opn ← mkFreshExprMVar (← mkAppM ``IsOpen #[V])
        let rest ← opn.mvarId!.apply (← mkConstWithFreshMVarLevels ``Metric.isOpen_ball)
        unless rest.isEmpty do throwError "not the actual open core ball"
        let hm ← mkAppM ``IsOpen.measurableSet #[← instantiateMVars opn]
        let pf := a (ns ++ `uncut_restricted) (raw.getAppArgs ++ #[hW,V,hm,hsub])
        let target := (← inferType pf).replace fun e => if e == raw then some uncut else if e.isAppOfArity (pkt ++ `originalTensor) 9 then some (a (pkt ++ `tensor) v) else none
        discard <| store (ns ++ `uncut_on_original_core) v pf false (some target)
        return
      let hu := a (ns ++ `uncut_on_original_core) v
      let stress := (← inferType hu).appArg!
      let rhs := rt.back!
      unless rhs.isAppOf ``HSub.hSub do throwError "native right side is not the original source + corrected paired source - corrected source"
      let ab := rhs.getAppArgs
      let plus := ab[ab.size-2]!
      unless plus.isAppOf ``HAdd.hAdd do throwError "native right side lost original uncut source"
      let ux := plus.getAppArgs
      let pf := a (ns ++ `right_minus_original) #[n,V,rt[3]!,ux[ux.size-2]!,stress,ux.back!,ab.back!,right,hu]
      discard <| store (ns ++ `right_discrepancy) v pf
derive_original_packet_equation 0
derive_original_packet_equation 1
end JanetCartan.PhysicalPairs.OriginalPacketEquation
end
