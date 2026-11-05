module
public import JanetCartan.Iteration.PhysicalPairs.OriginalTensorLag
public import JanetCartan.Iteration.PhysicalPairs.OriginalLagAlgebra
public import JanetCartan.Iteration.PhysicalPairs.OriginalCommonWaves

/-! # The original common-shift signed correction: the physical lag inequality

Starting only from the complete primary derivative profiles, use the actual
measured Neumann tail, the observed powers of the same operator, the tested
smooth pencil and normal reconstruction. The single constant is fixed before
R₀, the finite history, ξ, sign, and both nodes. No per-packet residual or
whole-product lag is a hypothesis. `app:ch_pairs:eq:pairs-lag-sum-error`,
`main:prop:pairs`.
-/
@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter
open scoped Topology
namespace JanetCartan.PhysicalPairs.OriginalStageLag
open UniformStep
variable {n : ℕ}
def accuracy (q : ℕ) : ℝ := q

def singlePrice (hn : 5 ≤ n) (A R : ℝ) (q : ℕ) : ℝ := projectedStressResidualConstant hn * A * (2:ℝ)^q * R^(-((carrierExponent-separationExponent)*(q:ℝ)))

def totalPrice (hn : 5 ≤ n) (A M : ℝ) (q : ℕ) : ℝ := 2*(projectedStressResidualConstant hn * A)*(2:ℝ)^q*max 0 M

theorem single_nonneg (hn : 5 ≤ n) (A R : ℝ) (q : ℕ) (hA : 0 ≤ A) (hR : 1 ≤ R) : 0 ≤ singlePrice hn A R q := by
  have hF := (projectedStressResidualConstant_pos hn).le
  have hr := zero_le_one.trans hR
  unfold singlePrice; positivity

theorem total_nonneg (hn : 5 ≤ n) (A M : ℝ) (q : ℕ) (hA : 0 ≤ A) : 0 ≤ totalPrice hn A M q := by
  have hF := (projectedStressResidualConstant_pos hn).le
  have hM := le_max_left 0 M
  unfold totalPrice; positivity

theorem single (hn : 5 ≤ n) (A R beat : ℝ) (q : ℕ) (w e : ℝ) (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hb : R^(-separationExponent)/2 ≤ beat) (hs : w ≤ projectedStressResidualConstant hn*e) (he : e ≤ A*(R^carrierExponent*beat)^(-accuracy q)) :
    w ≤ singlePrice hn A R q := by
  have hF := (projectedStressResidualConstant_pos hn).le
  calc
    w ≤ projectedStressResidualConstant hn*(A*(R^carrierExponent*beat)^(-accuracy q)) := hs.trans (mul_le_mul_of_nonneg_left he hF)
    _ ≤ projectedStressResidualConstant hn*(A*((2:ℝ)^q*R^(-((carrierExponent-separationExponent)*(q:ℝ))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (OriginalLagAlgebra.true_rate hR hb q) hA) hF
    _ = _ := by unfold singlePrice; ring

theorem total (hn : 5 ≤ n) (A M R δ : ℝ) (q : ℕ) (mass v : ℝ) (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hs : v ≤ 2*singlePrice hn A R q*(δ*R^(RevisedScales.forcingExponent n))^2*mass) (hm : mass ≤ M*R^(1+samplingSlack)) :
    v ≤ totalPrice hn A M q * δ^2 * R^(2*RevisedScales.forcingExponent n+1+samplingSlack-(carrierExponent-separationExponent)*(q:ℝ)) := by
  apply hs.trans
  exact OriginalLagAlgebra.total_price hR (mul_nonneg (projectedStressResidualConstant_pos hn).le hA) q
    (hm.trans (mul_le_mul_of_nonneg_right (le_max_right 0 M) (Real.rpow_nonneg (zero_le_one.trans hR) _)))

theorem plateau {m : ℕ} {η : Euclidean m → ℝ} {x : Euclidean m} (h : η =ᶠ[𝓝 x] fun _ ↦ 1) : η x = 1 := h.eq_of_nhds
end JanetCartan.PhysicalPairs.OriginalStageLag
end
public meta section
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.OriginalStageLag
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalStageLag
private def hs := `JanetCartan.PhysicalPairs.SampledHistory
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def cw := `JanetCartan.PhysicalPairs.OriginalCommonWaves
private def mass := `JanetCartan.PhysicalPairs.OriginalSampleMass
private def one := `JanetCartan.PhysicalPairs.OriginalTensorLag.strain_to_original_error
private def a (k : Name) (p : Array Expr) := mkAppN (mkConst k) p
private def part (h : Expr) (j : Nat) : Expr := Expr.proj ``And 0 (Nat.rec h (fun _ v => .proj ``And 1 v) j)
elab "assemble_actual_common_signed_lag " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hs ++ `index)).type (some 49) fun pt _ => do
    let b := pt[:37].toArray
    let stem := pt[:45].toArray
    let dyn := pt[37:45].toArray
    let signs := pt[45:].toArray
    let hn := pt[1]!
    let n := mkApp (mkConst ``Nat.succ) pt[0]!
    let M := a (mass ++ `constant) pt[:22].toArray
    let label := a (hs ++ `label) pt
    withLocalDeclD `commonWaves (a (cw ++ `Waves) b) fun W => do
      let original := mkAppN W dyn
      let w := a (cw ++ `onLabels) (b.push W)
      forallBoundedTelescope (← inferType (a (fm ++ `first_mask) (b.push w))) (some 3) fun profile _ => withLocalDeclD `accuracyOrder (mkConst ``Nat) fun q => do
        let fixed := b ++ #[W] ++ profile ++ #[q]
        let exp := a (ns ++ `accuracy) #[q]
        let rapid := a `JanetCartan.PhysicalPairs.OriginalCorrectedLag.pointwise (b ++ #[w] ++ profile ++ #[exp])
        let A ← mkAppM ``Classical.choose #[rapid]
        let spec ← mkAppM ``Classical.choose_spec #[rapid]
        let hA := Expr.proj ``And 0 spec
        let price := a (ns ++ `totalPrice) #[n,hn,A,M,q]
        if piece.getNat == 0 then
          discard <| store (ns ++ `constant) fixed price true
          return
        if piece.getNat == 1 then
          let pf := a (ns ++ `total_nonneg) #[n,hn,A,M,q,hA]
          discard <| store (ns ++ `constant_nonneg) fixed pf false (some ((← inferType pf).replace fun e => if e == price then some (a (ns ++ `constant) fixed) else none))
          return
        let width := (← inferType (a one b)).bindingDomain!
        withLocalDeclD `prehistoryFrameWidth width fun hγ => withLocalDeclD `δ (mkConst ``Real) fun δ => do
          let correction := a (sum ++ `correction) (stem ++ #[original,δ])
          let raw := ((← getConstInfo (sum ++ `correction)).value! (allowOpaque := true)).beta (stem ++ #[original,δ])
          unless raw.isAppOfArity (sum ++ `sum) 9 do throwError "not the common sampled correction"
          let sa := raw.getAppArgs
          let R := sa[7]!
          let μ := sa[8]!
          let index := ((← getConstInfo (hs ++ `index)).value! (allowOpaque := true)).beta pt
          unless index.isAppOfArity (hs ++ `enter) 15 do throwError "not the original graph+operator scale window"
          let both := index.getAppArgs[7]!
          let merged := (← inferType both).getAppArgs[2]!
          let ma := merged.getAppArgs
          let hG ← mkAppM ``le_trans #[← mkAppM ``le_max_left #[ma[ma.size-2]!,ma.back!],both]
          let now := pt[:36].toArray ++ #[pt[37]!,hG] ++ pt[39:43].toArray
          let F := Expr.proj ``Subtype 0 (a `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected now)
          let hR := a `JanetCartan.PhysicalPairs.OriginalWindow.stage_one #[pt[36]!,pt[37]!,index.getAppArgs[8]!,pt[39]!]
          let cert := a (hs ++ `native_window) pt
          let hb := part (part cert 1) 0
          let beat := (← inferType hb).appArg!
          let native := pt.push original
          let tensor := ((← getConstInfo `JanetCartan.PhysicalPairs.OriginalSignedPackets.tensor).value! (allowOpaque := true)).beta native
          let η := tensor.appArg!
          let angles ← mkLambdaFVars signs (a `JanetCartan.PhysicalPairs.OriginalSignedData.angles pt)
          let per := a one (b ++ #[hγ] ++ pt[37:].toArray ++ #[original])
          let g := (← inferType (a (hs ++ `index) pt)).getAppArgs
          let cutoffs := a `JanetCartan.RevisedUniform.OriginalCore.original_cutoffs g[:23].toArray
          let alg := a `JanetCartan.PhysicalPairs.OriginalLagAlgebra.sum_strain (sa[:5].toArray ++ #[F,sa[5]!,original])
          withLocalDeclD `completePrimaryAngles (← inferType alg).bindingDomain! fun θ => do
            let result ← forallBoundedTelescope (← inferType per) (some 2) fun y _ => do
              let hsx := mkAppN per y
              let hex := mkAppN (.proj ``And 1 spec) (#[label] ++ y)
              let wv := (← inferType hsx).getAppArgs[2]!
              let ev := (← inferType hex).getAppArgs[2]!
              let each := a (ns ++ `single) #[n,hn,A,R,beat,q,wv,ev,hA,hR,hb,hsx,hex]
              let hsingle ← mkLambdaFVars signs each
              let C := a (ns ++ `singlePrice) #[n,hn,A,R,q]
              let hC := a (ns ++ `single_nonneg) #[n,hn,A,R,q,hA,hR]
              let hη ← mkAppM (ns ++ `plateau) #[part (mkAppN cutoffs y) 2]
              let whole := mkAppN alg #[θ,angles,η,δ,R,μ,a (sum ++ `weight_nonneg) stem,y[0]!,hη,C,hC,hsingle]
              let hmass := part (a (mass ++ `coefficient_budgets) stem) 1
              let mv := (← inferType hmass).getAppArgs[2]!
              let wval := (← inferType whole).getAppArgs[2]!
              let pf := a (ns ++ `total) #[n,hn,A,M,R,δ,q,mv,wval,hA,hR,whole,hmass]
              mkLambdaFVars y pf
            let publicType := (← inferType result).replace fun e => if e == raw then some correction else if e == price then some (a (ns ++ `constant) fixed) else none
            discard <| store (ns ++ `lag) (b ++ #[hγ,W] ++ profile ++ #[q] ++ dyn ++ #[δ,θ]) result false (some publicType)
assemble_actual_common_signed_lag 0
assemble_actual_common_signed_lag 1
assemble_actual_common_signed_lag 2
end JanetCartan.PhysicalPairs.OriginalStageLag
end
