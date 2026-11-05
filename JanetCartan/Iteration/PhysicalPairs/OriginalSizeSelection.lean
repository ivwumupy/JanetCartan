module
public import JanetCartan.Iteration.PhysicalPairs.LocalHistorySize
public import JanetCartan.Iteration.PhysicalPairs.OriginalSizeSupport
public import JanetCartan.Iteration.PhysicalPairs.OriginalSizeFrequency

/-! # Select the physical size threshold on the original reference

This is a second, honest finite-order coefficient estimate on the SAME F,Q,B.
Its reserve is sectorLowOrder d + (d+2), not the smaller reserve of the
original finite signed graph. Choose the numerical history cap accordingly,
then merge the existing size theorem's threshold with the original signed
threshold. Its full all-order profile precedes every sample and history.
`main:prop:current-scale`, `app:ch_pairs:eq:pairs-lag-sum-size`.
-/
@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
open Set Metric
namespace JanetCartan.PhysicalPairs.OriginalSizeSelection
open RegularSector.FiniteEvolution

def reserve (d : ℕ) : ℕ := sectorLowOrder d + (d+2)
def historyCap (d earlier : ℕ) : ℕ := max earlier (2+reserve d)
theorem covers_size (d earlier : ℕ) : 2+reserve d ≤ historyCap d earlier := le_max_right _ _
theorem covers_earlier (d earlier : ℕ) : earlier ≤ historyCap d earlier := le_max_left _ _

def profileRadius (r b : ℝ) := max (r+1) b
theorem buffer (r b : ℝ) : r < profileRadius r b := (lt_add_one _).trans_le (le_max_left _ _)
theorem in_profile {n : ℕ} {U : Set (Euclidean n)} {b : ℝ} (r : ℝ) (h : U ⊆ ball 0 b) : U ⊆ ball 0 (profileRadius r b) := h.trans (ball_subset_ball (le_max_right _ _))
end JanetCartan.PhysicalPairs.OriginalSizeSelection
end
public meta section
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalSizeSelection
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSizeSelection
private def hs := `JanetCartan.PhysicalPairs.SampledHistory
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def sup := `JanetCartan.PhysicalPairs.OriginalSizeSupport
private def fq := `JanetCartan.PhysicalPairs.OriginalSizeFrequency
private def key := `JanetCartan.PhysicalPairs.exists_physical_history_localized_normalized_product_size_constants
private def a (k : Name) (v : Array Expr) := mkAppN (mkConst k) v
private def binders : Expr → Array Name
  | .forallE n _ t _ => #[n] ++ binders t
  | .mdata _ e => binders e
  | _ => #[]
elab "select_true_original_size " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hs ++ `Labels)).type (some 37) fun b _ => do
    let d := b[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let gf := (← inferType (a (hs ++ `historyMap) b)).bindingBody!
    let fix := gf.getAppArgs[:23].toArray
    let regp (k : Name) := a (reg ++ k) fix
    let m (k : Name) := a (mask ++ k) fix
    let rawFam := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily).value! (allowOpaque := true)).beta gf.getAppArgs
    let coeff := rawFam.getAppArgs.back!.getAppArgs
    let op := ((← getConstInfo `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles.exists_profiles).value! (allowOpaque := true)).beta coeff
    unless op.isAppOfArity `JanetCartan.PhysicalGeometry.exists_retained_coefficient_profiles 18 do throwError "not the same original physical reference and history"
    let ca := op.getAppArgs
    let β := a (ns ++ `reserve) #[d]
    let cap := mkApp2 (mkConst ``Nat.add) (mkNatLit 2) β
    withLocalDeclD `historyCapForSize (← mkAppM ``LE.le #[cap,ca[12]!]) fun hcap => do
      let ct ← mkArrow (mkConst ``Nat) (mkConst ``Real)
      withLocalDeclD `primaryProfile ct fun C => do
        let zero ← mkNumeral (mkConst ``Real) 0
        let hcTy ← withLocalDeclD `k (mkConst ``Nat) fun k => do mkForallFVars #[k] (← mkAppM ``LE.le #[zero,mkApp C k])
        withLocalDeclD `primaryProfile_nonneg hcTy fun hC => do
          let p := b ++ #[hcap,C,hC]
          if piece.getNat == 0 then
            let f := regp `f
            let fa := (← inferType f).getAppArgs
            let E ← inferType fa[2]!
            let χ := a (sup ++ `factor) fix
            let ψ := (← inferType (m `χ₃_smooth)).appArg!
            let hψr ← mkAppM ``Set.Subset.trans #[m `χ₃_support_chart,m `chart_in_coefficient_ball]
            let orig := #[n] ++ fix[1:21].toArray
            let hK := a `JanetCartan.PhysicalInitialization.OriginalProtected.fact14 orig
            let hob := a `JanetCartan.PhysicalInitialization.OriginalSampledObserved.bounded_mask #[E,regp `output,regp `fact18]
            let rad := regp `normRadius
            let D := a `JanetCartan.PhysicalPairs.OriginalSignedFrames.jointProfile b[:36].toArray
            let hr := a `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Native.norm_radius_pos fix
            let one ← mkNumeral (mkConst ``Real) 1
            let η ← withLocalDeclD `point E fun x => mkLambdaFVars #[x] one
            let args : Array (Name × Expr) := #[(`d,d),(`ι,mkApp (mkConst ``Fin) (mkNatLit 2)),(`Ω,fa[1]!),(`center,fa[2]!),(`RQ,fa[3]!),(`A₀,fa[4]!),(`K,fa[5]!),(`M,fa[6]!),
              (`Gref,ca[1]!),(`r,ca[2]!),(`R,ca[3]!),(`hr,ca[4]!),(`hrR,ca[5]!),(`hR,ca[6]!),(`ext,ca[7]!),(`hextcenter,ca[8]!),(`hextradius,ca[9]!),
              (`Cband,ca[10]!),(`hCband,ca[11]!),(`rStar,ca[12]!),(`reserve,β),(`kMin,ca[14]!),(`hStar,ca[15]!),(`hreserve,hcap),(`hlowReserve,← mkAppM ``le_refl #[β]),(`horder,ca[17]!),
              (`f,f),(`hK,hK),(`L₀,regp `L),(`output,regp `output),(`ho,← mkAppM ``ContDiff.continuous #[regp `fact17]),(`hob,hob),(`χ₂,regp `χ₂),(`χ₃,regp `χ₃),
              (`ψ,ψ),(`hψ,m `χ₃_smooth),(`hψc,m `χ₃_compact),(`hψr,hψr),(`normRadius,rad),(`profileRadius,a (ns ++ `profileRadius) #[rad,ca[2]!]),(`hnorm,hr),(`hbuffer,a (ns ++ `buffer) #[rad,ca[2]!]),
              (`S,← mkAppM ``tsupport #[χ]),(`hS,a (sup ++ `compact) fix),(`P,a (fq ++ `phasePrice) #[D]),(`X,a (sup ++ `jetCost) #[n,ca[2]!,χ]),(`Y,a (sup ++ `jetCost) #[n,ca[2]!,η]),
              (`C,C),(`responseCost,regp `responseCost),(`hP,a (fq ++ `phasePrice_nonneg) #[D,a `JanetCartan.PhysicalPairs.OriginalSignedFrames.jointProfile_nonneg b[:36].toArray]),
              (`hX,a (sup ++ `jetCost_nonneg) #[n,ca[2]!,χ]),(`hY,a (sup ++ `jetCost_nonneg) #[n,ca[2]!,η]),(`hC,hC),(`hresponseCost,regp `fact52),
              (`Cfreq,a (fq ++ `constant) b[:22].toArray),(`hCfreq,a (fq ++ `constant_nonneg) b[:22].toArray)]
            let info ← getConstInfo key
            let mut xs := #[]
            for nm in binders info.type do
              let some (_,term) := args.find? (fun nv => nv.1 == nm) | throwError "unpriced size operand {nm}"
              xs := xs.push term
            let pf := mkAppN (mkConst key [.zero]) xs
            discard <| store (ns ++ `native_budget) p pf
            return
          let ex := a (ns ++ `native_budget) p
          if piece.getNat == 1 then
            let t ← store (ns ++ `threshold) p (← mkAppM ``Classical.choose #[ex]) true
            let spec ← store (ns ++ `spec) p (← mkAppM ``Classical.choose_spec #[ex]) false (some ((← inferType ex).appArg!.beta #[t]))
            discard <| store (ns ++ `threshold_ge_two) p (.proj ``And 0 spec)
            return
          let spec := a (ns ++ `spec) p
          let exD := Expr.proj ``And 1 spec
          if piece.getNat == 2 then
            let D ← store (ns ++ `D) p (← mkAppM ``Classical.choose #[exD]) true
            let Ds ← store (ns ++ `Dspec) p (← mkAppM ``Classical.choose_spec #[exD]) false (some ((← inferType exD).appArg!.beta #[D]))
            discard <| store (ns ++ `D_nonneg) p (.proj ``And 0 Ds)
            discard <| store (ns ++ `continuation) p (.proj ``And 1 Ds)
            return
          let t := a (ns ++ `threshold) p
          let old := a (hs ++ `S) b
          let S ← store (ns ++ `S) p (← mkAppM ``Max.max #[old,t]) true
          let oldLe ← mkAppM ``le_max_left #[old,t]
          let newLe ← mkAppM ``le_max_right #[old,t]
          discard <| store (ns ++ `reaches_signed) p oldLe false (some (← mkAppM ``LE.le #[old,S]))
          discard <| store (ns ++ `reaches_size) p newLe false (some (← mkAppM ``LE.le #[t,S]))
          discard <| store (ns ++ `hS) p (← mkAppM ``le_trans #[a (ns ++ `threshold_ge_two) p,newLe]) false (some (← mkAppM ``LE.le #[(← inferType (a (ns ++ `threshold_ge_two) p)).getAppArgs[2]!,S]))
select_true_original_size 0
select_true_original_size 1
select_true_original_size 2
select_true_original_size 3
end JanetCartan.PhysicalPairs.OriginalSizeSelection
end
