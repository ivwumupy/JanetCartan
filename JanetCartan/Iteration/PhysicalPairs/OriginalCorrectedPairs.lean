module
public import JanetCartan.Iteration.PhysicalPairs.OriginalObservedPairs
public import JanetCartan.Iteration.PhysicalPairs.OriginalNeumannTail
public import JanetCartan.Iteration.PhysicalPairs.OriginalPacketEquation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedObservedResidual.CorrectedSourceTail

/-! # Angular decay of the SAME complete corrected original signed product

Observe on the unchanged original inner core `ball 0 χ₂.rIn`; `χ₃` is used
only as an auxiliary observation collar where it is already one. The source in
the physical correction operator is the UNCUT signed stress, so the original
correction contributes the existing measurement once, not twice. Both actual
finite chains and the actual unobserved inverse remainder are discharged.
Consumers: `app:ch_regular:eq:resolved-angular-tail`, `main:prop:pairs`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Metric
namespace JanetCartan.PhysicalPairs.OriginalCorrectedPairs

theorem inner_plateau {n : ℕ} {c : Euclidean n} (χ ψ : ContDiffBump c)
    (h : ∀ y ∈ tsupport (χ : Euclidean n → ℝ), ψ y = 1) : ∀ y ∈ ball c χ.rIn, ψ y = 1 := by
  intro y hy
  exact h y (subset_tsupport (χ : Euclidean n → ℝ) (show χ y ≠ 0 by rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy)]; exact one_ne_zero))
end JanetCartan.PhysicalPairs.OriginalCorrectedPairs
end
public meta section
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalCorrectedPairs
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalCorrectedPairs
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def sd := `JanetCartan.PhysicalPairs.OriginalSignedData
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def key := `JanetCartan.ArbitraryAccuracy.SelectedLocalization.normalized_correctedSource_angular_rapidDecayAt_of_original_remainder
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def down (h : Expr) : Nat → Expr | 0 => h | k+1 => down (.proj ``And 1 h) k
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (down h j)
private def beforeLets : Expr → Array Name
  | .forallE n _ body _ => #[n] ++ beforeLets body
  | .mdata _ e => beforeLets e
  | _ => #[]
elab "observe_actual_corrected_pairs" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (fm ++ `first_mask)).type (some 41) fun p _ => do
    let b := p[:37].toArray
    let z := p[:38].toArray
    let d := b[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let β := a (hist ++ `Labels) b
    let gf := (← inferType (a (hist ++ `historyMap) b)).bindingBody!
    let fix := gf.getAppArgs[:23].toArray
    let stat (k : Name) := a (reg ++ k) fix
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    let W := a (world ++ `W) fix
    let hW := a (world ++ `W_measurable) fix
    let E ← inferType fa[2]!
    let χ := stat `χ₂
    let ψ := stat `χ₃
    let r ← mkAppM `ContDiffBump.rIn #[χ]
    let V ← mkAppM `Metric.ball #[fa[2]!,r]
    let hV := a `JanetCartan.PhysicalInitialization.OriginalSampledObserved.native_norm_ball #[n,r]
    let hψW ← mkAppM `Set.Subset.trans #[a (masks ++ `χ₃_support_chart) fix,stat `hUW]
    let hχW ← mkAppM `Set.Subset.trans #[a (masks ++ `χ₂_support_chart) fix,stat `hUW]
    let χVW ← mkAppM `JanetCartan.PhysicalPairs.OriginalPacketEquation.inner_subset #[χ,hχW]
    let hχobsCore := a (ns ++ `inner_plateau) #[n,fa[2]!,χ,ψ,a (masks ++ `χ₃_on_χ₂) fix]
    let hob := a `JanetCartan.PhysicalInitialization.OriginalSampledObserved.bounded_mask #[E,stat `output,stat `fact18]
    let measured := ((← getConstInfo (fm ++ `measured)).value! (allowOpaque := true)).beta z
    lambdaBoundedTelescope measured 1 fun label row => do
      let t := label[0]!
      let rv := row.getAppArgs
      let pt := rv[:49].toArray
      let hi := a (hist ++ `measured_history) pt
      let now := pt[:36].toArray ++ #[pt[37]!,part hi 0] ++ pt[39:43].toArray
      let current := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected).value! (allowOpaque := true)).beta now
      unless current.isAppOfArity (reg ++ `Current.projected) 38 do throwError "corrected observation lost native current"
      let cur (k : Name) := a (reg ++ `Current ++ k) current.getAppArgs
      let fam (x : Expr) := mkLambdaFVars label x
      let unc ← mkAppM ``Subtype.val #[a (sd ++ `uncut) rv]
      let coeff := #[n] ++ fix[1:21].toArray
      let window := part (a (hist ++ `native_window) pt) 0
      let ρ := a (fm ++ `frequency) b
      let one ← mkNumeral (mkConst ``Real) 1
      let hA ← mkAppOptM `zero_le_one #[some (mkConst ``Real),none,none,none,none]
      let plus ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
      withLocalDeclD `observationOrder (mkConst ``Nat) fun s => do
        let args : Array (Name × Expr) := #[(`d,d),(`ι,β),(`Ω,fa[1]!),(`center,fa[2]!),(`RQ,fa[3]!),(`A₀,fa[4]!),(`K,fa[5]!),(`M,fa[6]!),
          (`f,f),(`hK,a `JanetCartan.PhysicalInitialization.OriginalProtected.fact14 coeff),(`L₀,stat `L),(`hL₀,stat `hL),
          (`Q,← fam (cur `Q)),(`B,← fam (cur `B)),(`W₁,← fam (cur `W₁)),(`retarded,← fam (mkApp (cur `retarded) plus)),
          (`output,stat `output),(`ho,stat `fact17),(`hoc,stat `fact19),(`hob,hob),(`D,W),(`hD,hW),(`rLp,(← inferType (stat `hrU)).appArg!),
          (`hrLp,stat `hrU),(`hball,stat `hUW),(`hmem,← fam (cur `hmem)),(`budget,(← inferType (stat `hbudget)).appArg!),(`hbudget,stat `hbudget),(`hbound,← fam (cur `hbound)),
          (`χ₂,χ),(`χ₃,ψ),(`χobs,ψ),(`hχ₂ball,stat `fact42),(`hnest,a (masks ++ `χ₃_on_χ₂) fix),(`hχ₃D,hψW),(`Vobs,W),(`Wcore,V),(`hVobs,hW),(`hWcore,hV),
          (`hχobsV,hψW),(`hWV,χVW),(`hχobsCore,hχobsCore),(`ρ,ρ),(`A,← fam one),(`hρ,← fam (a (fm ++ `one_of_two) #[mkApp ρ t,part window 2])),(`hA,← fam hA),(`s,s),(`h,← fam unc)]
        let info ← getConstInfo key
        let names := beforeLets info.type
        unless names.back! == `h do throwError "changed original corrected-remainder telescope: {names}"
        let fields ← names.mapM fun k => do
          let some (_,x) := args.find? (·.1 == k) | throwError "unsupplied original corrected-source coordinate {k}"
          pure x
        let hK ← fam (← mkAppM `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.lt_one_of_half_bound #[cur `fact6])
        let chains := mkApp (a `JanetCartan.PhysicalPairs.OriginalObservedPairs.observed_powers (p ++ #[W,hW])) s
        let remainder := a `JanetCartan.PhysicalPairs.OriginalNeumannTail.unobserved_remainder (p.push s)
        let pf := mkAppN (mkConst key (info.levelParams.map fun _ => .zero)) (fields ++ #[hK,chains,remainder])
        discard <| store (ns ++ `corrected_rapid) (p.push s) pf
observe_actual_corrected_pairs
end JanetCartan.PhysicalPairs.OriginalCorrectedPairs
end
