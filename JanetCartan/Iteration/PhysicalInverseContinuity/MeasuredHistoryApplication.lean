module

public meta import JanetCartan.Iteration.PhysicalInverseContinuity.DatumApplication

/-! Kernel-checked composition with the same prefix bound, finite mean,
measured residual, and uncorrected current operator. No moving residual or
right-inverse convergence certificate is accepted as an input. -/

public meta section
namespace JanetCartan.PhysicalInverseContinuity.MeasuredHistoryApplication
open Lean Meta Elab Command Term
open DatumApplication

private def rawHist := `JanetCartan.PhysicalInverseContinuity.StrongRaw.History
private def rawSource := `JanetCartan.PhysicalNormalInverse.StrongSource

private def term (s : String) (expected : Option Expr := none) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term s |
    throwError "measured history: invalid term {s}"
  Term.withoutErrToSorry do
    let t ← elabTermEnsuringType stx expected
    synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars t
    if t.hasMVar || t.hasLevelMVar || t.hasSorry then throwError "measured history: unresolved term {s}"
    return t

private partial def aliases (b : List (Name × Expr)) (k : TermElabM Expr) : TermElabM Expr := do
  match b with
  | [] => k
  | (n, v) :: b => withLetDecl n (← inferType v) v fun x => do
    return (← aliases b k).replaceFVar x v

private def chooseParts (dataName specName posName continuationName : Name) (params : Array Expr)
    (p : Expr) : TermElabM (Expr × Expr × Expr) := do
  let δ ← store (`History ++ dataName) params (← mkAppM ``Classical.choose #[p]) true
  let t := (← whnf (← inferType p)).appArg!.beta #[δ]
  let spec ← store (`History ++ specName) params (← mkAppM ``Classical.choose_spec #[p]) false (some t)
  let hδ ← store (`History ++ posName) params (← mkAppM ``And.left #[spec])
  let next ← store (`History ++ continuationName) params (← mkAppM ``And.right #[spec])
  return (δ, hδ, next)

/-- Get the measured-data finite-neighborhood frequency and close the three
remaining input estimates of the raw inverse comparison on the same history.
The actual current inverse hypotheses are exactly native row output clauses
of the physical inverse producer and are kept in their original form. -/
elab "apply_actual_measured_source_to_history" : command => liftTermElabM do
  let info ← getConstInfo (rawSource ++ `exists_history_coercivity)
  forallBoundedTelescope info.type (some 29) fun source _ => do
    let fixed := source[:23].toArray
    let head := mkAppN (mkConst (datumNS ++ `reference)) fixed
    forallBoundedTelescope (← inferType head) (some 6) fun masks _ => do
      unless masks.size == 6 do throwError "measured history: expected mask, three proofs and fixed tangent field with smoothness"
      let datum := fixed ++ masks
      let e₀ := mkAppN (mkConst (datumNS ++ `reference)) datum
      let mem := mkAppN (mkConst (datumNS ++ `reference_mem)) datum
      let settings := mkAppN (mkConst (rawHist ++ `S)) source
      forallBoundedTelescope (← inferType settings) (some 6) fun budget _ => do
        let m := budget[0]!
        let s := mkApp (mkConst ``Nat.succ) m
        let start := source ++ budget ++ #[e₀, mkApp mem (mkNatLit 1), mkApp mem s]
        let seeded := mkAppN (mkConst (rawHist ++ `S)) start
        forallBoundedTelescope (← inferType seeded) (some 2) fun acc _ => do
          let original := start ++ acc
          let full := source ++ masks ++ budget ++ acc
          let raw (name : Name) := mkAppN (mkConst (rawHist ++ name)) original
          let η := raw `η
          let hη := raw `hη
          let Sraw := raw `S
          let hSraw := raw `hS
          let reference := mkAppN (mkConst (rawHist ++ `referenceMap)) fixed
          let hsref := mkAppN (mkConst (rawHist ++ `reference_smooth)) fixed
          let actualSource := mkAppN (mkConst (datumNS ++ `exists_source_measured_tolerance)) (datum ++ #[s, η, hη])
          let (_, hd, measured) ← chooseParts `jetRadius `jet_spec `jet_pos `measured_from_jet full actualSource
          let near ← aliases [(`actualBand, source[24]!), (`actualOrder, source[28]!), (`jetPos, hd)] <|
            term "PhysicalHistory.exists_initialScale_for_prefix_neighborhood (N := embeddingDimension n) actualBand actualOrder jetPos"
          let (Se, _, pref) ← chooseParts `datumFrequency `datum_frequency_spec `datum_frequency_ge_two `prefix full near
          let S ← store `History.S full (← mkAppM ``max #[Sraw, Se]) true
          let hS ← aliases [(`rawFrequency, Sraw), (`datumFrequency, Se), (`rawGeTwo, hSraw), (`jointFrequency, S)] <|
            term "(show 2 ≤ jointFrequency from rawGeTwo.trans (le_max_left rawFrequency datumFrequency))"
          let hS ← store `History.hS full hS
          let previous := raw `continuation
          let stageProof ← forallBoundedTelescope (← inferType previous) (some 1) fun r _ => do
            let R₀ := r[0]!
            withLocalDeclD `hReached (← mkAppM ``LE.le #[S, R₀]) fun reached => do
              let boundAliases := [(`rawFrequency, Sraw), (`datumFrequency, Se), (`reached, reached)]
              let hRaw ← aliases boundAliases <| term "(le_max_left rawFrequency datumFrequency).trans reached"
              let he ← aliases boundAliases <| term "(le_max_right rawFrequency datumFrequency).trans reached"
              let atScale := mkAppN previous #[R₀, hRaw]
              let proof ← forallBoundedTelescope (← inferType atScale) (some 11) fun z _ => do
                unless z.size == 11 do throwError "measured history: original physical/current adjoint branch changed"
                let hist := z[1]!
                let current := z[4]!
                let F ← mkAppM `JanetCartan.RevisedGlobal.finiteMap #[reference, hist]
                let hF ← aliases [(`actualPrefix, hist), (`actualF, F), (`sourceSmooth, hsref)] <|
                  term "(show ContDiff ℝ ∞ actualF from sourceSmooth.add (ContDiff.sum (fun i _ ↦ (actualPrefix i).smooth')))"
                let hF ← store `History.current_smooth (fixed ++ z[:2].toArray) hF
                let atF := mkAppN measured #[F, hF]
                let input := (← whnf (← inferType atF)).bindingDomain!
                let some jet := input.find? (·.isAppOf `JanetCartan.cNorm) |
                  throwError "measured history: missing primitive physical immersion difference"
                let ja := jet.getAppArgs
                let K := ja[ja.size - 3]!
                let hK ← term "isCompact_closedBall _ _" (some (← mkAppM `IsCompact #[K]))
                let bounded := mkAppN pref #[R₀, he, K, reference, hK, z[0]!, hist, z[2]!, z[3]!]
                let hnear ← aliases [(`nearPrefix, bounded), (`radiusPos, hd)] <| term
                  "(cNorm_mono_order (show max 8 ((m + 1) + 6) ≤ rStar by unfold canonicalCarrierLowOrder at _hreserve; omega)).trans_lt (nearPrefix.trans (half_lt_self radiusPos))" (some input)
                let hnear ← store `History.current_measured_jet (full ++ #[R₀, reached] ++ z[:4].toArray) hnear
                let both := mkAppN atF #[hnear, current]
                let meanSpec ← mkAppM ``Classical.choose_spec #[both]
                let estimates ← mkAppM ``Classical.choose_spec #[meanSpec]
                let heMem ← mkAppM ``And.left #[estimates]
                let scalar ← mkAppM ``And.right #[estimates]
                let heLow ← mkAppM ``And.left #[scalar]
                let heHigh ← mkAppM ``And.right #[scalar]
                let some e := (← inferType heMem).find? (·.isAppOf `JanetCartan.PhysicalBackground.measuredSourceToL2) |
                  throwError "measured history: current datum is not the original measured physical source"
                let atCurrent := mkAppN atScale (z ++ #[e])
                let out ← forallBoundedTelescope (← inferType atCurrent) (some 1) fun gap _ => do
                  let atGap := mkAppN atCurrent (gap ++ #[heMem, heHigh])
                  let bound ← forallBoundedTelescope (← inferType atGap) (some 2) fun high _ => do
                    let result := mkAppN atGap (high ++ #[heLow])
                    mkLambdaFVars high (← instantiateMVars result)
                  mkLambdaFVars gap bound
                mkLambdaFVars z out
              mkLambdaFVars #[R₀, reached] proof
          let cont ← store `History.continuation full stageProof
          let bundle ← mkAppM ``And.intro #[hS, cont]
          discard <| store `history_measured_raw_tolerance full bundle
          logInfo "eliminated all current datum hypotheses using the actual retained finite mean and the physical prefix; only native current inverse clauses remain"

end JanetCartan.PhysicalInverseContinuity.MeasuredHistoryApplication
end
