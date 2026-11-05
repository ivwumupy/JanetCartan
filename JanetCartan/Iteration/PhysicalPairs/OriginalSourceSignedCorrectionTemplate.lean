module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourcePrimary
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedSources
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedSum
/-! # The original signed correction of the actual complete-source primary

Use the already constructed actual Schwartz family on the SAME original
selected shift and physical history. The only additional predicate is the
existing numerical signed-window threshold. No source bound, output estimate,
new inverse, or new successful sampling event is assumed. Constants selecting
that threshold precede the history (`main:prop:pairs`, `main:eq:primary`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourceSignedCorrectionTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "construct_original_source_signed_correction" : command => liftTermElabM do
  withActualSelectedSourceWave fun p _ _ _ _ native64 _ => do
    unless native64.size == 64 do throwError "actual source signed correction: native64 changed"
    let W ← mkLambdaFVars #[p[52]!] (app `JanetCartan.PhysicalPairs.OriginalSourceSchwartz.wave p)
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p[:50].toArray
    withLocalDeclD `Cscale (mkConst ``Real) fun C => do
      let fixed := native64[:22].toArray ++ p[22:36].toArray ++ #[C]
      let threshold := app `JanetCartan.PhysicalPairs.SampledHistory.S fixed
      withLocalDeclD `reachedSignedWindow (← mkAppM ``LE.le #[threshold,p[44]!]) fun hR => do
        withLocalDeclD `δ (mkConst ``Real) fun δ => do
          let stem := fixed ++ #[p[44]!,hR] ++ p[46:50].toArray ++ #[p[43]!,shift]
          unless stem.size == 45 do throwError "actual source signed correction: original history45 changed"
          let original := app `JanetCartan.PhysicalPairs.OriginalSignedSum.correction (stem ++ #[W,δ])
          let params := p[:44].toArray ++ #[C] ++ p[44:52].toArray ++ #[hR,δ]
          unless params.size == 55 do throwError "actual source signed correction: threshold-before-history ABI changed"
          let type ← instantiateMVars (← mkForallFVars params (← inferType original))
          let value ← instantiateMVars (← mkLambdaFVars params original)
          for e in #[type,value] do
            if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
              throwError "actual source signed correction: unresolved sample or construction parameter"
          let pair := Lean.ShareCommon.shareCommon (type,value)
          let name := `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction
          liftM <| IO.eprintln "actual source signed correction: checking SAME actual complete-source S55"
          addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
          addDocStringCore name "The SAME original finite full signed real Schwartz correction of the actual complete-source primary family, on its ONE original selected shift/history; plus diagonals retained, only minus diagonal omitted; no norm/profile or successful response is assumed (main:prop:pairs)."
          liftM <| IO.eprintln "actual source signed correction: checked SAME actual complete-source S55"
end JanetCartan.PhysicalPairs.OriginalSourceSignedCorrectionTemplate
end
