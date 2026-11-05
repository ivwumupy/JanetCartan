module
public import JanetCartan.Iteration.PhysicalPairs.OriginalFirstMask
/-! # Universal complete waves at the SAME original signed labels

A fixed single-node derivative price is chosen before histories, shifts, target
or smoothing data. Index every complete Schwartz family satisfying that price
at each ORIGINAL signed label. The first component is the unchanged PSigma×12
label; the history map simply forgets the extra source. It is not assumed
injective. Actual full-source membership remains a separate producer obligation
(`main:prop:pairs`, `new:sec:order-of-choices`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformWaveDataTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformWaveData
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def rows := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def data := `JanetCartan.PhysicalPairs.OriginalSignedData
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def point (base : Array Expr) (t : Expr) : Array Expr := Id.run do
  let mut p := base
  let mut q := t
  for _ in [:12] do
    p := p.push (.proj ``PSigma 0 q)
    q := .proj ``PSigma 1 q
  return p
private def save (key : Name) (p : Array Expr) (value target : Expr) (isData := true) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "uniform original wave: later input escaped fixed derivative-price telescope {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking universal original wave {key}/{p.size}"
  (← IO.getStdout).flush
  if isData then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "All complete Schwartz source waves at the unchanged original signed label, with ONE fixed derivative price before history/shift/target/smoothing inputs; forget only the source, with no injectivity or cardinality assumption (main:prop:pairs; new:sec:order-of-choices)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "uniform original wave: nonstandard axioms at {name}: {axioms}"
  logInfo m!"universal original wave {key}/{p.size}: {axioms}"
elab "define_original_uniform_wave_data " mode:num : command => liftTermElabM do
  unless mode.getNat < 12 do throwError "uniform original wave: unknown mode"
  forallBoundedTelescope (← getConstInfo (hist ++ `Labels)).type (some 37) fun b _ => do
    withLocalDeclD `amplitudePrice (← mkArrow (mkConst ``Nat) (mkConst ``Real)) fun C => do
      let fixed := b.push C
      let oldβ := app (hist ++ `Labels) b
      let n := mkApp (mkConst ``Nat.succ) b[0]!
      let N := app `JanetCartan.embeddingDimension #[n]
      let graph := (← inferType (app (hist ++ `historyMap) b)).bindingBody!
      let chart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart graph.getAppArgs[:23].toArray
      if mode.getNat == 0 then
        withLocalDeclD `originalLabel oldβ fun t => do
          let p := point b t
          let wt := (← inferType (app (data ++ `uncut) p)).bindingDomain!
          withLocalDeclD `completeWaves wt fun Z => do
            let row := p.push Z
            let A := app (rows ++ `leftAmplitude) row
            let B := app (rows ++ `rightAmplitude) row
            let L := mkApp (app (fm ++ `fine) b) t
            let family (e : Expr) := withLocalDeclD `unit (mkConst ``Unit) fun u => mkLambdaFVars #[u] e
            let ledger := app (fm ++ `FullDerivativeProfile)
              #[b[0]!,N,mkConst ``Unit,chart,← family A,← family B,C,← family L]
            save `DerivativeProfile (fixed ++ #[t,Z]) ledger (mkSort .zero)
        return
      if mode.getNat == 1 then
        let fiber ← withLocalDeclD `originalLabel oldβ fun t => do
          let wt := (← inferType (app (data ++ `uncut) (point b t))).bindingDomain!
          let predicate ← withLocalDeclD `completeWaves wt fun Z =>
            mkLambdaFVars #[Z] (app (root ++ `DerivativeProfile) (fixed ++ #[t,Z]))
          let subtype ← mkAppM ``Subtype #[predicate]
          mkLambdaFVars #[t] subtype
        let labels ← mkAppM ``Sigma #[fiber]
        save `Labels fixed labels (mkSort .one)
        return
      let β := app (root ++ `Labels) fixed
      withLocalDeclD `sourceLabel β fun t => do
        let old := Expr.proj ``Sigma 0 t
        let Z := Expr.proj ``Subtype 0 (.proj ``Sigma 1 t)
        let p := point b old
        let row := p.push Z
        let family (e : Expr) := mkLambdaFVars #[t] e
        let values := #[( `historyMap,mkApp (app (hist ++ `historyMap) b) old),
            (`frequency,mkApp (app (fm ++ `frequency) b) old),
            (`fine,mkApp (app (fm ++ `fine) b) old),
            (`frame,mkApp (app (fm ++ `frame) b) old),
            (`phase,mkApp (app (fm ++ `phase) b) old),
            (`minus,mkApp (app (fm ++ `minus) b) old),
            (`left,app (rows ++ `leftAmplitude) row),
            (`right,app (rows ++ `rightAmplitude) row),
            (`measured,app (data ++ `measured) row),
            (`complexSource,app (data ++ `complex_input) row)]
        let (key,value) := values[mode.getNat-2]!
        let value ← family value
        save key fixed value (← inferType value)
end JanetCartan.PhysicalPairs.OriginalUniformWaveDataTemplate
end
