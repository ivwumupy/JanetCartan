module

public import JanetCartan.Iteration.PhysicalPairs.ColoredWindow
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledPolynomial
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# The actual signed outer sample in the original measured-factor family

Feed the very same original graph, history, common shift, ordered pair and sign
into `OriginalSampledPolynomial.GraphFamily`. Its frequency is exactly the
signed `λ*beat`; its slow scale is the entire fine envelope, not a free parameter.
All reached thresholds precede the external shift. The existing uniform
`graph_signed_costs` (and its adjoints) thus already apply, at their ORIGINAL
orders and constants; the final lemma evaluates the actual independent signed
low bound on that index. No sample, frequency or inverse is reselected.
Consumers: original measured finite chains and `main:prop:pairs`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
namespace JanetCartan.PhysicalPairs.SampledHistory
open PhysicalPrimary.OriginalHistoryFamily PhysicalInitialization.OriginalSampledPolynomial
open RevisedScales

/-- Unit-normalized input of the *operator* estimate for one signed term.
`amplitude=1` here is only the unused normalization slot of the operator family;
the actual `b²√(μᵢμⱼ)` stays outside the signed product. -/
def enter (d : ℕ) (B : ℝ) (kMin : ℕ) (Sreg Sop C R₀ : ℝ)
    (hR : max Sreg Sop ≤ R₀) (hscale : OriginalWindow.scaleThreshold C ≤ R₀)
    (j : ℕ) (u : Fin j → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
    (ell : Fin j → ℕ) (hh : RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell)
    (beat : ℝ) (hb : (historyScale R₀ growthExponent j)^(-separationExponent)/2 ≤ beat) :
    Histories d B kMin Sreg Sop := by
  let R := historyScale R₀ growthExponent j
  let raw : RawIndex d Unit := ⟨R₀,j,u,ell,R^carrierExponent * beat,
    OriginalWindow.fineScale C R,1,()⟩
  have w := OriginalWindow.history_pair_window C R₀ hscale j beat hb
  exact ⟨raw,hR,hh,(by norm_num : (1:ℝ) ≤ 2).trans w.2.2.1,w.2.1,w.2.2.2.1,zero_le_one⟩
end JanetCartan.PhysicalPairs.SampledHistory
end

public meta section
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.SampledHistory
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def here := `JanetCartan.PhysicalPairs.SampledHistory
private def win := `JanetCartan.PhysicalPairs.OriginalWindow
private def poly := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def a (k : Name) (p : Array Expr) := mkAppN (mkConst k) p
run_cmd liftTermElabM do
  let certName := win ++ `on_original_sample
  forallBoundedTelescope (← getConstInfo certName).type (some 37) fun x rest => do
    let C := x[36]!
    let some wDef := (← getConstInfo (win ++ `S)).value? (allowOpaque := true) | throwError "missing signed window threshold"
    let some graph := (wDef.beta x).find? (fun e => e.isAppOfArity (reg ++ `Graph.S) 34)
      | throwError "missing literal original graph in signed threshold"
    let g := graph.getAppArgs
    let some graphDef := (← getConstInfo (poly ++ `GraphFamily)).value? (allowOpaque := true) | throwError "missing measured graph family"
    let native := graphDef.beta g
    unless native.isAppOfArity (poly ++ `Histories) 5 && native.getAppArgs[3]! == graph do throwError "unexpected measured graph family"
    let gs := native.getAppArgs
    let sop := gs[4]!
    unless sop.isAppOfArity (op ++ `S) 33 do throwError "missing actual coefficient threshold"
    let old := a (win ++ `S) x
    let numeric := a (win ++ `scaleThreshold) #[C]
    let S ← store (here ++ `S) x (← mkAppM ``max #[old,sop]) true
    discard <| store (here ++ `hS) x (← mkAppM ``le_trans #[a (win ++ `hS) x,← mkAppM ``le_max_left #[old,sop]]) false
      (some (← mkAppM ``LE.le #[(← inferType (a (win ++ `hS) x)).getAppArgs[2]!,S]))
    forallBoundedTelescope rest (some 1) fun R₀ afterR => do
      unless afterR.isForall do throwError "missing reached original window"
      withLocalDeclD `reachedMeasuredSample (← mkAppM ``LE.le #[S,R₀[0]!]) fun hR => do
        let previous ← mkAppM ``le_trans #[← mkAppM ``le_max_left #[old,sop],hR]
        let hc ← mkAppM ``le_trans #[← mkAppM ``le_max_right #[old,sop],hR]
        let hg ← mkAppM ``le_trans #[← mkAppM ``le_max_left #[graph,numeric],previous]
        let hscale ← mkAppM ``le_trans #[← mkAppM ``le_max_right #[graph,numeric],previous]
        let both ← mkAppM ``max_le #[hg,hc]
        forallBoundedTelescope (afterR.bindingBody!.instantiate1 previous) (some 10) fun row _ => do
          unless row.size == 10 do throwError "actual signed shift/row tail changed"
          let p := x ++ R₀ ++ #[hR] ++ row
          let cert := a certName (x ++ R₀ ++ #[previous] ++ row)
          let spec := Expr.proj ``And 0 (.proj ``And 1 cert)
          let hb := Expr.proj ``And 0 spec
          let beat := (← inferType hb).getAppArgs.back!
          let i ← store (here ++ `index) p (a (here ++ `enter)
            (gs ++ #[C,R₀[0]!,both,hscale] ++ row[:4].toArray ++ #[beat,hb])) true (some (a (poly ++ `GraphFamily) g))
          discard <| store (here ++ `native_window) p cert
          discard <| store (here ++ `measured_history) p (a (poly ++ `admitted_data) (gs ++ #[a (op ++ `fact0) sop.getAppArgs,i]))
          let bounds := a (poly ++ `graph_signed_low) g
          forallBoundedTelescope (← inferType bounds) (some 3) fun sign _ => do
            discard <| store (here ++ `signed_low) (p ++ sign) (mkAppN bounds (sign.push i))
  logInfo "actual external common-ξ ordered signed pair entered the original measured graph family at ρ=λ*beat and complete fine K; original signed low-bound/adjoint index, no frequency or sample input"

/- A graph index deliberately forgets the actual ξ and pair. Keep them on the
INPUT side of the map even if several different sources have the same beat.
This is the β → GraphFamily argument of the observed finite-chain theorem. -/
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (here ++ `index)).type (some 49) fun p graphFamily => do
    unless p.size == 49 && graphFamily.isAppOfArity (poly ++ `GraphFamily) 34 do
      throwError "lost literal measured family of original signed labels"
    let x := p[:37].toArray
    let fields := p[37:].toArray
    let mut ty := mkConst ``Unit
    let mut val := mkConst ``Unit.unit
    for f in fields.reverse do
      let fam ← mkLambdaFVars #[f] ty
      let A ← inferType f
      val ← mkAppOptM ``PSigma.mk #[A,fam,f,val]
      ty ← mkAppM ``PSigma #[fam]
    let labels ← store (here ++ `Labels) x ty true (some (mkSort .one))
    let put ← store (here ++ `label) p val true (some labels)
    let map ← withLocalDeclD `signedSource labels fun l => do
      let mut row := #[]
      let mut tail := l
      for _ in fields do
        row := row.push (.proj ``PSigma 0 tail)
        tail := .proj ``PSigma 1 tail
      mkLambdaFVars #[l] (a (here ++ `index) (x ++ row))
    let map ← store (here ++ `historyMap) x map true (some (← mkArrow labels graphFamily))
    let point := a (here ++ `index) p
    discard <| store (here ++ `map_label) p (← mkEqRefl point) false (some (← mkEq (mkApp map put) point))
    let costs := a (poly ++ `graph_signed_costs) graphFamily.getAppArgs
    forallBoundedTelescope (← inferType costs) (some 3) fun letter _ => do
      discard <| store (here ++ `uniform_signed_costs) (x ++ letter)
        (← mkAppM (poly ++ `pullback_cost) #[map,mkAppN costs letter])
    for k in [`Labels,`label,`historyMap,`map_label,`uniform_signed_costs] do
      addDocStringCore (here ++ k) "The original external signed sample labels and their exact map to the measured history; polynomial order, constants and independent adjoints are uniform BEFORE all histories, shifts, and pairs (app:ch_regular:lem:finite-chain; main:prop:pairs)."
  logInfo "single full external signed sample family β → original GraphFamily; independently signed polynomial costs precede EVERY history/shift/pair"
end JanetCartan.PhysicalPairs.SampledHistory
end
