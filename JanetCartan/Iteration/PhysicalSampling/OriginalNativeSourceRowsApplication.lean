module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalResponseSmooth
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceScalar
public meta import Lean

/-!
# Original source39 constants fixed before any response budget or sampled history

Use `rInit=16+rSrc` with the actual native initial constant of each row. The
source budget is the **unscaled** shift `initialC_i(k+16)`, since source input
50 is σ. Its strain-frame tolerance already occurs in the one chosen bare
frame; no additional frame/admission premise. This finite numerical maximum
pays every source39 row without putting a history or a future response budget
in any of them (`app:ch_response:eq:response-graded-source`,
`app:ch_response:cor:current-atoms`).
-/

@[expose] public section
namespace JanetCartan.PhysicalSampling.OriginalNativeSourceRowsApplication
private theorem source_fits {n r rStar : ℕ}
    (h : (16+r+(3+(n-1))+2)+ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n ≤ rStar) :
    16+r ≤ rStar := by omega
end JanetCartan.PhysicalSampling.OriginalNativeSourceRowsApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalNativeSourceRowsApplication
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalSampling
private def ns := root ++ `OriginalNativeSourceRows
private def base := root ++ `OriginalNativeInitialEvent
private def source := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def density := `JanetCartan.PhysicalBackground.NativeDensityProfiles
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (Nat.repeat (fun e => Expr.proj ``And 1 e) j h)

private def save (q : Name) (xs : Array Expr) (e : Expr) (data := false) (goal : Option Expr := none) : MetaM Expr := do
  let t ← match goal with | some v => pure v | none => inferType e
  let type ← instantiateMVars (← mkForallFVars xs t)
  let value ← instantiateMVars (← mkLambdaFVars xs e)
  if type.hasMVar || type.hasFVar || value.hasMVar || value.hasFVar || type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "original native source39: open {q}"
  let name := ns ++ q
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked original pre-response source39 {q} at {xs.size} inputs"
  return mkAppN (mkConst name) xs

/-- The actual source row and original sampler getter spines (not object-level
hypotheses). `fixed` has only 44 inputs, none after native density admission.
`initial44` uses the stronger 16+rSrc; `source39` uses the shifted budget. -/
structure Data where
  fixed : Array Expr
  initial44 : Array Expr
  sampler22 : Array Expr
  native33 : Array Expr
  source39 : Array Expr
  i : Expr
  index : Expr

def withSourceData (k : Data → MetaM Unit) : MetaM Unit := do
  let IConst := base ++ `initialC
  let some icBody := (← getConstInfo IConst).value? (allowOpaque := true)
    | throwError "original native source39: missing named actual initial budget"
  forallBoundedTelescope (← getConstInfo IConst).type (some 40) fun p _ => do
    let n := (← inferType p[1]!).appArg!
    let rpar := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
    withLocalDeclD `rSrc (mkConst ``Nat) fun r => do
      withLocalDeclD `hSamplerReserve (← mkAppM ``LE.le #[rpar,r]) fun hr => do
        let ri ← mkAppM ``HAdd.hAdd #[mkNatLit 16,r]
        let hri ← mkAppM ``Nat.add_le_add_left #[hr,mkNatLit 16]
        let early := p ++ #[ri,hri]
        forallBoundedTelescope (← inferType (mkAppN (mkConst IConst) early)) (some 2) fun later _ => do
          let initial44 := early ++ later
          let fixed := p ++ #[r,hr] ++ later
          let original := (icBody.beta initial44).headBeta
          lambdaTelescope original fun v b => do
            unless v.size == 1 && b.isAppOfArity (density ++ `initialC) 39 do
              throwError "original native source39: lost density38+row from actual initialC"
            let i := v[0]!
            let I ← inferType i
            let na := b.getAppArgs[:33].toArray
            let cap := na[20]!
            unless cap.isAppOfArity (root ++ `samplingCappedExtra) 4 do throwError "original native source39: changed original sampling cap"
            let w := p[:3].toArray ++ na[2:20].toArray ++ #[cap.appArg!]
            let family := #[p[0]!] ++ na[1:21].toArray ++ p[22:24].toArray
            let frame ← mkAppM (root ++ `OriginalBare.exists_frame) #[p[1]!,p[4]!]
            let hf ← mkAppM ``Classical.choose_spec #[frame]
            let C := mkAppN (mkConst IConst) (initial44.push i)
            let hC := mkAppN (mkConst (base ++ `initialC_nonneg)) (initial44.push i)
            let (A,hA) ← withLocalDeclD `j (mkConst ``Nat) fun j => do
              let s ← mkAppM ``HAdd.hAdd #[j,mkNatLit 16]
              return (← mkLambdaFVars #[j] (mkApp C s),← mkLambdaFVars #[j] (mkApp hC s))
            let hres := mkAppN (mkConst ``source_fits) #[n,r,p[31]!,later[0]!]
            let row := family ++ na[21:31].toArray ++ #[part hf 3,i,A,hA,r,hres]
            unless w.size == 22 && row.size == 39 do throwError "original native source39: changed sampler22 / source39 datums"
            k ⟨fixed,initial44,w,na,row,i,I⟩

elab "fix_original_native_source_rows " which:num : command => liftTermElabM <| withTransparency .reducible <| withSourceData fun d => do
  let xs := d.fixed
  let atRow := xs.push d.i
  let rowS := mkAppN (mkConst (source ++ `S)) d.source39
  let S := mkAppN (mkConst (ns ++ `S)) xs
  let ex := mkAppN (mkConst (ns ++ `exists_threshold)) xs
  match which.getNat with
  | 0 => discard <| save `rowS atRow rowS true
  | 1 => discard <| save `Csource atRow (mkAppN (mkConst (source ++ `Csource)) d.source39) true
  | 2 => discard <| save `Csource_nonneg atRow (mkAppN (mkConst (source ++ `Csource_nonneg)) d.source39)
  | 3 =>
    let rows ← mkLambdaFVars #[d.i] (mkAppN (mkConst (ns ++ `rowS)) atRow)
    let two ← mkNumeral (mkConst ``Real) 2
    let I := mkAppN (mkConst (root ++ `OriginalWeights.Index)) d.sampler22
    let fi ← withTransparency .default <| synthInstance (← mkAppM ``Finite #[I])
    let t ← mkAppOptM `JanetCartan.PhysicalInitialization.OriginalRegular.common_graph_threshold #[some I,some fi,some two,some rows]
    discard <| save `exists_threshold xs t
  | 4 => discard <| save `S xs (← mkAppM ``Classical.choose #[ex]) true
  | 5 =>
    let h ← mkAppM ``Classical.choose_spec #[ex]
    let two ← mkNumeral (mkConst ``Real) 2
    discard <| save `hS xs (.proj ``And 0 h) false (some (← mkAppM ``LE.le #[two,S]))
  | 6 =>
    let h ← mkAppM ``Classical.choose_spec #[ex]
    let h := mkApp (.proj ``And 1 h) d.i
    discard <| save `source_le atRow h false (some (← mkAppM ``LE.le #[rowS,S]))
  | _ => throwError "original native source39: unknown numerical field"

end JanetCartan.PhysicalSampling.OriginalNativeSourceRowsApplication
end
