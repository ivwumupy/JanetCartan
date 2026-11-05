module

public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalGradedResponseWindow
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalResponseProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalInitialSourceApplication
public meta import Lean

/-!
# Fix the actual quantitative full-response budget before the original shift

The response reserve is the literal raw-slice parameter order r, the source
reserve is r+n+1 and the genuine density reserve is 16+r+n+1. The single high
coefficient order already pays the complete inverse, strain and reconstruction
orders. The original signed and sampler source-scale admissions are both on
the one early bare family. The actual full derivative-amplitude budget comes
from the source39 row's native finite inverse; no response constants, shifts,
or prior histories are parameters of that cost (`new:sec:order-of-choices`,
`app:ch_response:eq:response-reconstruction-grading`, `app:ch_waves:thm:sampling`).
-/

@[expose] public section
namespace JanetCartan.PhysicalSampling.OriginalNativeGradedEventApplication
open RawPrimary.SliceBounds RegularSector.FiniteEvolution FourierIntegral
open ContinuumRow.CanonicalCarrier

private theorem actual_reserves {d r rs : ℕ} (hr : rawSliceParameterOrder (d+1) ≤ r)
    (h : (16+r+(3+((d+1)-1))+2)+canonicalCarrierLowOrder (d+1) ≤ rs) :
    r + 3*(d+1) + 20 ≤ rs ∧ sectorLowOrder d + (d+2) + 2 ≤ rs := by
  simp only [rawSliceParameterOrder,rawSliceJetOrder] at hr
  simp only [canonicalCarrierLowOrder,Nat.add_sub_cancel] at h
  simp only [sectorLowOrder,RegularSector.Characteristic.UniformEvolution.retardedCoefficientOrder,
    WholeImageGeometry.wholeImagePhaseReserve,LowBounds.primitiveNormalReserve,FullLowBounds.fullLowReserve_eq]
  omega

private theorem rpar_le_shifted (d : ℕ) (r : ℕ) : r ≤ r+(d+1)+1 := by omega
private theorem sampler_matrix_weight {bound D σ τ K : ℝ} {j r : ℕ}
    (h : bound ≤ D * (τ*σ) * K^(j-r)) : bound ≤ τ * (σ*D) * K^(j-r) := by
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h
private theorem one_at_two {S R : ℝ} (h : 2 ≤ S) (hr : S ≤ R) : 1 ≤ R := by linarith only [h,hr]
private theorem native_rate_le_one {τ : ℝ} (h : 1 ≤ τ⁻¹) : τ ≤ 1 := by
  simpa only [inv_inv] using inv_le_one_of_one_le₀ h

end JanetCartan.PhysicalSampling.OriginalNativeGradedEventApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalNativeGradedEventApplication
open Lean Meta Elab Command OriginalNativeSourceRowsApplication
private def ps := `JanetCartan.PhysicalSampling
private def ns := ps ++ `OriginalNativeGradedEvent
private def ni := ps ++ `OriginalNativeInitialEvent
private def sm := ps ++ `OriginalNativeSmoothEvent
private def rows := ps ++ `OriginalNativeSourceRows
private def response := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseProfiles
private def input := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
private def boundNS := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse
private def src := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (Nat.repeat (fun e => Expr.proj ``And 1 e) j h)
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some b := (← getConstInfo n).value? (allowOpaque := true) | throwError "quantitative sampling: missing {n}"
  return (b.beta xs).headBeta
private def save (n : Name) (xs : Array Expr) (v : Expr) (data := false) (goal : Option Expr := none) : MetaM Expr := do
  let ty ← match goal with | some t => pure t | none => inferType v
  let type ← instantiateMVars (← mkForallFVars xs ty)
  let value ← instantiateMVars (← mkLambdaFVars xs v)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "quantitative sampling: open {n}"
  let name := ns ++ n
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked actual full-derivative sampling {n} at {xs.size} inputs"
  return app name xs

private structure Static where
  params : Array Expr
  source : Data
  quantitative44 : Array Expr
  reserve : Expr

private def withStatic (run : Static → MetaM Unit) : MetaM Unit := do
  let rsName := rows ++ `rowS
  forallBoundedTelescope (← getConstInfo rsName).type (some 40) fun p _ => do
    let n := (← inferType p[1]!).appArg!
    let r := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
    let rs ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[r,n],mkNatLit 1]
    let hr := app ``rpar_le_shifted #[p[0]!,r]
    let fixed0 := p ++ #[rs,hr]
    forallBoundedTelescope (← inferType (app rsName fixed0)) (some 2) fun later _ => do
      let fixed := fixed0 ++ later
      let rInit ← mkAppM ``HAdd.hAdd #[mkNatLit 16,rs]
      let initial := p ++ #[rInit,← mkAppM ``Nat.add_le_add_left #[hr,mkNatLit 16]] ++ later
      let I := (← whnf (← inferType (app rsName fixed))).bindingDomain!
      withLocalDeclD `i I fun i => do
        let row ← bodyAt rsName (fixed.push i)
        unless row.isAppOfArity (src ++ `S) 39 do throwError "quantitative sampling: changed source39 maximum"
        let s := row.getAppArgs
        unless s[20]!.isAppOfArity (ps ++ `samplingCappedExtra) 4 do throwError "quantitative sampling: changed original capped selector"
        let w := p[:3].toArray ++ s[2:20].toArray ++ #[s[20]!.appArg!]
        let low ← bodyAt (ni ++ `initialC) (initial.push i)
        unless low.isAppOfArity `JanetCartan.PhysicalBackground.NativeDensityProfiles.initialC 39 do throwError "quantitative sampling: different native density"
        let d : Data := ⟨fixed,initial,w,low.getAppArgs[:33].toArray,s,i,I⟩
        let hsType := (← whnf (← inferType (app (response ++ `S) s))).bindingDomain!
        withLocalDeclD `hSignedSigma hsType fun hσ => do
          let h := app ``actual_reserves #[p[0]!,rs,p[31]!,hr,later[0]!]
          let stat := s ++ #[hσ,Expr.proj ``And 0 h,Expr.proj ``And 1 h,r,← mkEqRefl rs]
          withLocalDeclD `hp (← mkAppM ``LT.lt #[mkNatLit 0,p[2]!]) fun hp =>
            run ⟨p ++ later ++ #[hσ,hp],d,stat,r⟩

private def master (g : Static) : MetaM (Array Expr × Array Expr) := do
  let d := g.source
  let C := app (ns ++ `Cresp) g.params
  let hC := app (ns ++ `Cresp_nonneg) g.params
  let rest := #[C,hC,g.params.back!]
  return (d.fixed ++ rest,d.initial44 ++ rest)

elab "fix_original_quantitative_sampling_budget " which:num : command => liftTermElabM <| withTransparency .reducible <| withStatic fun g => do
  let d := g.source
  let p := g.params
  let q := g.quantitative44
  let S := app (ns ++ `S) p
  let ex := app (ns ++ `exists_threshold) p
  let hσ := (← mkAppM `le_of_lt #[Expr.proj ``And 0 d.native33[23]!])
  match which.getNat with
  | 0 | 1 =>
    let v ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      let C := mkApp (app (boundNS ++ `Cresp) q) k
      let c ← if which.getNat == 0 then mkAppM ``HMul.hMul #[d.native33[21]!,C]
        else mkAppM `mul_nonneg #[hσ,mkApp (app (boundNS ++ `Cresp_nonneg) q) k]
      mkLambdaFVars #[d.i,k] c
    discard <| save (if which.getNat == 0 then `Cresp else `Cresp_nonneg) p v (which.getNat == 0)
  | 2 => discard <| save `responseS (p.push d.i) (app (response ++ `S) q) true
  | 3 =>
    let (sm47,_) ← master g
    let base := app (sm ++ `S) sm47
    let row ← mkLambdaFVars #[d.i] (app (ns ++ `responseS) (p.push d.i))
    let I := app (ps ++ `OriginalWeights.Index) d.sampler22
    let f ← withTransparency .default <| synthInstance (← mkAppM ``Finite #[I])
    let v ← mkAppOptM `JanetCartan.PhysicalInitialization.OriginalRegular.common_graph_threshold #[some I,some f,some base,some row]
    discard <| save `exists_threshold p v
  | 4 => discard <| save `S p (← mkAppM ``Classical.choose #[ex]) true
  | 5 =>
    let (sm47,_) ← master g
    discard <| save `event_le p (.proj ``And 0 (← mkAppM ``Classical.choose_spec #[ex])) false (some (← mkAppM ``LE.le #[app (sm ++ `S) sm47,S]))
  | 6 =>
    let h := Expr.proj ``And 1 (← mkAppM ``Classical.choose_spec #[ex])
    discard <| save `response_le (p.push d.i) (mkApp h d.i) false (some (← mkAppM ``LE.le #[app (response ++ `S) q,S]))
  | 7 =>
    let (sm47,_) ← master g
    discard <| save `hS p (← mkAppM `le_trans #[app (sm ++ `hS) sm47,app (ns ++ `event_le) p])
  | _ => throwError "quantitative sampling: unknown static bound"

private def withHistory (g : Static) (k : Array Expr → Array Expr → Array Expr → Array Expr → Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  let p := g.params
  let (sm47,high47) ← master g
  withLocalDeclD `R₀ (mkConst ``Real) fun R => do
    withLocalDeclD `hReached (← mkAppM ``LE.le #[app (ns ++ `S) p,R]) fun hR => do
      let hs ← mkAppM `le_trans #[app (ns ++ `event_le) p,hR]
      let hr ← mkAppM `le_trans #[app (ns ++ `response_le) (p.push g.source.i),hR]
      let prior := app (sm ++ `exists_of_quantitative_uncut_jets) (sm47 ++ #[R,hs])
      forallBoundedTelescope (← inferType prior) (some 4) fun hist _ =>
        k (p ++ #[R,hR] ++ hist) sm47 high47 hist (mkAppN prior hist) hs hr hR

/-- Checked-syntax read-only view of *one original* native graded stage for
normal comparison/transport. `data` retains the actual native initial44,
source39, sampler22, row and index. `params44` are the numerical original
event inputs; `physical44` is this row's fixed full-jet producer.
`hSmooth` reaches `OriginalNativeSmoothEvent.S`, `hPhysical` reaches THIS
row's `OriginalPhysicalResponse.S`, and `hR` reaches the original graded
maximum. No analytic hypothesis or new physical choice is made by the view. -/
structure NativeGradedStage where
  data : Data
  params44 : Array Expr
  physical44 : Array Expr
  args50 : Array Expr
  smooth47 : Array Expr
  high47 : Array Expr
  history : Array Expr
  prior : Expr
  hSmooth : Expr
  hPhysical : Expr
  hR : Expr

/-- Read-only aligned stage producer for the exact original continuum
comparison; it merely opens the canonical theorem's own fixed telescope. -/
def withNativeGradedStage (go : NativeGradedStage → MetaM Unit) : MetaM Unit :=
  withStatic fun g => withHistory g fun a s h hist p hs hr hR =>
    go ⟨g.source,g.params,g.quantitative44,a,s,h,hist,p,hs,hr,hR⟩

/-- The literal full measured row derivative profile. Its source has genuine
σ-size and its output is NOT χ₂-truncated outside a phase chart. -/
elab "prove_original_uncontracted_sampling_jets" : command => liftTermElabM <| withTransparency .reducible <| withStatic fun g => withHistory g fun args sm47 high hist prior hs hr hR => do
  let p := g.params
  let d := g.source
  let R := args[44]!
  let hh ← mkAppM `le_trans #[app (sm ++ `event_le) sm47,hs]
  let hNat ← mkAppM `le_trans #[app (ni ++ `native_le) high,hh]
  let hSrc ← mkAppM `le_trans #[app (rows ++ `source_le) (d.fixed.push d.i),← mkAppM `le_trans #[app (sm ++ `source_le) sm47,hs]]
  let ht := app (sm ++ `uncut_response_smooth) (sm47 ++ #[R,hs] ++ hist)
  let wanted := (← whnf (← inferType prior)).bindingDomain!
  let .forallE _ _ each _ ← whnf wanted | throwError "quantitative sampling: missing measured row"
  let next := each.instantiate1 d.i
  let result ← forallBoundedTelescope next (some 1) fun colors rest => do
    let c := colors[0]!
    let full ← inferType (mkAppN ht #[d.i,c])
    let (s,_) ← OriginalNativeSmoothEventApplication.trueSourceSpines d high hist R hh hSrc hNat c full
    let pic ← mkAppM ``Prod.mk #[d.i,c]
    let radial := app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.radial_ge_one (d.sampler22.push pic)
    let hOne := app ``one_at_two #[app (ns ++ `S) p,R,app (ns ++ `hS) p,hR]
    let win ← mkAppM `JanetCartan.PhysicalPrimary.OriginalReservedWords.colored_window_of_radial #[hOne,radial,hist[0]!]
    let rateOne ← mkAppM ``native_rate_le_one #[part win 1]
    let full60 := g.quantitative44 ++ #[R,hr] ++ s[41:53].toArray ++ #[rateOne,tail win 2]
    unless full60.size == 60 do throwError "quantitative sampling: native physical carrier60 changed"
    let inside := app (ps ++ `OriginalResponseWindow.working_in_native_graded_domain) (d.sampler22 ++ s[21:53].toArray)
    forallBoundedTelescope rest (some 3) fun v t => do
      unless v.size == 3 && t.isAppOfArity ``LE.le 4 do throwError "quantitative sampling: missing all-order whole-K target"
      let h := app (boundNS ++ `derivative_jets) (full60 ++ #[v[0]!,v[1]!,mkAppN inside #[v[1]!,v[2]!]])
      let h ← mkAppM ``sampler_matrix_weight #[h]
      mkLambdaFVars (#[d.i,c] ++ v) h
  discard <| save `uncut_response_jets args result false (some wanted)

elab "apply_unconditional_original_sampling_event" : command => liftTermElabM <| withTransparency .reducible <| withStatic fun g => withHistory g fun args _ _ _ prior _ _ _ => do
  let e := mkApp prior (app (ns ++ `uncut_response_jets) args)
  unless (← whnf (← inferType e)).isAppOfArity ``Exists 2 do throwError "quantitative sampling: missing the actual common shift"
  discard <| save `exists_on_original_history args e

end JanetCartan.PhysicalSampling.OriginalNativeGradedEventApplication
end
