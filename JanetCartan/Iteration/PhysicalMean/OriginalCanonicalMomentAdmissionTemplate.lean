module

public import JanetCartan.Iteration.PhysicalMean.OriginalSampledMomentGeometry
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
public meta import Lean

/-!
# Pre-source specialization of the actual native telescope

Choose the quadrature order and the extra-frame allowance before the original
bare frame. Insert the original named gamma before sigma, and obtain all five
sigma admissions from its one original ceiling. The final threshold is one
maximum of the original native threshold and task90's threshold. The original
source, inverse, sample, cutoff and history are never selected again
(`new:sec:order-of-choices`, `app:ch_mean_pairs:defn:mean-canonical`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission

/-- Quadrature order is fixed before the frame and every native choice. -/
def pOrder : ℕ := 1

/-- The fixed order satisfies the original native constructor's requirement. -/
theorem pOrder_pos : 0 < pOrder := Nat.zero_lt_one

/-- The source forcing-order specialization uses exactly this early order. -/
theorem pOrder_eq_one : pOrder = 1 := rfl

/-- Only the frozen dimension/model menu enters the extra-frame allowance. -/
def extraFrame {d : ℕ} (hn : 5 ≤ d + 1) : ℝ :=
  OriginalSampledMomentGeometry.tolerance hn / 2

/-- The original bare-frame selector receives a genuinely positive allowance. -/
theorem extraFrame_pos {d : ℕ} (hn : 5 ≤ d + 1) : 0 < extraFrame hn :=
  div_pos (OriginalSampledMomentGeometry.tolerance_pos hn) (by norm_num)

/-- This bound is established before choosing the original bare frame. -/
theorem extraFrame_le_tolerance {d : ℕ} (hn : 5 ≤ d + 1) :
    extraFrame hn ≤ OriginalSampledMomentGeometry.tolerance hn :=
  div_le_self (OriginalSampledMomentGeometry.tolerance_pos hn).le one_le_two

end JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission

namespace JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
open OriginalCanonicalMomentAdmission

private theorem moment_bound (d : ℕ) (hn : 5 ≤ d + 1) (gamma : ℝ)
    (h : gamma ≤ extraFrame hn) : gamma ≤ OriginalSampledMomentGeometry.tolerance hn :=
  h.trans (extraFrame_le_tolerance hn)

private theorem join_native (a b : ℝ) : a ≤ max a b := le_max_left a b
private theorem join_moment (a b : ℝ) : b ≤ max a b := le_max_right a b
private theorem join_two (a b : ℝ) (h : 2 ≤ a) : 2 ≤ max a b :=
  h.trans (le_max_left a b)
private theorem reach_native (a b R : ℝ) (h : max a b ≤ R) : a ≤ R :=
  (le_max_left a b).trans h
private theorem reach_moment (a b R : ℝ) (h : max a b ≤ R) : b ≤ R :=
  (le_max_right a b).trans h

end JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
private def geom := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry
private def ps := `JanetCartan.PhysicalSampling
private def native := ps ++ `OriginalNativeGradedEvent
private def bareScale := ps ++ `OriginalBareScale
private def source := `JanetCartan.PhysicalMean.OriginalCanonicalActual.G
private def app (n : Name) (xs : Array Expr) : Expr := mkAppN (mkConst n) xs
private def left (e : Expr) : Expr := .proj ``And 0 e
private def right (e : Expr) : Expr := .proj ``And 1 e

private def progress (s : String) : MetaM Unit := do
  logInfo s
  if let some path ← IO.getEnv "JANET_MOMENT_ADMISSION_TRACE" then
    IO.FS.withFile path .append fun h => do
      h.putStrLn s
      h.flush

private def save (short : Name) (params : Array Expr) (term : Expr)
    (data := false) (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType term
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let env ← getEnv
  for e in #[type, value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "original moment admission: missing producers in {short}: {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original moment admission: open declaration {short}"
  let name := root ++ short
  progress s!"original moment admission: kernel checking {short} on {params.size} inputs"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name
    "Actual pre-source admission on the SAME original native telescope; one early order/frame/gamma/ceiling, no source, inverse, sample, cutoff or history reselection (new:sec:order-of-choices)."

/-- Open an actual native prefix, inserting the early choices as dependent
terms, not substituting an already-open telescope. `params` contains only
free inputs. Its sigma admission is to the ONE original BareScale ceiling. -/
def withSelectedBefore (count : Nat)
    (next : Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  unless count ≤ 44 do throwError "original moment admission: prefix exceeds native44"
  let rec walk (fuel index : Nat) (type : Expr) (all params : Array Expr)
      (admissions : Option Expr) : MetaM Unit := do
    match fuel with
    | 0 => throwError "original moment admission: native prefix fuel exhausted"
    | fuel + 1 =>
      if index == count then
        next all params type
      else do
        let .forallE name domain body bi := type.consumeMData
          | throwError "original moment admission: native telescope ended at {index}"
        let early := all[:24].toArray
        let chosen? := match index with
          | 2 => some (mkConst (root ++ `pOrder))
          | 3 => some (app (root ++ `extraFrame) all[:2].toArray)
          | 4 => some (app (root ++ `extraFrame_pos) all[:2].toArray)
          | 24 => some (app (bareScale ++ `γ) early)
          | 25 => some (app (bareScale ++ `γ_pos) early)
          | 26 => some (app (bareScale ++ `γ_le_sampler) early)
          | 43 => some (mkConst (root ++ `pOrder_pos))
          | _ => none
        if let some chosen := chosen? then
          walk fuel (index+1) (body.instantiate1 chosen) (all.push chosen) params admissions
        else if index == 28 then do
          let admit := app (bareScale ++ `scale_admissions) (early ++ #[all[27]!])
          let .forallE _ capDomain _ _ ← inferType admit
            | throwError "original moment admission: missing original sigma-ceiling domain"
          withLocalDeclNoLocalInstanceUpdate `hSigma .default capDomain fun hSigma => do
            let five := mkApp admit hSigma
            let chosen := left (left five)
            walk fuel (index+1) (body.instantiate1 chosen) (all.push chosen)
              (params.push hSigma) (some five)
        else if #[36,37,41,42].contains index then do
          let some five := admissions
            | throwError "original moment admission: sigma admissions used before the original ceiling"
          let chosen := match index with
            | 36 => left (right (left five))
            | 37 => left (right (right (left five)))
            | 41 => right five
            | _ => right (right (right (left five)))
          walk fuel (index+1) (body.instantiate1 chosen) (all.push chosen) params admissions
        else
          let cont := fun x =>
            walk fuel (index+1) (body.instantiate1 x) (all.push x) (params.push x) admissions
          if bi == .instImplicit then withLocalDecl name bi domain cont
          else withLocalDeclNoLocalInstanceUpdate name bi domain cont
  walk 45 0 (← getConstInfo source).type #[] #[] none

private def gammaMoment (p : Array Expr) : Expr :=
  app ``moment_bound (p[:2].toArray ++ #[p[24]!,app (bareScale ++ `γ_le_extra) p[:24].toArray])

private def momentArgs (p : Array Expr) : MetaM (Array Expr) := do
  let sampler ← JanetCartan.PhysicalSampling.OriginalBareScaleApplication.originalSampler p[:24].toArray
  unless sampler.size == 22 do throwError "original moment admission: original sampler22 changed"
  -- Direct Native.S consumes the once-capped user slot21. AtPoint instead
  -- consumes the original external slot and applies userCap in its body.
  return sampler ++ p[22:27].toArray ++ #[gammaMoment p] ++ p[27:36].toArray ++ #[p[39]!]

/-- The full actual native53/source53/graph42 specialization. Only the single
joined threshold is assumed reached; the native and task90 reached proofs are
both consequences, inserted before the dependent original history. -/
def withSelectedAtPoint
    (next : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  withSelectedBefore 44 fun p params remaining => do
    forallBoundedTelescope remaining (some 1) fun rs reach => do
      unless rs.size == 1 do throwError "original moment admission: missing original R0"
      let .forallE _ _ body _ := reach.consumeMData
        | throwError "original moment admission: missing original reached premise"
      let common := app (root ++ `commonS) params
      withLocalDeclNoLocalInstanceUpdate `hCommon .default
          (← mkAppM ``LE.le #[common,rs[0]!]) fun hCommon => do
        let reachedParams := params ++ rs ++ #[hCommon]
        let hNative := app (root ++ `native_reached) reachedParams
        let hMoment := app (root ++ `moment_reached) reachedParams
        forallBoundedTelescope (body.instantiate1 hNative) (some 7) fun tail _ => do
          unless tail.size == 7 do throwError "original moment admission: native history tail7 changed"
          let all := p ++ rs ++ #[hNative] ++ tail
          let sampler ← JanetCartan.PhysicalSampling.OriginalBareScaleApplication.originalSampler p[:24].toArray
          let point := sampler[:21].toArray ++ p[21:27].toArray ++ #[gammaMoment p] ++
            p[27:36].toArray ++ #[p[39]!,rs[0]!,hMoment] ++ tail
          unless all.size == 53 && point.size == 47 do
            throwError "original moment admission: native53/AtPoint47 join changed"
          next all (reachedParams ++ tail) point

/-- Publish each checked field separately, without raising resource limits or
re-elaborating a giant conjunction. The same dependent selector is used for
every field, so no free gamma or independently admitted sigma can reappear. -/
elab "construct_original_canonical_moment_admission " mode:num : command =>
  liftTermElabM <| withTransparency .reducible do
    let mode := mode.getNat
    if mode ≤ 6 then
      withSelectedBefore 24 fun p params _ => do
        let gamma := app (bareScale ++ `γ) p
        match mode with
        | 0 => save `AtPoint.gamma params gamma true
        | 1 => save `AtPoint.gamma_pos params (app (bareScale ++ `γ_pos) p)
        | 2 => save `AtPoint.gamma_le_delta params (app (bareScale ++ `γ_le_sampler) p)
        | 3 => save `AtPoint.gamma_le_extra params (app (bareScale ++ `γ_le_extra) p)
        | 4 => save `AtPoint.gamma_le_tolerance params (gammaMoment (p.push gamma))
        | 5 => save `ceiling params (app (bareScale ++ `ceiling) p) true
        | _ => save `ceiling_pos params (app (bareScale ++ `ceiling_pos) p)
    else if mode ≤ 14 then
      withSelectedBefore 44 fun p params _ => do
        let nativeS := app (native ++ `S) p
        let momentS := app (geom ++ `Native.S) (← momentArgs p)
        let a := app (root ++ `nativeS) params
        let b := app (root ++ `momentS) params
        match mode with
        | 7 => save `nativeS params nativeS true
        | 8 => save `momentS params momentS true
        | 9 => save `commonS params (← mkAppM ``Max.max #[a,b]) true
        | 10 => save `commonS_ge_native params (app ``join_native #[a,b])
        | 11 => save `commonS_ge_moment params (app ``join_moment #[a,b])
        | 12 => save `commonS_ge_two params (app ``join_two #[a,b,app (native ++ `hS) p])
        | _ =>
          withLocalDeclNoLocalInstanceUpdate `R0 .default (mkConst ``Real) fun R => do
            let common := app (root ++ `commonS) params
            withLocalDeclNoLocalInstanceUpdate `hCommon .default
                (← mkAppM ``LE.le #[common,R]) fun hCommon => do
              let proof := app (if mode == 13 then ``reach_native else ``reach_moment) #[a,b,R,hCommon]
              save (if mode == 13 then `native_reached else `moment_reached)
                (params ++ #[R,hCommon]) proof
    else
      withSelectedAtPoint fun all params point => do
        match mode with
        | 15 => save `AtPoint.fields params (app (geom ++ `AtPoint.fields) point) true
        | 16 => save `AtPoint.profiles params (app (geom ++ `AtPoint.profiles) point)
        | 17 => save `G params (app source all) true
        | 18 =>
          let actual := app source all
          save `G_eq_original params (← mkEqRefl actual) false
            (some (← mkEq (app (root ++ `G) params) actual))
        | _ => throwError "original moment admission: unknown publication mode {mode}"

end JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
end
