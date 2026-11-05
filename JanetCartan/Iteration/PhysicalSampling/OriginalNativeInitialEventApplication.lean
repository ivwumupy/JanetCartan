module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
public import JanetCartan.Iteration.PhysicalBackground.NativeAdmission
public meta import Lean

/-!
# Specialize the original sampler to its actual high positive initial profile

The consumer is the literal initial field of the bare positive event. Admit a
possibly stronger `rInit` for the separate size-σ source calculation, reuse the
native density's unscaled prehistory `initialC`, and put `σ * initialC` (not a
second σ) into the sampler. The required raw density and coefficient reserves
and its operator threshold are paid before R₀. No successful sample, high
initial estimate or new positive density is assumed
(`new:eq:amplitude-test`, `app:ch_background:prop:bg-current`).
-/

@[expose] public noncomputable section
namespace JanetCartan.PhysicalSampling.OriginalNativeInitialEventApplication
open RawPrimary.SliceBounds ContinuumRow.CanonicalCarrier

private theorem reserve_facts {n rInit rStar : ℕ}
    (hbase : 16 + rawSliceParameterOrder n ≤ rInit)
    (hreserve : (rInit + (3 + (n-1)) + 2) + canonicalCarrierLowOrder n ≤ rStar) :
    16 + rawSliceParameterOrder n ≤ rStar ∧ 2 + (rInit + (3 + (n-1)) + 2) ≤ rStar := by
  simp only [canonicalCarrierLowOrder] at hreserve
  omega

private theorem scale_at_native_threshold {S R : ℝ} (hS : 2 ≤ S) (h : S ≤ R) (stage : ℕ) :
    1 ≤ currentCoefficientScale R stage := one_le_currentCoefficientScale (by linarith) stage

private theorem profile_weaken_reserve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f : E → ℝ} {r r' : ℕ} {L : ℝ} {A : ℕ → ℝ}
    (hL : 1 ≤ L) (h : r ≤ r') (hA : ∀ k, 0 ≤ A k) (hp : HasDerivativeProfile K f r' L A) :
    HasDerivativeProfile K f r L A := fun k ↦ (hp k).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (Nat.sub_le_sub_left h k)) (hA k))

end JanetCartan.PhysicalSampling.OriginalNativeInitialEventApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalNativeInitialEventApplication
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalSampling
private def ns := root ++ `OriginalNativeInitialEvent
private def bare := root ++ `OriginalBareEvent
private def pos := root ++ `OriginalPositiveEvent
private def adm := `JanetCartan.PhysicalBackground.NativeAdmission
private def density := `JanetCartan.PhysicalBackground.NativeDensityProfiles
private def source := `JanetCartan.PhysicalBackground.NativeSourceProfiles

private def save (n : Name) (xs : Array Expr) (e : Expr) (data := false)
    (goal : Option Expr := none) : MetaM Expr := do
  let t ← instantiateMVars (← mkForallFVars xs (← match goal with | none => inferType e | some v => pure v))
  let v ← instantiateMVars (← mkLambdaFVars xs e)
  if t.hasFVar || v.hasFVar || t.hasMVar || v.hasMVar || t.hasLevelMVar || v.hasLevelMVar ||
      t.hasSorry || v.hasSorry then throwError "native initial sampler: unexpected open term {n}"
  let name := ns ++ n
  if data then addDecl (.defnDecl {name,levelParams := [],type := t,value := v,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type := t,value := v}) (forceExpose := true)
  logInfo m!"checked original native initial-profile sampler field {n} at {xs.size} inputs"
  return mkAppN (mkConst name) xs

private def bodyApp (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some b := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "native initial sampler: missing actual threshold {n}"
  return (b.beta xs).headBeta

private structure Static where
  params : Array Expr
  event46 : Array Expr
  native33 : Array Expr
  density38 : Array Expr
  source38 : Array Expr
  index : Expr
  base : Expr
  hσ : Expr

/-- Extract the original positive47 and native32 from the checked numerical
maximum; these are the SAME frame and cap chosen before the bare event. -/
private def withStatic (k : Static → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (bare ++ `S)).type (some 46) fun x _ => do
    unless x.size == 46 do throwError "native initial sampler: original bare46 prehistory changed"
    let n := (← inferType x[1]!).appArg!
    let rpar := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
    let floor ← mkAppM ``HAdd.hAdd #[mkNatLit 16,rpar]
    let I := (← whnf (← inferType x[40]!)).bindingDomain!
    withLocalDeclD `rInit (mkConst ``Nat) fun rInit => do
      withLocalDeclD `hInitReserve (← mkAppM ``LE.le #[floor,rInit]) fun hBase => do
        let shift ← mkAppM ``HAdd.hAdd #[mkNatLit 3,← mkAppM ``HSub.hSub #[n,mkNatLit 1]]
        let rSrc ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[rInit,shift],mkNatLit 2]
        let sum ← mkAppM ``HAdd.hAdd #[rSrc,mkApp (mkConst `JanetCartan.ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder) n]
        withLocalDeclD `hRawDensityReserve (← mkAppM ``LE.le #[sum,x[31]!]) fun hRaw => do
          let facts := mkAppN (mkConst ``reserve_facts) #[n,rInit,x[31]!,hBase,hRaw]
          let x := x.set! 45 (.proj ``And 0 facts)
          let S ← bodyApp (bare ++ `S) x
          let some ps := S.find? (·.isAppOfArity (pos ++ `S) 47)
            | throwError "native initial sampler: original positive47 threshold absent"
          let original ← bodyApp (pos ++ `S) ps.getAppArgs
          let some native := original.find? (·.isAppOfArity (adm ++ `S) 32)
            | throwError "native initial sampler: original native32 threshold absent"
          let p32 := native.getAppArgs
          let ptype := (← whnf (← inferType (mkAppN (mkConst (adm ++ `labels)) p32))).bindingDomain!
          withLocalDeclD `hσbackground ptype fun hσ => do
            let p33 := p32.push hσ
            let orders := #[rSrc,← mkAppM ``le_refl #[rSrc],Expr.proj ``And 1 facts,hRaw]
            let high := p33 ++ #[rInit] ++ orders
            let raw := p33 ++ #[rSrc] ++ orders
            let p := x[:40].toArray ++ #[rInit,hBase,hRaw,hσ] ++ x[42:45].toArray
            let (A,hA) ← withLocalDeclD `i I fun i => do
              let C := mkAppN (mkConst (density ++ `initialC)) (high.push i)
              let hC := mkAppN (mkConst (density ++ `initialC_nonneg)) (high.push i)
              let sign ← mkAppM `le_of_lt #[Expr.proj ``And 0 p33[23]!]
              withLocalDeclD `j (mkConst ``Nat) fun j => do
                let a ← mkAppM ``HMul.hMul #[p33[21]!,mkApp C j]
                let h ← mkAppM `mul_nonneg #[sign,mkApp hC j]
                return (← mkLambdaFVars #[i,j] a,← mkLambdaFVars #[i,j] h)
            let args := (x.set! 40 A).set! 41 hA
            k ⟨p,args,p33,high,raw,I,hBase,hσ⟩

/-- One numerical maximum admits the high density inverse threshold as well as
all native bare/weighted/measured event thresholds, before any history. -/
elab "choose_original_native_initial_threshold " which:num : command => liftTermElabM <| withTransparency .reducible <| withStatic fun s => do
  let old := mkAppN (mkConst (bare ++ `S)) s.event46
  let high := mkAppN (mkConst (source ++ `operatorS)) s.source38
  let S := mkAppN (mkConst (ns ++ `S)) s.params
  let budgetPrefix := s.params[:44].toArray
  match which.getNat with
  | 0 | 1 =>
    let q := if which.getNat == 0 then `initialC else `initialC_nonneg
    let v ← withLocalDeclD `i s.index fun i => do
      mkLambdaFVars #[i] (mkAppN (mkConst (density ++ q)) (s.density38.push i))
    discard <| save q budgetPrefix v (which.getNat == 0)
  | 2 => discard <| save `sampler_initial_budget budgetPrefix s.event46[40]! true
  | 3 => discard <| save `sampler_initial_budget_nonneg budgetPrefix s.event46[41]!
  | 4 => discard <| save `S s.params (← mkAppM ``Max.max #[old,high]) true
  | 5 => discard <| save `event_le s.params (← mkAppM `le_max_left #[old,high]) false (some (← mkAppM ``LE.le #[old,S]))
  | 6 => discard <| save `operator_le s.params (← mkAppM `le_max_right #[old,high]) false (some (← mkAppM ``LE.le #[high,S]))
  | 7 => discard <| save `hS s.params (← mkAppM `le_trans #[mkAppN (mkConst (bare ++ `hS)) s.event46,mkAppN (mkConst (ns ++ `event_le)) s.params])
  | 8 =>
    let actual ← bodyApp (bare ++ `S) s.event46
    let some ps := actual.find? (·.isAppOfArity (pos ++ `S) 47)
      | throwError "native initial sampler: original positive47 threshold absent"
    let low := mkAppN (mkConst (pos ++ `native_le)) ps.getAppArgs
    let hb := mkAppN (mkConst (bare ++ `event_le)) s.event46
    let hn ← mkAppM `le_trans #[low,hb]
    discard <| save `native_le s.params (← mkAppM `le_trans #[hn,mkAppN (mkConst (ns ++ `event_le)) s.params])
  | _ => throwError "native initial sampler: unknown prehistory field"

private def withHistory (s : Static) (k : Array Expr → Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  withLocalDeclD `R₀ (mkConst ``Real) fun R => do
    let S := mkAppN (mkConst (ns ++ `S)) s.params
    withLocalDeclD `hReached (← mkAppM ``LE.le #[S,R]) fun hR => do
      let hb ← mkAppM `le_trans #[mkAppN (mkConst (ns ++ `event_le)) s.params,hR]
      let prev := mkAppN (mkConst (bare ++ `exists_with_native_individual_rows)) (s.event46 ++ #[s.hσ,R,hb])
      forallBoundedTelescope (← inferType prev) (some 4) fun hist _ => do
        let args := s.params ++ #[R,hR] ++ hist
        let next := mkAppN prev hist
        let hop ← mkAppM `le_trans #[mkAppN (mkConst (ns ++ `operator_le)) s.params,hR]
        let target := (← whnf (← inferType next)).bindingDomain!
        let native ← forallBoundedTelescope target (some 1) fun _ expected => do
          let some labels := expected.find? (·.isAppOfArity (adm ++ `labels) 39)
            | throwError "native initial sampler: missing original labels39 in actual profile target"
          pure labels.getAppArgs
        for i in [:33] do
          unless ← isDefEq native[i]! s.native33[i]! do throwError "native initial sampler: native fixed datum {i} differs"
        k args next (native[33:39].toArray.push hop)

private def withNativeHistory (s : Static) (k : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  withLocalDeclD `R₀ (mkConst ``Real) fun R => do
    let S := mkAppN (mkConst (ns ++ `S)) s.params
    withLocalDeclD `hReached (← mkAppM ``LE.le #[S,R]) fun hR => do
      let hn ← mkAppM `le_trans #[mkAppN (mkConst (ns ++ `native_le)) s.params,hR]
      let ho ← mkAppM `le_trans #[mkAppN (mkConst (ns ++ `operator_le)) s.params,hR]
      let native := mkAppN (mkConst (adm ++ `labels)) (s.native33 ++ #[R,hn])
      forallBoundedTelescope (← inferType native) (some 4) fun hist _ =>
        k (s.params ++ #[R,hR] ++ hist) (#[R,hn] ++ hist ++ #[ho])

/-- Produce the genuine higher-reserve size-σ initial profile directly from the
original native density (not any sampling event). The separate sampler field
uses the correct smaller reserve at the same coefficient scale. -/
elab "prove_original_native_initial_profile " which:num : command => liftTermElabM <| withTransparency .reducible <| withStatic fun s => withNativeHistory s fun args history => do
  match which.getNat with
  | 0 =>
    let field ← withLocalDeclD `i s.index fun i => do
      let high := mkAppN (mkConst (density ++ `initial_profile)) (s.density38 ++ history ++ #[i])
      mkLambdaFVars #[i] high
    discard <| save `native_initial_profile args field
  | 1 =>
    let full := mkAppN (mkConst (ns ++ `native_initial_profile)) args
    let scale ← mkAppM ``scale_at_native_threshold #[mkAppN (mkConst (adm ++ `hS)) s.native33[:32].toArray,history[1]!,history[2]!]
    let low ← withLocalDeclD `i s.index fun i => do
      let proof ← mkAppM ``profile_weaken_reserve #[scale,s.base,mkApp s.event46[41]! i,mkApp full i]
      mkLambdaFVars #[i] proof
    discard <| save `sampler_initial_profile args low
  | _ => throwError "native initial sampler: unknown physical initial profile field"

/-- Apply the unchanged original event after consuming its high scalar profile;
only the true joint uncut response and its quantitative jets remain. -/
elab "apply_original_event_with_native_initial" : command => liftTermElabM <| withTransparency .reducible <| withStatic fun s => withHistory s fun args next _ => do
  let actual := mkApp next (mkAppN (mkConst (ns ++ `sampler_initial_profile)) args)
  forallBoundedTelescope (← inferType actual) (some 2) fun resp t => do
    unless resp.size == 2 && (← whnf t).isAppOfArity ``Exists 2 do throwError "native initial sampler: lost the single original shift"
    discard <| save `exists_of_response_profiles (args ++ resp) (mkAppN actual resp)

end JanetCartan.PhysicalSampling.OriginalNativeInitialEventApplication
end
