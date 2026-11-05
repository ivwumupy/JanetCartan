module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# The native event from one original combined σ interval

Neither a sampling tolerance, a signed/natural/regular scale proof, a density
profile, nor a derivative cost is new input. The fixed high regular order also
implies all low reserve tests. The remaining scalar/radius/finite-regularity
choices precede R₀ and the single physical history (`new:sec:order-of-choices`).
-/

@[expose] public section
namespace JanetCartan.PhysicalSampling.OriginalActualEventApplication
open RawPrimary.SliceBounds RegularSector.FiniteEvolution FourierIntegral
open ContinuumRow.CanonicalCarrier
private theorem coarse_reserves {d rStar : ℕ}
    (h : (16+(rawSliceParameterOrder (d+1)+(d+1)+1)+(3+((d+1)-1))+2)+canonicalCarrierLowOrder (d+1) ≤ rStar) :
    8 ≤ rStar ∧ sectorLowOrder d + 2 ≤ rStar ∧ canonicalCarrierLowOrder (d+1) ≤ rStar ∧
    20*((d+1)+1)+5 ≤ rStar := by
  simp only [canonicalCarrierLowOrder,rawSliceParameterOrder,rawSliceJetOrder,Nat.add_sub_cancel] at h
  simp only [sectorLowOrder,RegularSector.Characteristic.UniformEvolution.retardedCoefficientOrder,
    WholeImageGeometry.wholeImagePhaseReserve,LowBounds.primitiveNormalReserve,
    FullLowBounds.fullLowReserve_eq,canonicalCarrierLowOrder]
  omega
end JanetCartan.PhysicalSampling.OriginalActualEventApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalActualEventApplication
open Lean Meta Elab Command
private def ps := `JanetCartan.PhysicalSampling
private def ns := ps ++ `OriginalActualEvent
private def gr := ps ++ `OriginalNativeGradedEvent
private def bs := ps ++ `OriginalBareScale
private def app (n : Name) (v : Array Expr) := mkAppN (mkConst n) v
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (Nat.repeat (fun e => Expr.proj ``And 1 e) j h)
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def save (n : Name) (xs : Array Expr) (e : Expr) (data := false) (goal : Option Expr := none) : MetaM Unit := do
  let ty ← match goal with | none => inferType e | some t => pure t
  let type ← instantiateMVars (← mkForallFVars xs ty)
  let value ← instantiateMVars (← mkLambdaFVars xs e)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "actual physical event: open {n}"
  let name := ns ++ n
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  logInfo m!"checked original one-scale full physical event: {n} at {xs.size} inputs"

/-- Build every original44 prehistory admission from the one before-source cap
and the one actual high regularity order (rather than separate graph, native
background or signed-source assumptions). -/
private def withCombined (k : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let S := mkConst (gr ++ `S)
  forallBoundedTelescope (← inferType S) (some 24) fun p _ => do
    let γ := app (bs ++ `γ) p
    let fixed := p ++ #[γ,app (bs ++ `γ_pos) p,app (bs ++ `γ_le_sampler) p]
    let both := app (bs ++ `scale_admissions) p
    forallBoundedTelescope (← inferType both) (some 2) fun sig _ => do
      let admissions := mkAppN both sig
      let four := Expr.proj ``And 0 admissions
      let init := fixed ++ #[sig[0]!,part four 0]
      forallBoundedTelescope (← inferType (mkAppN S init)) (some 4) fun nums _ => do
        let n := (← inferType p[1]!).appArg!
        let r := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
        let rs ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[r,n],mkNatLit 1]
        let shift ← mkAppM ``HAdd.hAdd #[mkNatLit 3,← mkAppM ``HSub.hSub #[n,mkNatLit 1]]
        let ri ← mkAppM ``HAdd.hAdd #[mkNatLit 16,rs]
        let rr ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[ri,shift],mkNatLit 2]
        let raw ← mkAppM ``HAdd.hAdd #[rr,mkApp (mkConst `JanetCartan.ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder) n]
        withLocalDeclD `hFixedOrder (← mkAppM ``LE.le #[raw,nums[2]!]) fun h => do
          let co := app ``coarse_reserves #[p[0]!,nums[2]!,h]
          let low := init ++ nums ++ #[part co 0,part co 1]
          forallBoundedTelescope (← inferType (mkAppN S low)) (some 1) fun order _ => do
            withLocalDeclD `hQuadratureOrder (← mkAppM ``LT.lt #[mkNatLit 0,p[2]!]) fun hp => do
              let grade44 := low ++ order ++ #[part four 1,part four 2,part co 2,tail co 3,h,Expr.proj ``And 1 admissions,tail four 3,hp]
              let xs := p ++ sig ++ nums ++ #[h] ++ order ++ #[hp]
              unless grade44.size == 44 && xs.size == 33 do throwError "actual physical event: changed causal early33 or graded44"
              k xs grade44

private def withStoredCombined (run : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let ci ← getConstInfo (ns ++ `S)
  let some value := ci.value? | throwError "actual physical event: missing original33 threshold body"
  forallBoundedTelescope ci.type (some 33) fun p _ => do
    let q := (value.beta p).headBeta
    unless q.isAppOfArity (gr ++ `S) 44 do throwError "actual physical event: changed saved original44 maximum"
    run p q.getAppArgs

elab "pack_actual_original_event " which:num : command => liftTermElabM <| withTransparency .reducible <| (if which.getNat == 0 then withCombined else withStoredCombined) fun p q => do
  let S := app (ns ++ `S) p
  match which.getNat with
  | 0 => save `S p (app (gr ++ `S) q) true
  | 1 => save `hS p (app (gr ++ `hS) q) false (some (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 2,S]))
  | 2 => save `Cresp p (app (gr ++ `Cresp) q) true
  | 3 => save `Cresp_nonneg p (app (gr ++ `Cresp_nonneg) q)
  | 4 | 5 =>
    withLocalDeclD `R₀ (mkConst ``Real) fun R => do
      withLocalDeclD `hReached (← mkAppM ``LE.le #[S,R]) fun hR => do
        let key := if which.getNat == 4 then `uncut_response_jets else `exists_on_original_history
        let prior := app (gr ++ key) (q ++ #[R,hR])
        forallBoundedTelescope (← inferType prior) (some 4) fun hist target => do
          if which.getNat == 5 then
            unless (← whnf target).isAppOfArity ``Exists 2 do throwError "actual physical event: lost only shift"
          save key (p ++ #[R,hR] ++ hist) (mkAppN prior hist)
  | _ => throwError "actual physical event: invalid publication"

end JanetCartan.PhysicalSampling.OriginalActualEventApplication
end
