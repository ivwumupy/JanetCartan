module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemainders
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-! # The actual physical carrier in the full-inverse family

The observed inverse admits a frequency independent of the source rate.  The
physical atom does not: it queries that family at frequency `τ⁻¹`, with the
same `τ` and scalar in its payload.  We construct this query from the original
source and its own primitive admissions, and apply the already uniform observed
remainder. In particular neither the tail depth nor its cost is chosen from a
history (`app:ch_regular:eq:inverse-remainder`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex

/-- The single original physical query, not a statement identifying two
independent fields of an arbitrary raw query. -/
def carrierIndex {d : ℕ} {A : Type} (R₀ : ℝ) (stage : ℕ)
    (u : Fin stage → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
    (ell : Fin stage → ℕ) (K τ size : ℝ) (r : A) : OriginalHistoryFamily.RawIndex d (ℝ × A) :=
  ⟨R₀,stage,u,ell,τ⁻¹,K,size,(τ,r)⟩

theorem carrier_one_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : 1 ≤ τ⁻¹ :=
  (one_le_inv₀ hτ).2 hτ1

end JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate
private def out := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def fam := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def appl (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def emit (field : Name) (xs : Array Expr) (v : Expr) (data := false)
    (t : Option Expr := none) : MetaM Expr := do
  let h ← store (out ++ field) xs v data t
  addDocStringCore (out ++ field) "Same original physical source at its literal inverse rate, using the original history and sigma-scaled primitive scalar profile (app:ch_regular:eq:inverse-remainder)."
  return h
private def conjs (hs : List Expr) : MetaM Expr := do
  match hs with
  | [] => throwError "empty native admission"
  | [h] => return h
  | h :: tail => mkAppM ``And.intro #[h,← conjs tail]

/-- Select the two uniform constants *before* querying the physical family. -/
elab "retain_physical_inverse_depth_cost" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (fam ++ `admitted_remainder)).type (some 46) fun xs _ => do
    unless xs.size == 46 do throwError "expected static44 plus Sobolev and parameter orders"
    let h := appl (fam ++ `admitted_remainder) xs
    let N ← emit `depth xs (← mkAppM ``Classical.choose #[h]) true
    let costExists ← mkAppM ``Classical.choose_spec #[h]
    let D ← emit `cost xs (← mkAppM ``Classical.choose #[costExists]) true
    let bound ← mkAppM ``Classical.choose_spec #[costExists]
    let sides := (← inferType bound).getAppArgs
    let nonneg ← mkAppM ``LE.le #[← mkNumeral (mkConst `Real) 0,D]
    discard <| emit `cost_nonneg xs (.proj ``And 0 bound) false (some nonneg)
    let originalN ← mkAppM ``Classical.choose #[h]
    let originalD ← mkAppM ``Classical.choose #[costExists]
    let t := sides.back!.replace fun e =>
      if e == originalN then some N else if e == originalD then some D else none
    discard <| emit `on_admitted xs (.proj ``And 1 bound) false (some t)

/-- `xs` uses a single reached threshold.  Insert the already-proved native
source threshold inequality instead of requiring it as another premise. -/
def withPhysicalInputs (go : Array Expr → Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (fam ++ `admitted_remainder)).type (some 44) fun base _ => do
    let fixed := base[:39].toArray
    let family := base[:41].toArray
    let source := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
    let origType ← inferType (appl (source ++ `a) fixed)
    forallBoundedTelescope origType (some 1) fun rr type => do
      let R₀ := rr[0]!
      withLocalDeclD `hReached (← mkAppM ``LE.le #[appl (fam ++ `S) family,R₀]) fun hR => do
        let hSource ← mkAppM ``le_trans #[appl (fam ++ `source_threshold) family,hR]
        let .forallE _ _ rest _ := type | throwError "lost native source threshold"
        forallBoundedTelescope (rest.instantiate1 hSource) (some 12) fun tail _ => do
          let s := fixed ++ #[R₀,hSource] ++ tail
          unless s.size == 53 do throwError "changed original physical source53"
          let scalar ← mkAppM ``Subtype.val #[s[49]!]
          let i ← mkAppM (out ++ `carrierIndex) #[R₀,s[41]!,s[42]!,s[43]!,s[45]!,s[47]!,s[50]!,scalar]
          let rawType := (← inferType (appl (fam ++ `Point.source) base)).bindingDomain!
          unless rawType.isAppOfArity ``Subtype 2 do throwError "lost native admitted point"
          let both := (← whnf (rawType.getAppArgs[1]!.beta #[i])).getAppArgs
          let hist ← whnf both[0]!
          let winType := hist.getAppArgs[1]!.getAppArgs[1]!.getAppArgs[1]!.getAppArgs[1]!.getAppArgs[0]!
          withLocalDeclD `hRateOne (← mkAppM ``LE.le #[s[47]!,← mkNumeral (mkConst `Real) 1]) fun hτ1 => do
            withLocalDeclD `hScaleWindow winType fun hWin => do
              let hρ ← mkAppM (out ++ `carrier_one_le) #[s[48]!,hτ1]
              let admitted ← conjs [hR,s[44]!,hρ,s[46]!,hWin,s[51]!]
              let sourceAdmission ← conjs [s[48]!,← mkAppM ``Subtype.property #[s[49]!],s[52]!]
              let proof ← mkAppM ``And.intro #[admitted,sourceAdmission]
              let point := mkAppN (mkConst ``Subtype.mk [.succ .zero]) #[rawType.getAppArgs[0]!,rawType.getAppArgs[1]!,i,proof]
              go (base ++ #[R₀,hR] ++ tail ++ #[hτ1,hWin]) base s point proof

elab "apply_physical_inverse_remainder" : command => liftTermElabM do
  withPhysicalInputs fun inputs base _ point h => do
    let i := point.getAppArgs[2]!
    let q ← emit `index inputs i true
    let hp ← emit `admitted inputs h false (some (point.getAppArgs[1]!.beta #[q]))
    let pp := point.getAppArgs
    let member ← emit `point inputs (mkAppN point.getAppFn #[pp[0]!,pp[1]!,q,hp]) true
    let src := appl (fam ++ `Point.source) (base.push member)
    discard <| emit `source inputs src true
    let φ := appl (fam ++ `Point.φ) (base.push member)
    discard <| emit `phase inputs φ true
    let continuation := appl (out ++ `on_admitted) base
    forallBoundedTelescope (← inferType continuation) (some 2) fun sk _ => do
      let h := mkAppN continuation (sk ++ #[q,hp])
      discard <| emit `physical_remainder (inputs ++ sk) h
  logInfo "applied canonical observed full inverse at the original physical carrier tau^-1 and payload (tau,scalar); common depth/cost before history, native primitive source admission proved"

end JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
end

set_option maxHeartbeats 2400000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
retain_physical_inverse_depth_cost
apply_physical_inverse_remainder
