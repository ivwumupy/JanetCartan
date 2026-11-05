module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalStaticReach
public import JanetCartan.Iteration.RevisedUniform.Scales
public import JanetCartan.Iteration.RevisedUniform.OriginalFinalCore
public import JanetCartan.Iteration.PhysicalInitialization.OriginalReference
public meta import Lean

/-!
# Dimension-only inputs to the original selected prehistory

The original extension, covectors, low-order margins, fixed band and coefficient
reserve are chosen before the original source scale. They are not changed when
the later moment/mean/Fourier depths are selected. This file provides the input
menu and the exact dependent instantiation of the frozen 101/105 producers.
Consumers: the fixed initialization of `UniformHistoryCorrection` and the same
original current, reference and common core (`main:prop:seed`,
`new:sec:order-of-choices`, `main:eq:displacement-budget`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
namespace JanetCartan.RevisedUniform.OriginalSelectedPrehistory
open PhysicalSeed PhysicalInitialization

/-- The protected reference is chosen at order six before the scale ceiling,
not at the later finite-moment smoothing order (`main:prop:seed`). -/
def protectedOrder : ℕ := 6

theorem protectedOrder_ge_six : 6 ≤ protectedOrder := le_rfl

/-- A finite maximum of every actual original numerical reserve, together with
the existing revised baseline. No target or accuracy occurs in this choice. -/
def reserve (d : ℕ) : ℕ :=
  max (RevisedScales.baselineOrder (d+1))
    (max 6 (max (RegularSector.FiniteEvolution.sectorLowOrder d + 2)
      (max (ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder (d+1))
        (max (20 * (d.succ+1) + 5)
          (16 + (RawPrimary.SliceBounds.rawSliceParameterOrder d.succ + d.succ + 1) +
            (3 + (d.succ-1)) + 2 + ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder d.succ)))))

/-- The one physical history derivative reserve (`main:eq:displacement-budget`). -/
def rStar (d : ℕ) : ℕ := max 8 (reserve d + 2)

theorem reserve_ge_baseline (d : ℕ) : RevisedScales.baselineOrder (d+1) ≤ reserve d :=
  le_max_left _ _

theorem reserve_fits (d : ℕ) : 2 + reserve d ≤ rStar d := by
  dsimp only [rStar]
  omega

theorem rStar_ge_eight (d : ℕ) : 8 ≤ rStar d := le_max_left _ _

theorem rStar_ge_sector (d : ℕ) : RegularSector.FiniteEvolution.sectorLowOrder d + 2 ≤ rStar d := by
  dsimp only [rStar,reserve]
  omega

theorem rStar_ge_carrier (d : ℕ) : ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder (d+1) ≤ rStar d := by
  dsimp only [rStar,reserve]
  omega

theorem rStar_ge_moment (d : ℕ) : 20 * (d.succ+1) + 5 ≤ rStar d := by
  dsimp only [rStar,reserve]
  omega

theorem rStar_ge_density (d : ℕ) :
    16 + (RawPrimary.SliceBounds.rawSliceParameterOrder d.succ + d.succ + 1) +
      (3 + (d.succ-1)) + 2 + ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder d.succ ≤ rStar d := by
  dsimp only [rStar,reserve]
  omega

theorem protectedOrder_le_rStar (d : ℕ) : protectedOrder ≤ rStar d := by
  have := rStar_ge_eight d
  dsimp only [protectedOrder]
  omega

/-- The very initial-order producer that simultaneously pays the physical map
loss and cubic convergence gap (`new:sec:order-of-choices`). -/
def kMin (d : ℕ) : ℕ := Classical.choose (RevisedScales.exists_initial_order (d+1) (rStar d))

theorem kMin_pos (d : ℕ) : 1 ≤ kMin d :=
  (Classical.choose_spec (RevisedScales.exists_initial_order (d+1) (rStar d))).1

theorem kMin_cubic (d : ℕ) : RevisedScales.cubicLoss (d+1) + 2 * growthExponent + 4 <
    (3-2*growthExponent) * (kMin d : ℝ) :=
  (Classical.choose_spec (RevisedScales.exists_initial_order (d+1) (rStar d))).2.1

theorem kMin_history (d : ℕ) : RevisedScales.displacementLoss (d+1) +
    bandExponent * ((rStar d : ℝ) + (d+1 : ℕ)/2) + 2 < (kMin d : ℝ) :=
  (Classical.choose_spec (RevisedScales.exists_initial_order (d+1) (rStar d))).2.2

/-- The prescribed finite extension menu contains every protected/fixed history
order, rather than using an empty set to avoid the actual initializer. -/
def orders (d : ℕ) : Finset ℕ := Finset.range (rStar d + 1)

theorem mem_orders {d j : ℕ} (hj : j ≤ rStar d) : j ∈ orders d := by
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)

theorem protectedOrder_mem_orders (d : ℕ) : protectedOrder ∈ orders d :=
  mem_orders (protectedOrder_le_rStar d)

theorem rStar_mem_orders (d : ℕ) : rStar d ∈ orders d := mem_orders le_rfl

/-- The original bare frame allowance already implied by 101, used only to
make a strictly positive earlier external margin. The actual frame is still
selected by the unchanged native producer, not chosen again at a stage. -/
def margin {d : ℕ} (hn : 5 ≤ d+1) : ℕ → ℝ := fun _ ↦
  min 1 (Classical.choose (PhysicalSampling.OriginalBare.exists_frame hn
    (PhysicalMean.OriginalCanonicalMomentAdmission.extraFrame_pos hn)) / 2)

theorem margin_pos {d : ℕ} (hn : 5 ≤ d+1) (j : ℕ) : 0 < margin hn j :=
  lt_min zero_lt_one (half_pos (Classical.choose_spec (PhysicalSampling.OriginalBare.exists_frame hn
    (PhysicalMean.OriginalCanonicalMomentAdmission.extraFrame_pos hn))).1)

theorem margin_pos_on_orders {d : ℕ} (hn : 5 ≤ d+1) : ∀ j ∈ orders d, 0 < margin hn j :=
  fun j _ ↦ margin_pos hn j

/-- Fixed strictly positive extra radii, subsequently constrained by the same
native bare/strong minima. This is not a replacement cutoff or extra cap. -/
def extraCaps {d : ℕ} (hn : 5 ≤ d+1) : PhysicalNormalInverse.StrongExtraCaps hn :=
  fun _ _ _ ↦ ⟨margin hn 0, margin_pos hn 0⟩

/-- A definite positive member of the very original source interval. -/
theorem half_mem_Ioc {c : ℝ} (hc : 0 < c) : c/2 ∈ Set.Ioc 0 c :=
  ⟨half_pos hc,(half_lt_self hc).le⟩

private theorem cap_positive : (0 : ℝ) < 1 := zero_lt_one

private theorem initial_trans {a b c : ℝ} (h : a ≤ b) (k : b ≤ c) : a ≤ c := h.trans k

end JanetCartan.RevisedUniform.OriginalSelectedPrehistory
end

public meta section
namespace JanetCartan.RevisedUniform.OriginalSelectedPrehistoryTemplate
open Lean Meta Elab Command
open PhysicalMean.OriginalCanonicalMomentAdmissionTemplate (withSelectedBefore)
open PhysicalMean.OriginalCanonicalStaticReachTemplate (withHistoryBand)

private def root := `JanetCartan.RevisedUniform.OriginalSelectedPrehistory
private def moments := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
private def statics := `JanetCartan.PhysicalMean.OriginalCanonicalStaticReach
private def native := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def graph := `JanetCartan.PhysicalSampling.OriginalGraphResponse.B
private def core := `JanetCartan.RevisedUniform.OriginalFinalCore
private def app (key : Name) (xs : Array Expr) := mkAppN (mkConst key) xs

private def progress (s : String) : MetaM Unit := do
  logInfo s
  if let some path ← IO.getEnv "JANET_SELECTED_PREHISTORY_TRACE" then
    IO.FS.withFile path .append fun h => do
      h.putStrLn s
      h.flush

private def save (key : Name) (xs : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let type ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars xs type)
  let value ← instantiateMVars (← mkLambdaFVars xs value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "selected original prehistory: free menu or unproved input escaped {key}"
    let missing := e.getUsedConstants.filter fun k => (env.find? k).isNone
    unless missing.isEmpty do throwError "selected original prehistory: unavailable producers {missing.toList}"
  let name := root ++ key
  progress s!"selected original prehistory: kernel checking {key}/{xs.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Dimension-only actual original initialization: unchanged original extension/center/frame/graph/source scale, fixed physical B=2 and both history-order gaps, and the single genuine initial threshold (main:prop:seed; new:sec:order-of-choices)."

/-- Deterministic expressions for every original free menu coordinate other
than the source scale. Their only external inputs are dimension and hn. -/
private def input (i : Nat) (args : Array Expr) : MetaM Expr := do
  let d := args[0]!
  let hn := args[1]!
  let n := app ``Nat.add #[d,mkNatLit 1]
  let byDim (k : Name) := app (root ++ k) #[d]
  let on (k : Name) := app (root ++ k) #[d,hn]
  let original (k : Name) := app (`JanetCartan.PhysicalInitialization ++ k) #[n,hn]
  match i with
  | 2 | 8 => pure (original `originalBallExtension)
  | 3 => pure (original `originalBallExtension_center)
  | 4 => pure (original `originalBallExtension_radius)
  | 5 => pure (original `originalCenterFamily)
  | 6 => pure (original `original_kCenter_ne_zero)
  | 7 => pure (original `originalCenterFamily_mem_domain)
  | 9 => pure (byDim `orders)
  | 10 | 11 => pure (on `margin)
  | 12 | 13 => pure (on `margin_pos_on_orders)
  | 14 | 16 => pure (← mkNumeral (mkConst ``Real) 1)
  | 15 | 17 => pure (mkConst ``OriginalSelectedPrehistory.cap_positive)
  | 18 => pure (on `extraCaps)
  | 19 => pure (mkConst (root ++ `protectedOrder))
  | 20 => pure (mkConst (root ++ `protectedOrder_ge_six))
  | 21 => pure (app (root ++ `sigma) #[d,hn])
  | 22 => pure (app (root ++ `sigma_mem_ceiling) #[d,hn])
  | 23 => pure (byDim `rStar)
  | 24 => pure (byDim `kMin)
  | 25 => pure (byDim `rStar_ge_eight)
  | 26 => pure (byDim `rStar_ge_sector)
  | 27 => pure (byDim `kMin_history)
  | 28 => pure (byDim `rStar_ge_carrier)
  | 29 => pure (byDim `rStar_ge_moment)
  | 30 => pure (byDim `rStar_ge_density)
  | _ => throwError "selected original prehistory: not a chosen menu coordinate {i}"

/-- Open the *actual dependent* Tref31 telescope, preserving only d,hn, and
insert every earlier menu term before opening a later proof. At count21 no
sigma or history data is touched; count31 produces the fixed threshold args. -/
def withDimensionInputs (count : Nat)
    (next : Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  unless count == 21 || count == 31 do throwError "selected original prehistory: invalid prefix"
  let rec loop (fuel i : Nat) (type : Expr) (args kept : Array Expr) : MetaM Unit := do
    match fuel with
    | 0 => next args kept type
    | k+1 =>
      let .forallE name dom body bi := type.consumeMData
        | throwError "selected original prehistory: dependent telescope ended at {i}"
      if i < 2 then
        withLocalDecl name bi dom fun x => loop k (i+1) (body.instantiate1 x) (args.push x) (kept.push x)
      else
        let v ← input i args
        loop k (i+1) (body.instantiate1 v) (args.push v) kept
  loop count 0 (← getConstInfo (statics ++ `Tref)).type #[] #[]

/-- Recover the named 101 and native44 arguments after dimension-only
selection. This is substitution into their original dependent callbacks,
never equality of independently initialized charts or samples. -/
def withDimensionStatic (next : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  withSelectedBefore 44 fun raw selected _ => do
    let rawTerms ← raw.mapM (mkLambdaFVars selected ·)
    withHistoryBand fun selected fixed _ => do
      let native := rawTerms.map (·.beta selected)
      let selectedTerms ← selected.mapM (mkLambdaFVars fixed ·)
      let nativeTerms ← native.mapM (mkLambdaFVars fixed ·)
      withDimensionInputs 31 fun chosen dh _ => do
        let sel := selectedTerms.map (·.beta chosen)
        let nat := nativeTerms.map (·.beta chosen)
        unless chosen.size == 31 && sel.size == 33 && nat.size == 44 && dh.size == 2 do
          throwError "selected original prehistory: dimension-only argument sizes changed"
        for term in nat do
          for x in raw do
            if x.isFVar && term.containsFVar x.fvarId! then throwError "selected original prehistory: original free static input escaped"
        next dh chosen sel nat

/-- Dimension-only native50: the sole initial gate is the genuine 105 Tref.
The exact unchanged physical history tail is opened after inserting the
proved native reached bound. No caller-supplied analytic profile occurs. -/
def withDimensionHistory (next : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  withDimensionStatic fun dh chosen selected fixed => do
    let remaining ← instantiateForall (← getConstInfo `JanetCartan.PhysicalMean.OriginalCanonicalActual.G).type fixed
    forallBoundedTelescope remaining (some 1) fun rs atReach => do
      unless rs.size == 1 do throwError "selected original prehistory: missing actual R0"
      let .forallE _ _ body _ := atReach.consumeMData | throwError "selected original prehistory: missing actual reach binder"
      let R := rs[0]!
      let T := app (root ++ `Tref) dh
      withLocalDeclNoLocalInstanceUpdate `hInitial .default (← mkAppM ``LE.le #[T,R]) fun hR => do
        let hCommon := app (root ++ `common_reached) (dh ++ #[R,hR])
        let hNative := app (moments ++ `native_reached) (selected ++ #[R,hCommon])
        forallBoundedTelescope (body.instantiate1 hNative) (some 4) fun history _ => do
          unless history.size == 4 do throwError "selected original prehistory: actual history4 changed"
          let params := dh ++ #[R,hR] ++ history
          let actual := fixed ++ #[R,hNative] ++ history
          let selected39 := selected ++ #[R,hCommon] ++ history
          next params actual selected39 chosen

elab "select_original_dimension_ceiling " which:num : command => liftTermElabM do
  withDimensionInputs 21 fun early dh _ => do
    let C := app (moments ++ `ceiling) early
    let hC := app (moments ++ `ceiling_pos) early
    let named := app (root ++ `ceiling) dh
    match which.getNat with
    | 0 => save `ceiling dh C true
    | 1 => save `ceiling_pos dh hC false (some (← mkAppM ``LT.lt #[← mkNumeral (mkConst ``Real) 0,named]))
    | 2 => save `sigma dh (← mkAppM ``HDiv.hDiv #[named,← mkNumeral (mkConst ``Real) 2]) true
    | 3 => save `sigma_mem_ceiling dh (app ``OriginalSelectedPrehistory.half_mem_Ioc #[named,app (root ++ `ceiling_pos) dh])
    | 4 => save `gamma dh (app (moments ++ `AtPoint.gamma) early) true
    | 5 => save `gamma_pos dh (app (moments ++ `AtPoint.gamma_pos) early)
    | 6 => save `gamma_le_tolerance dh (app (moments ++ `AtPoint.gamma_le_tolerance) early)
    | _ => throwError "selected original prehistory: unknown early selector mode"

elab "select_original_dimension_threshold " which:num : command => liftTermElabM do
  withDimensionStatic fun dh chosen selected _ => do
    let common := app (moments ++ `commonS) selected
    let value := app (statics ++ `Tref) chosen
    let named := app (root ++ `Tref) dh
    let hCommon := app (statics ++ `commonS_le_Tref) chosen
    match which.getNat with
    | 0 => save `Tref dh value true
    | 1 => save `two_le_Tref dh (app ``OriginalSelectedPrehistory.initial_trans #[← mkNumeral (mkConst ``Real) 2,common,named,app (moments ++ `commonS_ge_two) selected,hCommon])
    | 2 =>
      withLocalDeclD `R₀ (mkConst ``Real) fun R => do
        withLocalDeclD `hInitial (← mkAppM ``LE.le #[named,R]) fun hR => do
          save `common_reached (dh ++ #[R,hR]) (app ``OriginalSelectedPrehistory.initial_trans #[common,named,R,hCommon,hR])
    | 3 => save `Saux_le_Tref dh (app (statics ++ `Saux_le_Tref) chosen)
    | _ => throwError "selected original prehistory: unknown fixed threshold mode"

/-- Recover the actual reference through the original graph42 and its S34
admission. Every returned regular25 term closes over dimension and hn alone;
no source, frame, cutoff, history or sample is reconstructed. -/
def withDimensionReference
    (next : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  withDimensionHistory fun params actual _ _ => do
    let query := app (native ++ `uncut_response_jets) actual
    forallBoundedTelescope (← inferType query) (some 2) fun rowColor _ => do
      let t ← inferType (mkAppN query rowColor)
      let some g := t.find? (·.isAppOfArity graph 42) |
        throwError "selected original prehistory: lost original graph42"
      if g.hasLooseBVars then throwError "selected original prehistory: graph depends on later observation"
      let gt := (← instantiateForall (← getConstInfo graph).type g.getAppArgs[:37].toArray).consumeMData
      let .forallE _ reached _ _ := gt | throwError "selected original prehistory: missing graph reach"
      unless reached.isAppOfArity ``LE.le 4 do throwError "selected original prehistory: non-numeric graph gate"
      let S := reached.getAppArgs[2]!
      unless S.isAppOfArity (regular ++ `Graph.S) 34 do throwError "selected original prehistory: changed original S34"
      let fixed := S.getAppArgs
      let ref := fixed[:23].toArray ++ #[fixed[25]!,app (regular ++ `Graph.regular_scale) fixed[:27].toArray]
      let dh := params[:2].toArray
      for arg in ref do
        let closed ← mkLambdaFVars dh arg
        if closed.hasFVar || closed.hasLooseBVars then
          throwError "selected original prehistory: history, row or observation entered regular25"
      next dh actual ref

/-- The global original admission39, not the per-row comparison current. Its
entire argument list closes over the same eight physical-history inputs. -/
def withDimensionCurrent
    (next : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  withDimensionHistory fun params actual _ _ =>
    PhysicalMean.OriginalCanonicalCurrentApplication.withCurrentAt actual fun current => do
      unless current.size == 39 do throwError "selected original prehistory: global admission39 changed"
      for x in current do
        let closed ← mkLambdaFVars params x
        if closed.hasFVar || closed.hasMVar || closed.hasLooseBVars then
          throwError "selected original prehistory: new free menu or row entered current39"
      next params actual current

/-- Keep the unchanged actual row/color/node tail available to 101's chosen
source and moment chart. This callback does not choose any of those points. -/
def withDimensionAtPoint
    (next : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  withDimensionHistory fun params native selected _ => do
    let G := app `JanetCartan.PhysicalMean.OriginalCanonicalActual.G native
    forallBoundedTelescope (← inferType G) (some 3) fun point _ => do
      unless point.size == 3 do throwError "selected original prehistory: expected exact row/color/node tail"
      next (params ++ point) (native ++ point) (selected ++ point)

elab "select_original_dimension_geometry " which:num : command => liftTermElabM do
  withDimensionReference fun dh _ ref => do
    let fixed := ref[:23].toArray
    let originalG := app (regular ++ `Gref) ref
    let originalD := app (core ++ `D) fixed
    let originalSmooth := app (core ++ `Dsmoothing) fixed
    let rename (t : Expr) := t.replace fun e =>
      if e == originalG then some (app (root ++ `Gref) dh)
      else if e == originalD then some (app (root ++ `D) dh)
      else if e == originalSmooth then some (app (root ++ `Dsmoothing) dh)
      else none
    let forward (key old : Name) (args : Array Expr) := do
      let v := app (core ++ old) args
      save key dh v false (some (rename (← inferType v)))
    match which.getNat with
    | 0 => save `Gref dh originalG true
    | 1 => save `Dsmoothing dh originalSmooth true
    | 2 => save `D dh originalD true
    | 3 => save `Gmap dh (← mkAppM `JanetCartan.FlatReference.map #[app (root ++ `Gref) dh]) true
    | 4 => forward `D_isCompact `isCompact fixed
    | 5 => forward `D_zero_mem_interior `zero_mem_interior fixed
    | 6 => forward `D_subset_chart `D_subset_chart ref
    | 7 => forward `source_interval `source_interval ref
    | 8 => forward `target_reduction `target_reduction ref
    | _ => throwError "selected original prehistory: unknown fixed geometry mode"

elab "select_original_dimension_current " which:num : command => liftTermElabM do
  withDimensionCurrent fun params _ current => do
    let currentRoot := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current
    let rawQ := app (currentRoot ++ `Q0) current
    match which.getNat with
    | 0 => save `Q0 params rawQ true
    | 1 =>
      let h := app (currentRoot ++ `source_regular) current
      let t := (← inferType h).replace fun e => if e == rawQ then some (app (root ++ `Q0) params) else none
      save `source_regular params h false (some t)
    | _ => throwError "selected original prehistory: unknown global current mode"

end JanetCartan.RevisedUniform.OriginalSelectedPrehistoryTemplate
end
