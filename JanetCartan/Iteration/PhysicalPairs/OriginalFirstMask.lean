module
public import JanetCartan.Iteration.PhysicalPairs.OriginalMaskRows
public import JanetCartan.Iteration.PhysicalPairs.MeasuredSourceCost

/-! # The native signed-family admission from the original full-amplitude ledger

The ONLY quantitative wave input here is the uniform order-by-order envelope
of the two literal demodulated full derivatives. Its physical producer is the
original reconstructed primary family, not a localization or observed-chain
hypothesis. All geometric, row, cutoff, normalization and inverse interfaces
below are the previously constructed original ones. `main:prop:pairs`,
`app:ch_regular:lem:finite-chain`, `app:ch_pairs:prop:pairs-lag-sum`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius NNReal ENNReal
namespace JanetCartan.PhysicalPairs.OriginalFirstMask
variable {d N : ℕ} {β : Type}
local notation "E" => Euclidean (d+1)

/-- The remaining quantitative primary ledger at the two actual external nodes;
no phase-space mask, decay rate, or guessed solution occurs in it. -/
def FullDerivativeProfile (U : Set E) (A B : β → E → Matrix (Fin N) (Fin (d+1)) ℂ) (C : ℕ → ℝ) (K : β → ℝ) : Prop :=
  ∀ t y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j (A t) y‖ ≤ C j*(K t)^j ∧ ‖iteratedFDeriv ℝ j (B t) y‖ ≤ C j*(K t)^j

theorem left_bound {U : Set E} {A B : β → E → Matrix (Fin N) (Fin (d+1)) ℂ} {C K}
    (h : FullDerivativeProfile U A B C K) : ∀ t y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j (A t) y‖ ≤ C j*(K t)^j :=
  fun t y hy j ↦ (h t y hy j).1

theorem right_bound {U : Set E} {A B : β → E → Matrix (Fin N) (Fin (d+1)) ℂ} {C K}
    (h : FullDerivativeProfile U A B C K) : ∀ t y, y ∈ U → ∀ j, ‖iteratedFDeriv ℝ j (B t) y‖ ≤ C j*(K t)^j :=
  fun t y hy j ↦ (h t y hy j).2

def phaseCost (D : ℕ → ℝ) (j : ℕ) : ℝ := 2*(D (j+1)+D (j+2))
theorem phaseCost_nonneg (D : ℕ → ℝ) (h : ∀ j, 0 ≤ D j) (j : ℕ) : 0 ≤ phaseCost D j :=
  mul_nonneg (by norm_num) (add_nonneg (h _) (h _))

theorem support_refl (χ : E → ℝ) : tsupport χ ⊆ tsupport χ := fun _ h ↦ h

theorem on_chart (U : Set E) (f : E → ℝ) (h : ContDiff ℝ ∞ f) : ContDiffOn ℝ ∞ f U := h.contDiffOn
theorem one_of_two {r : ℝ} (hr : 2 ≤ r) : 1 ≤ r := le_trans (by norm_num) hr

theorem on_support {U K : Set E} (χ φ : E → ℝ) (hU : tsupport χ ⊆ U)
    (h : ∀ y ∈ U, gradient φ y ∈ K) : ∀ y ∈ tsupport χ, gradient φ y ∈ K := fun y hy ↦ h y (hU hy)

theorem jets_on_support {U : Set E} (χ φ : E → ℝ) (hU : tsupport χ ⊆ U) (P : ℕ → ℝ) (M : ℝ)
    (h : ∀ y ∈ U, ∀ j, ‖iteratedFDeriv ℝ (j+1) φ y‖ ≤ P j*M^j) :
    ∀ y ∈ tsupport χ, ∀ j, 1 ≤ j → ‖iteratedFDeriv ℝ (j+1) φ y‖ ≤ P j*M^j := fun y hy j _ ↦ h y (hU hy) j
end JanetCartan.PhysicalPairs.OriginalFirstMask
end

public meta section
set_option warningAsError true
set_option maxHeartbeats 1100000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.OriginalFirstMask
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def data := `JanetCartan.PhysicalPairs.OriginalSignedData
private def rows := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def geo := `JanetCartan.PhysicalPairs.OriginalMaskGeometry
private def fr := `JanetCartan.PhysicalPairs.OriginalSignedFrames
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def mask := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def poly := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def cost := `JanetCartan.PhysicalPairs.MeasuredSourceCost
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def down (v : Expr) : Nat → Expr
  | 0 => v
  | j+1 => down (.proj ``And 1 v) j
private def part (v : Expr) (j : Nat) := Expr.proj ``And 0 (down v j)
private def nativeArgs (base : Array Expr) (b : Expr) : Array Expr := Id.run do
  let mut p := base
  let mut t := b
  for _ in [:12] do
    p := p.push (.proj ``PSigma 0 t)
    t := .proj ``PSigma 1 t
  return p

elab "publish_native_first_mask " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `Labels)).type (some 37) fun base _ => do
    let d := base[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := a `JanetCartan.embeddingDimension #[n]
    let β := a (hist ++ `Labels) base
    let emb := a (hist ++ `historyMap) base
    let gf := (← inferType emb).bindingBody!
    let fix := gf.getAppArgs[:23].toArray
    let V := a (mask ++ `chart) fix
    let W := a (world ++ `W) fix
    let hW := a (world ++ `W_measurable) fix
    let hχ := a (mask ++ `χ₂_smooth) fix
    let hψ := a (mask ++ `χsrc_smooth) fix
    let χ := (← inferType hχ).appArg!
    let ψ := (← inferType hψ).appArg!
    let hχV := a (mask ++ `χ₂_support_chart) fix
    let hV := a (mask ++ `chart_open) fix
    let hc := a (mask ++ `χ₂_compact) fix
    let supp ← mkAppM ``tsupport #[χ]
    let Ksrc := a `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.Ksource base[:22].toArray
    let sa := ((← getConstInfo (poly ++ `GraphFamily)).value! (allowOpaque := true)).beta gf.getAppArgs
    let coeff := sa.getAppArgs.back!.getAppArgs
    let AQ := a (op ++ `AQ) coeff
    let hAQ := a (op ++ `fact1) coeff
    let Dphase := a (fr ++ `jointProfile) base[:36].toArray
    let P := a (ns ++ `phaseCost) #[Dphase]
    let hp := a (ns ++ `phaseCost_nonneg) #[Dphase,a (fr ++ `jointProfile_nonneg) base[:36].toArray]
    let X := a (rows ++ `bumpProfile) base
    let Y := a (rows ++ `sourceProfile) base
    let hX := a (rows ++ `bumpProfile_nonneg) base
    let hY := a (rows ++ `sourceProfile_nonneg) base
    let chart (f h : Expr) := a (ns ++ `on_chart) #[d,V,f,h]
    withLocalDeclD `signedLabel β fun t => do
      let point := nativeArgs base t
      let history := a (hist ++ `measured_history) point
      let now := point[:36].toArray ++ #[point[37]!,part history 0] ++ point[39:43].toArray
      let fn (e : Expr) := mkLambdaFVars #[t] e
      let raw := Expr.proj ``Subtype 0 (mkApp emb t)
      let get (k : Name) := a (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ k) #[d,mkConst ``Unit,raw]
      if piece.getNat == 0 then
        let zTy := (← inferType (a (data ++ `uncut) point)).bindingDomain!
        discard <| store (ns ++ `Waves) base (← mkForallFVars #[t] zTy) true (some (mkSort .one))
        return
      if piece.getNat == 1 then
        for (k,v) in [(`frequency,get `lam),(`fine,get `K),(`frame,a (quad ++ `Q) now),(`phase,a (geo ++ `phase) point),(`minus,point[45]!)] do
          discard <| store (ns ++ k) base (← fn v) true
        return
      let ρ := a (ns ++ `frequency) base
      let M := a (ns ++ `fine) base
      let QT := a (ns ++ `frame) base
      let phase := a (ns ++ `phase) base
      let sign := a (ns ++ `minus) base
      let WT := a (ns ++ `Waves) base
      withLocalDeclD `fullSampledWaves WT fun z => do
        let zs := base.push z
        let row := point.push (mkApp z t)
        if piece.getNat == 2 then
          for (k,v) in [(`measured,a (data ++ `measured) row),(`complexSource,a (data ++ `complex_input) row),
              (`left,a (rows ++ `leftAmplitude) row),(`right,a (rows ++ `rightAmplitude) row)] do
            discard <| store (ns ++ k) zs (← fn v) true
          return
        let A := a (ns ++ `left) zs
        let B := a (ns ++ `right) zs
        let u := a (ns ++ `measured) zs
        let fnType ← mkArrow (mkConst ``Nat) (mkConst ``Real)
        withLocalDeclD `amplitudePrice fnType fun C => do
          let cPrefix := base.push C
          let hCType ← withLocalDeclD `jet (mkConst ``Nat) fun j => do
            mkForallFVars #[j] (← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,mkApp C j])
          withLocalDeclD `nonnegativePrice hCType fun hC => do
            let cData := cPrefix.push hC
            let pfLow := a (cost ++ `exists_cost) #[d,N,supp,hc,X,Y,AQ,C,hX,hY,hAQ,hC]
            if piece.getNat == 3 then
              discard <| store (ns ++ `cost_before_sources) cData pfLow
              return
            let low := a (ns ++ `cost_before_sources) cData
            let price ← mkAppM ``Classical.choose #[low]
            if piece.getNat == 4 then
              let name ← store (ns ++ `sourceNormCost) cData price true
              let positive := part (← mkAppM ``Classical.choose_spec #[low]) 0
              discard <| store (ns ++ `sourceNormCost_nonneg) cData positive false
                (some ((← inferType positive).replace fun e => if e == price then some name else none))
              return
            let ledgerArgs := #[d,N,β,V,A,B,C,M]
            let ledger := a (ns ++ `FullDerivativeProfile) ledgerArgs
            withLocalDeclD `completeDerivativeLedger ledger fun hA => do
              let inputs := zs ++ #[C,hC,hA]
              let left := a (ns ++ `left_bound) (ledgerArgs.push hA)
              let right := a (ns ++ `right_bound) (ledgerArgs.push hA)
              let window := part (a (hist ++ `native_window) point) 0
              let rowWave (s : Name) := a (rows ++ s) row
              let baseRow (s : Name) := a (rows ++ s) point
              let hM := part history 3
              if piece.getNat == 5 then
                let hgrad := a (ns ++ `on_support) #[d,V,Ksrc,χ,mkApp phase t,hχV,a (geo ++ `gradient_in_source) point]
                let hj := a (ns ++ `jets_on_support) #[d,V,χ,mkApp phase t,hχV,P,mkApp M t,a (geo ++ `higher_jets) point]
                let pf := a `JanetCartan.PhysicalPairs.SampledMask.first_mask #[d,N,β,V,W,hV,hW,χ,ψ,hc,hχV,chart χ hχ,chart ψ hψ,Ksrc,
                  QT,A,B,sign,phase,ρ,M,u,← fn (baseRow `row_smooth),← fn (rowWave `left_smooth),← fn (rowWave `right_smooth),
                  ← fn (chart (mkApp phase t) (a (geo ++ `smooth) point)),← fn hM,← fn (a (ns ++ `one_of_two) #[(get `lam),part window 2]),
                  ← fn (part window 3),mkApp P (mkNatLit 0),P,X,Y,AQ,C,hp,hX,hY,hAQ,hC,← fn (baseRow `bump_jets),
                  ← fn (baseRow `source_jets),← fn (baseRow `row_jets),left,right,← fn hgrad,← fn (a (geo ++ `gradient_upper) point),
                  ← fn hj,← fn (rowWave `represented_realization)]
                let ty ← inferType pf
                let aa := ty.getAppArgs
                let target := a `JanetCartan.PhysicalInitialization.OriginalSampledObserved.FirstMaskInput
                  #[d,β,ρ,a (ns ++ `complexSource) zs,aa.back!]
                discard <| store (ns ++ `first_mask) inputs pf false (some target)
              else
                let hbudget := down (← mkAppM ``Classical.choose_spec #[low]) 1
                let bounds := mkAppN hbudget #[V,W,hV,hW,χ,ψ,mkApp QT t,mkApp A t,mkApp B t,chart χ hχ,chart ψ hψ,baseRow `row_smooth,
                  rowWave `left_smooth,rowWave `right_smooth,a (ns ++ `support_refl) #[d,χ],hχV,mkApp M t,hM,
                  baseRow `bump_jets,baseRow `source_jets,baseRow `row_jets,mkApp left t,mkApp right t,mkApp sign t,
                  mkApp phase t,mkApp ρ t,mkApp u t,rowWave `represented_realization]
                let res ← fn bounds
                let name := a (ns ++ `sourceNormCost) cData
                discard <| store (ns ++ `norms) inputs res false (some ((← inferType res).replace fun e => if e == price then some name else none))
publish_native_first_mask 0
publish_native_first_mask 1
publish_native_first_mask 2
publish_native_first_mask 3
publish_native_first_mask 4
publish_native_first_mask 5
publish_native_first_mask 6
end JanetCartan.PhysicalPairs.OriginalFirstMask
end
