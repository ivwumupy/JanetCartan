module
public import JanetCartan.Iteration.PhysicalPairs.OriginalPacketEquation
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SmoothRealization

/-! # Pointwise tested PDE of the actual ambient signed packet on the inner core

Only the inner-core test is needed: the global smooth-right representative
may differ outside that core from the extension of the input plus the angular
discrepancy. Use the global smooth-right class for the smooth representative
and the local a.e. formula only under the ORIGINAL test support. No extra
plateau or alternate signed correction is used. `app:ch_regular:eq:exact-physical`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalPacketPDE
open CharacteristicTransport.CompleteResidual RegularSector.FiniteAssembly
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "RH" => Lp E 2 (volume : Measure E)
local notation "CV" => EuclideanSpace ℂ (Fin (d+1))

theorem from_global_and_core_tests (V : Set E) (hV : IsOpen V)
    (Q : E → Fin (d+1) → MetricTensor (d+1)) (B : E → MetricTensor (d+1)) (hQ : ContDiff ℝ ∞ Q) (hB : ContDiff ℝ ∞ B)
    (v r : E → E) (hv : ContDiff ℝ ∞ v) (hr : ContDiff ℝ ∞ r) (u w h a z : RH)
    (he : v =ᵐ[volume] u) (hre : r =ᵐ[volume] w)
    (hcore : r =ᵐ[volume.restrict V] (h : E → E) + (a : E → E) - (z : E → E))
    (tested : ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ j,
      physicalTestAction (fun y k ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single k 1)) B
        (fun y ↦ (l2ComplexInclusion volume u y).ofLp) φ j = ∫ y, φ y • l2ComplexInclusion volume (h+a-z) y j) :
    EqOn (physicalWeakApply (fun y k ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single k 1)) B
      (fun y ↦ (euclideanComplexInclusion (v y)).ofLp) (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (v y)).ofLp)))
      (fun y ↦ (euclideanComplexInclusion (r y)).ofLp) V := by
  let I : E →L[ℝ] CV := euclideanComplexInclusion
  have lift (f : E → E) (b : RH) (hb : f =ᵐ[volume] b) :
      (fun y ↦ I (f y)) =ᵐ[volume] l2ComplexInclusion volume b := by
    filter_upwards [hb,I.coeFn_compLpL b] with y hf hy
    exact (congrArg I hf).trans hy.symm
  have same : (fun y ↦ l2ComplexInclusion volume (h+a-z) y) =ᵐ[volume.restrict V]
      (fun y ↦ l2ComplexInclusion volume w y) := by
    filter_upwards [ae_restrict_of_ae (I.coeFn_compLpL (h+a-z)),ae_restrict_of_ae (I.coeFn_compLpL w),
      ae_restrict_of_ae (Lp.coeFn_sub (h+a) z),ae_restrict_of_ae (Lp.coeFn_add h a),hcore,ae_restrict_of_ae hre] with y h₁ h₂ h₃ h₄ h₅ h₆
    change (h+a-z) y = (h+a) y - z y at h₃
    change (h+a) y = h y + a y at h₄
    change r y = h y + a y - z y at h₅
    exact h₁.trans ((congrArg I (h₃.trans ((congrArg (· - z y) h₄).trans (h₅.symm.trans h₆)))).trans h₂.symm)
  apply smooth_representatives_physical_equation isOpen_univ hV (subset_univ _) Q B hQ.contDiffOn hB.contDiffOn
    (fun y ↦ I (v y)) (fun y ↦ I (r y)) (I.contDiff.comp hv) (I.contDiff.comp hr) _ _ (lift v u he) (lift r w hre)
  intro φ hφ hc hφV j
  rw [tested φ hφ hc hφV j]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hV.measurableSet).mp same] with y hy
  by_cases hmem : y ∈ V
  · rw [hy hmem]
  · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hmem (hφV hh)),zero_smul,zero_smul]
end JanetCartan.PhysicalPairs.OriginalPacketPDE
end
public meta section
set_option maxHeartbeats 950000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalPacketPDE
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalPacketPDE
private def sd := `JanetCartan.PhysicalPairs.OriginalSignedData
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def cur := `JanetCartan.PhysicalInitialization.OriginalRegular.Current
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def lp (e : Expr) : MetaM Expr := do
  unless e.isAppOfArity `MeasureTheory.AEEqFun.cast 6 && e.appArg!.isAppOfArity ``Subtype.val 3 do throwError "right side lost its explicit original Lp class: {e.getAppFn}"
  return e.appArg!.appArg!
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo (sd ++ `measured)).type (some 50) fun p _ => do
    let pt := p[:49].toArray
    let hi := a (hist ++ `measured_history) pt
    let now := pt[:36].toArray ++ #[pt[37]!,Expr.proj ``And 0 hi] ++ pt[39:43].toArray
    let current := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected).value! (allowOpaque := true)).beta now
    unless current.isAppOfArity (cur ++ `projected) 38 do throwError "packet equation received a different native inverse"
    let weak := current.getAppArgs
    let unc := a (sd ++ `uncut) p
    let smooth := mkApp (a (cur ++ `fact20) weak) unc
    let right := mkApp (a (cur ++ `fact21) weak) unc
    let core := mkApp (a (cur ++ `fact22) weak) unc
    let s := Expr.proj ``And 0 smooth
    let r := Expr.proj ``And 0 right
    let sae := Expr.proj ``And 1 smooth
    let rae := Expr.proj ``And 1 right
    let rt := (← inferType core).getAppArgs
    let V := rt[2]!.appArg!.appArg!
    let opn ← mkFreshExprMVar (← mkAppM ``IsOpen #[V])
    let rest ← opn.mvarId!.apply (← mkConstWithFreshMVarLevels ``Metric.isOpen_ball)
    unless rest.isEmpty do throwError "native test did not target the original open core"
    let ab := rt.back!.getAppArgs
    let plus := ab[ab.size-2]!.getAppArgs
    let tested := mkApp (a (cur ++ `fact19) weak) (← mkAppM ``Subtype.val #[unc])
    let v := (← inferType s).appArg!
    let pf := a (ns ++ `from_global_and_core_tests) #[p[0]!,V,← instantiateMVars opn,a (cur ++ `Q) weak,a (cur ++ `B) weak,a (cur ++ `hQ) weak,a (cur ++ `hB) weak,
      v,(← inferType r).appArg!,s,r,← lp (← inferType sae).appArg!,← lp (← inferType rae).appArg!,← lp plus[plus.size-2]!,← lp plus.back!,← lp ab.back!,sae,rae,core,tested]
    let actual := a `JanetCartan.PhysicalPairs.OriginalSignedPackets.solved p
    discard <| store (ns ++ `core_equation) p pf false (some ((← inferType pf).replace fun e => if e == v then some actual else none))
end JanetCartan.PhysicalPairs.OriginalPacketPDE
end
