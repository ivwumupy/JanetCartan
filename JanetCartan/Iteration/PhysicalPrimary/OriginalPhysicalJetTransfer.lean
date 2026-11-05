module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalObservation
public import JanetCartan.Iteration.PhysicalPrimary.OriginalReducedReserve
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalPhaseTemplate

/-! # Same actual ordered observation across the plateau comparison
The Fourier theorem acts on the full original doubled window. On the physical
comparison window its source and solver are the same. Only the totalization of
the phase mentions a different set; both agree on an *open neighborhood* of
each compared parameter. Thus their actual parameter jets are identical. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalJetTransfer
open FixedDomainInverse FixedDomainInverse.ObservedParameterRemainders ResponseTransfer.Complement Pseudodifferential

theorem congr_carrier {n q : ℕ} (ρ : ℝ) (φ ψ : Euclidean n → ℝ) (hp : Continuous φ)
    (hq : Continuous ψ) (he : φ = ψ) :
    carrierMultiplication (r := q) ρ φ hp = carrierMultiplication ρ ψ hq := by subst ψ; rfl

/-- Equality is needed on an open cell, not merely at the center, when
transferring ordered derivatives of the two continuous L² curves. -/
theorem original_window_jets {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {V : Set P} (hV : IsOpen V)
    (f g : P → E) (he : ∀ c ∈ V, f c = g c) :
    ∀ c ∈ V, ∀ k, iteratedFDeriv ℝ k f c = iteratedFDeriv ℝ k g c := by
  intro c hc k
  have h : f =ᶠ[𝓝 c] g := by
    filter_upwards [hV.mem_nhds hc] with b hb using he b hb
  exact (h.iteratedFDeriv ℝ k).self_of_nhds

/-- Use the scalar L² representatives of the actual physical solver to
transport the unchanged vector Fourier membership and bound, without choosing
a different solution or differentiating an arbitrary a.e. representative. -/
theorem graded_matrix_of_native_vector {n k : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {V : Set P} {f : Euclidean n × P → EuclideanSpace ℂ (Fin n)}
    {u v : P → Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n))}
    {c : P} (hc : c ∈ V) (w : Fin k → P) (s : ℕ) {D : ℝ}
    (he : iteratedFDeriv ℝ k u c = iteratedFDeriv ℝ k v c)
    (hclass : ∀ c ∈ V, ∀ k (w : Fin k → P),
      ∃ ug : PiLp 2 (fun _ : Fin n ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
        (∀ i, ug i =ᵐ[volume] fun x ↦ (iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) i) ∧
        ug = finiteL2CoordinateIsometry volume (iteratedFDeriv ℝ k u c w) ∧
        (∀ s : ℝ, MemMatrixFourierSobolev s ug ↔ MemVectorFourierSobolev s (iteratedFDeriv ℝ k u c w)) ∧
        (∀ s : ℝ, matrixFourierSobolevNorm s ug = vectorFourierSobolevNorm s (iteratedFDeriv ℝ k u c w)))
    (hv : MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k v c w) ∧
      vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k v c w) ≤ D) :
    ∃ ug : PiLp 2 (fun _ : Fin n ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
      (∀ i, ug i =ᵐ[volume] fun x ↦ (iteratedFDeriv ℝ k (fun b ↦ f (x,b)) c w) i) ∧
      MemMatrixFourierSobolev (s : ℝ) ug ∧ matrixFourierSobolevNorm (s : ℝ) ug ≤ D := by
  obtain ⟨ug,hug,_,hm,hn⟩ := hclass c hc k w
  rw [← he] at hv
  exact ⟨ug,hug,(hm s).2 hv.1,(hn s).trans_le hv.2⟩

end JanetCartan.PhysicalPrimary.OriginalPhysicalJetTransfer
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalJetTransferTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalPhysicalPhaseTemplate OriginalLocalWaveGeometryTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalJetTransfer
private def phy := `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def obs := `JanetCartan.FixedDomainInverse.ObservedParameterRemainders
private def family := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def cmp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def appl (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  addDocStringCore (ns ++ k) "The classical reduced parameter jets of the actual physical source are those of the same original observed complete inverse on its unshrunk doubled window (app:ch_response:eq:response-graded-reduced)."
  return h

elab "identify_original_full_observed_jets" : command => liftTermElabM do
  withPhysicalPhaseInputs fun xs base s _ => do
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let member := appl (ind ++ `point) xs
    let par := base.push member
    let hSm := appl (phy ++ `observation_smooth) xs
    let sa := (← inferType hSm).getAppArgs
    let u := sa[sa.size-2]!
    let U ← emit `comparison_solution xs u true
    let big := appl (family ++ `Static.V) base[:41].toArray
    let V := sa.back!
    let args := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let spec := appl (cmp ++ `parameterComparisonWindow_spec) #[n,s[1]!,args[23]!,args[24]!]
    let vb := Expr.proj ``And 0 (.proj ``And 1 spec)
    let φ := appl (ind ++ `phase) xs
    let rawBig ← withLocalDeclD `c (← inferType φ).bindingDomain! fun c => do
      let left := u.beta #[c]
      unless left.isAppOf `DFunLike.coe do throwError "full solution: comparison observation is not a carrier action"
      let car := left.getAppArgs[left.getAppArgs.size-2]!
      unless car.isAppOf `JanetCartan.ResponseTransfer.Complement.carrierMultiplication do
        throwError "full solution: original demodulating carrier missing"
      let a := car.getAppArgs
      let phase ← mkAppM (obs ++ `totalizedObservationPhase) #[big,φ,c]
      let hp ← mkAppM (obs ++ `continuous_totalizedObservationPhase) #[appl (family ++ `Point.hφ) par,c]
      let newCar := mkAppN car.getAppFn ((a.set! (a.size-2) phase).set! (a.size-1) hp)
      mkLambdaFVars #[c] (left.replace fun e => if e == car then some newCar else none)
    let native ← emit `full_solution xs rawBig true
    let e ← withLocalDeclD `c (← inferType φ).bindingDomain! fun c => do
      withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc => do
        let left := u.beta #[c]
        let right := rawBig.beta #[c]
        unless left.isAppOf `DFunLike.coe && right.isAppOf `DFunLike.coe do
          throwError "full solution: unexpected topology in {left.getAppFn} / {right.getAppFn}"
        let a := left.getAppArgs[left.getAppArgs.size-2]!.getAppArgs
        let b := right.getAppArgs[right.getAppArgs.size-2]!.getAppArgs
        let phaseEq ← mkAppM ``Eq.trans #[← mkAppM `JanetCartan.FixedDomainInverse.ObservedParameterRemainders.totalizedObservationPhase_of_mem #[φ,hc],
          ← mkAppM ``Eq.symm #[← mkAppM `JanetCartan.FixedDomainInverse.ObservedParameterRemainders.totalizedObservationPhase_of_mem #[φ,mkAppN vb #[c,hc]]]]
        let comp := appl (ns ++ `congr_carrier) #[n,n,a[a.size-3]!,a[a.size-2]!,b[b.size-2]!,a.back!,b.back!,phaseEq]
        let eq ← mkAppM ``DFunLike.congr_fun #[comp,left.appArg!]
        let eq ← emit `window_value (xs++#[c,hc]) eq false (some (← mkEq (mkApp U c) (mkApp native c)))
        mkLambdaFVars #[c,hc] eq
    let eq ← mkAppM (ns ++ `original_window_jets) #[Expr.proj ``And 0 spec,U,native,e]
    discard <| emit `ordered_solution_jets xs eq
    unless big.isApp do throwError "lost original large parameter window"
  logInfo "physical classical classes compared at all ordered parameter jets to the same unshrunk native complete observed solution, at the exact reciprocal rate"

end JanetCartan.PhysicalPrimary.OriginalPhysicalJetTransferTemplate
end

set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
identify_original_full_observed_jets
