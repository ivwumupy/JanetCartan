module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceLinear
public import JanetCartan.Iteration.PhysicalMean.CanonicalCoreResidual
public import JanetCartan.Iteration.PhysicalBackground.NativePositiveCancellation
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# Physical residual on the same original projected core

Consumer: `new:eq:qT-identity` and `new:lem:mean-exact`. The actual native39
base variation, SAME sampled E/Q and global inverse are retained. Only the
projected cancellation is used; no unmeasured tensor cancellation is asserted.
The deterministic open buffer below exists solely to apply the established
local strain theorem around the original closed core, without shrinking it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalCoreResidual
open ContinuumRow AmplitudeBound ProjectedStressFrame

private def projectedCoreBuffer {n : ℕ} (μ : ℝ) (ψ : C(Torus n, ℝ)) :
    Set (Euclidean n) :=
  ball 0 (2 * μ) ∩ torusQuotient ⁻¹' interior {z | ψ z = 1}

private theorem projectedCoreBuffer_open {n : ℕ} (μ : ℝ) (ψ : C(Torus n, ℝ)) :
    IsOpen (projectedCoreBuffer μ ψ) := by
  have hq : Continuous (@torusQuotient n) := by
    have h : IsOpenQuotientMap (@torusQuotient n) :=
      (IsOpenQuotientMap.piMap (fun _ : Fin n ↦
        QuotientAddGroup.isOpenQuotientMap_mk)).comp
          (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
    exact h.continuous
  exact isOpen_ball.inter (isOpen_interior.preimage hq)

private theorem original_core_mem_buffer {n : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (ψ : C(Torus n, ℝ)) {x : Euclidean n} (hx : x ∈ closedBall 0 μ)
    (hψ : torusQuotient x ∈ interior {z | ψ z = 1}) :
    x ∈ projectedCoreBuffer μ ψ :=
  ⟨closedBall_subset_ball (by linarith only [hμ]) hx, hψ⟩

private theorem core_buffer_sub_four {n : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (ψ : C(Torus n, ℝ)) : projectedCoreBuffer μ ψ ⊆ ball 0 (4 * μ) := by
  intro x hx
  exact ball_subset_ball (by linarith only [hμ]) hx.1

private theorem four_ball_sub_five {n : ℕ} {μ : ℝ} (hμ : 0 < μ) :
    ball (0 : Euclidean n) (4 * μ) ⊆ ball 0 (5 * μ) :=
  ball_subset_ball (by linarith only [hμ])

private theorem fixed_measurement_one_on_double {n : ℕ} {μ : ℝ} (hμ : 0 < μ)
    {x : Euclidean n} (hx : x ∈ closedBall 0 (2 * μ)) :
    FixedCutoffs.physical hμ 1 x = 1 := by
  have hp := FixedCutoffs.physical_plateau (n := n) hμ 1
  have hx' : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * μ) := by
    convert hx using 1
    norm_num
  exact (show x ∈ {y | FixedCutoffs.physical hμ 1 y = 1} from interior_subset (hp hx'))

private theorem fixed_periodic_measurement_one_on_double {n : ℕ} {μ : ℝ}
    (hμ : 0 < μ) (hcell : 4 * μ < 1 / 2) {x : Euclidean n}
    (hx : x ∈ closedBall 0 (2 * μ)) :
    FixedCutoffs.periodic hμ hcell 1 (torusQuotient x) = 1 := by
  have hx4 : x ∈ closedBall (0 : Euclidean n) (4 * μ) :=
    closedBall_subset_closedBall (by linarith only [hμ]) hx
  rw [FixedCutoffs.periodic_apply,
    PeriodicLocalL2.centeredTorusRepresentative_quotient
      (FixedCutoffs.closedBall_four_subset_cell hcell hx4)]
  exact fixed_measurement_one_on_double hμ hx

private theorem projected_measurement_on_double {n N : ℕ} {μ : ℝ}
    (hμ : 0 < μ) (hcell : 4 * μ < 1 / 2)
    (F : Euclidean n → Euclidean N) {x : Euclidean n}
    (hx : x ∈ closedBall 0 (2 * μ)) (H : MetricTensor n) (i : Fin n) :
    OriginalCanonicalMeasurement.nativeMeasurement
      (Sampling.canonicalSamplingMeasurement (projectedStress F) hμ)
      (torusQuotient x) H i = tensorPairing (projectedStress F x i) H := by
  have hx4 : x ∈ closedBall (0 : Euclidean n) (4 * μ) :=
    closedBall_subset_closedBall (by linarith only [hμ]) hx
  rw [OriginalCanonicalMeasurement.nativeMeasurement_apply,
    PeriodicLocalL2.centeredTorusRepresentative_quotient
      (FixedCutoffs.closedBall_four_subset_cell hcell hx4),
    Sampling.canonicalSamplingMeasurement_apply, fixed_measurement_one_on_double hμ hx, one_mul]

private theorem coefficients_on_double {n N : ℕ} {μ : ℝ}
    (hμ : 0 < μ) (hcell : 4 * μ < 1 / 2)
    (cut : Euclidean n → ℝ) (F : Euclidean n → Euclidean N)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j z, c j z = cut (centeredTorusRepresentative z) *
      GeometricProfile.geometricReducedCoefficients F (centeredTorusRepresentative z) j)
    (hcut : closedBall 0 (4 * μ) ⊆ interior {x | cut x = 1}) :
    ∀ x ∈ closedBall 0 (2 * μ), ∀ j,
      c j (torusQuotient x) = GeometricProfile.geometricReducedCoefficients F x j := by
  intro x hx j
  have hx4 : x ∈ closedBall (0 : Euclidean n) (4 * μ) :=
    closedBall_subset_closedBall (by linarith only [hμ]) hx
  have hrep := PeriodicLocalL2.centeredTorusRepresentative_quotient
    (FixedCutoffs.closedBall_four_subset_cell hcell hx4)
  have hone : cut x = 1 := (show x ∈ {y | cut y = 1} from interior_subset (hcut hx4))
  rw [hc, hrep, hone, one_mul]

end JanetCartan.PhysicalMean.OriginalCanonicalCoreResidual
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalCoreResidual
open Lean Meta Elab Command
open JanetCartan.PhysicalMean.OriginalBackgroundHermitianTemplate

private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args

private def localTerm (bindings : List (Name × Expr)) (code : String)
    (target : Option Expr := none) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code target)

private def save (name : Name) (params : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  let env ← getEnv
  for term in #[type,value] do
    let missing := term.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual core residual: missing producers {missing.toList}"
    if term.hasFVar || term.hasMVar || term.hasLevelMVar || term.hasLooseBVars || term.hasSorry then
      throwError "actual core residual: unresolved or extra input"
  let fullName := `JanetCartan.PhysicalMean.OriginalCanonicalCoreResidual ++ name
  addDecl (.thmDecl { name := fullName, levelParams := [], type, value }) (forceExpose := true)
  addDocStringCore fullName "SAME original native39 initial raw, physical base variation and global inverse; SAME sampled E52/Q52 on the original fixed closed core. The forcing and source are DATA. The displayed initial term is retained until projected positive cancellation and the complete-forcing identity are applied (new:eq:qT-identity)."

elab "construct_original_initialized_core_residual" : command => liftTermElabM do
  JanetCartan.PhysicalMean.OriginalCanonicalSourceApplication.withActualQuadratic fun p _ native _ rawQ => do
    let rawE ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear p
    unless rawE.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
      throwError "actual core residual: same linear28 changed"
    let e := rawE.getAppArgs
    let cancellation ← bodyAt
      `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.on_exterior_plateau native
    unless cancellation.isAppOfArity
        `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
      throwError "actual core residual: native projected cancellation64 changed"
    let c := cancellation.getAppArgs
    let n := c[0]!
    let N := c[1]!
    let mu := c[21]!
    let hr := c[22]!
    let hcell := c[23]!
    let F := c[34]!
    let psi := e[15]!
    let initial := app `JanetCartan.PhysicalBackground.NativeAdmission.raw native
    let core := app ``projectedCoreBuffer #[n,mu,psi]
    let hcore := app ``projectedCoreBuffer_open #[n,mu,psi]
    let hsub := app ``core_buffer_sub_four #[n,mu,hr,psi]
    let W ← localTerm [(`n,n),(`mu,mu)] "Metric.ball (0 : JanetCartan.Euclidean n) (4*mu)"
    let hW ← localTerm [(`W,W)] "(Metric.isOpen_ball : IsOpen W)"
    let h45 := app ``four_ball_sub_five #[n,mu,hr]
    let hF ← localTerm [(`hF,c[35]!),(`hsub,h45)] "hF.mono hsub"
    let himm ← localTerm [(`himm,c[36]!),(`hsub,h45)] "fun x hx ↦ himm x (hsub hx)"
    let hrank ← localTerm [(`hrank,c[37]!),(`hsub,h45)] "fun x hx ↦ hrank x (hsub hx)"
    unless c[51]!.isAppOfArity
        `JanetCartan.PhysicalBackground.native_measured_coefficients_core 10 do
      throwError "actual core residual: exact coefficient formula lost"
    let hdouble := app ``coefficients_on_double c[51]!.getAppArgs
    let hcoeff ← localTerm [(`K,core),(`h,hdouble)]
      "fun x (hx : x ∈ K) j ↦ h x (Metric.ball_subset_closedBall hx.1) j"
    let hperiodic := app ``fixed_periodic_measurement_one_on_double #[n,mu,hr,hcell]
    let hmeas ← localTerm [(`K,core),(`h,hperiodic)]
      "fun x (hx : x ∈ K) ↦ h (Metric.ball_subset_closedBall hx.1)"
    let hext ← localTerm [(`K,core),(`psi,psi)]
      "fun x (hx : x ∈ K) ↦ by\n  have hone := interior_subset hx.2\n  exact (show psi (JanetCartan.torusQuotient x) = 1 from hone)"
    let hprojected := app ``projected_measurement_on_double #[n,N,mu,hr,hcell,F]
    let hCeq ← localTerm [(`K,core),(`h,hprojected)]
      "fun x (hx : x ∈ K) H i ↦ h (Metric.ball_subset_closedBall hx.1) H i"
    let fixedCore := app `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.core native[:21].toArray
    let hooks := app `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.core_plateau native[:21].toArray
    let .forallE _ Y _ _ := (← inferType e[21]!).consumeMData
      | throwError "actual core residual: original source-regularity domain missing"
    withLocalDeclNoLocalInstanceUpdate `forcing .default Y fun g => do
      withLocalDeclNoLocalInstanceUpdate `source .default Y fun r => do
        withLocalDeclNoLocalInstanceUpdate `x .default (app `JanetCartan.Euclidean #[n]) fun x => do
          let hxType ← localTerm [(`K,fixedCore),(`x,x)] "x ∈ K"
          withLocalDeclNoLocalInstanceUpdate `hx .default hxType fun hx => do
            withLocalDeclNoLocalInstanceUpdate `component .default (app ``Fin #[n]) fun component => do
              let hook := mkAppN hooks #[x,hx]
              let hxBuffer := app ``original_core_mem_buffer
                #[n,mu,hr,psi,x,Expr.proj ``And 0 hook,Expr.proj ``And 1 hook]
              let common := #[e[0]!,N,e[1]!,e[2]!,e[4]!,e[5]!,e[7]!,e[8]!,e[9]!,e[10]!] ++
                e[11:].toArray
              let args := common ++ #[initial,c[60]!,F,c[57]!,W,core,hW,hcore,hsub,hF,c[58]!,
                himm,hrank,hcoeff,hmeas,hext,hCeq,g,r,x,hxBuffer,component]
              let producer := `JanetCartan.PhysicalMean.fixedSourceResidual_eq_initializedCoreDefect
              let info ← getConstInfo producer
              let proof := mkAppN (mkConst producer (info.levelParams.map (fun _ => .zero))) args
              let target ← Core.betaReduce (← zetaReduce (← inferType proof))
              let target := target.replace fun ex =>
                if ex == rawE then some (app `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear p)
                else if ex == rawQ then some (app `JanetCartan.PhysicalMean.OriginalCanonicalSource.quadratic p)
                else none
              let params := p ++ #[g,r,x,hx,component]
              unless params.size == 57 do throwError "actual initialized core residual changed native57"
              save `residual_eq_initialized_core_defect params proof target
              logInfo "actual initialized physical residual57: native39 initial and same sampled E/Q, original closed core; no unmeasured tensor cancellation"

end JanetCartan.PhysicalMean.OriginalCanonicalCoreResidual
end

construct_original_initialized_core_residual
