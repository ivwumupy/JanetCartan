module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseline
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMeasurement
public import JanetCartan.Iteration.PhysicalMean.OriginalMeasuredHermitianProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareOuter
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# The unscaled positive baseline on the original active measured carrier

This leaf discharges only `hbackground` in
`OriginalCanonicalRow.zero_safe_hraw_of_original_integral`. The actual inner
incidence/spectator factor is used only to enter the original carrier plateau.
The baseline is never multiplied by that factor and remains defined at zero.
The common observation, the original joint coefficient cutoff, and the retained
carrier extension are each removed using their own original plateau certificate.
The conclusion is equality of matrices, not merely of their Hermitian squares
(`app:ch_mean_pairs:defn:mean-canonical`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalActiveBaseline
open Sampling Sampling.MeasuredAmplitude ContinuumRow CanonicalConic CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase SeparatedSampling

private theorem active_carrier_support (z₀ : Euclidean 3) {a : ℝ} (ha : 0 < a)
    (z : Point)
    (hactive : incidenceMask z₀ ha (carrierSamplingEquiv.symm z).1 *
      spectatorMask z₀ ha (carrierSamplingEquiv.symm z).2 ≠ 0) :
    carrierSamplingEquiv.symm z ∈ carrierSupport z₀ (r := a) := by
  apply originalConicCarrierWeight_support z₀ ha
  exact pow_ne_zero 2 hactive

private theorem measured_point_in_carrier_cutoff {n : ℕ} {μ a : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hsep : 6 * μ < a)
    (Q : Euclidean n → Fin n → MetricTensor n)
    (x : Euclidean n) (hx : canonicalSamplingMeasurement Q hμ x ≠ 0) :
    x ∈ tsupport (FixedCutoffs.physical (n := n) ha (1 : Fin 3)) := by
  have hxμ := FixedCutoffs.physical_tsupport_four hμ 1
    (tsupport_canonicalSamplingMeasurement Q hμ (subset_tsupport _ hx))
  have hinner : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3).val + 1 : ℝ) * a) := by
    apply closedBall_subset_closedBall _ hxμ
    norm_num
    linarith
  have hone := interior_subset (FixedCutoffs.physical_plateau ha 1 hinner)
  exact subset_tsupport _ ((show FixedCutoffs.physical ha 1 x = 1 from hone).trans_ne one_ne_zero)

private theorem active_cut_background
    {d N : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (A : Euclidean (d + 1) × (Euclidean 3 × Euclidean (d + 1 - 1)) →
      Matrix (Fin N) (Fin (d + 1)) ℂ)
    (κ : Euclidean (d + 1) × (Euclidean 3 × Euclidean (d + 1 - 1)) → ℝ)
    (z₀ : Euclidean 3) {ρ a μ : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hμ : 0 < μ)
    (hsep : 6 * μ < a)
    (hgraph : ∀ p ∈ carrierSupport z₀ (r := a),
      (parameter p, T.reference.spatialPatch (parameter p)) ∈
        closedBall (z₀,T.reference.spatialPatch z₀) (ρ / 4))
    (hplateau : ∀ i : Fin 3, ∀ x ∈ tsupport (FixedCutoffs.physical (n := d + 1) ha i),
      ∀ p ∈ carrierSupport z₀ (r := a), ∀ shift : Euclidean (d + 1 - 1),
      ‖shift‖ ≤ ρ / 4 → κ (x,parameter p,T.reference.spatialPatch (parameter p) + shift) = 1)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (z : Point)
    (hactive : incidenceMask z₀ ha (carrierSamplingEquiv.symm z).1 *
      spectatorMask z₀ ha (carrierSamplingEquiv.symm z).2 ≠ 0)
    (x : Euclidean (d + 1)) (hx : canonicalSamplingMeasurement Q hμ x ≠ 0) :
    A (x,WithLp.toLp 2 z,T.reference.spatialPatch (WithLp.toLp 2 z)) =
      κ (x,WithLp.toLp 2 z,extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 z)) •
        A (x,WithLp.toLp 2 z,extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 z)) := by
  have hz := active_carrier_support z₀ ha z hactive
  have hcoord : parameter (carrierSamplingEquiv.symm z) = WithLp.toLp 2 z := by
    obtain ⟨p,rfl⟩ := carrierSamplingEquiv.surjective z
    rw [carrierSamplingEquiv.symm_apply_apply,parameter_apply]
    ext c
    fin_cases c <;> rfl
  have hpair := hgraph _ hz
  rw [← closedBall_prod_same,hcoord] at hpair
  have hcar : extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 z) =
      T.reference.spatialPatch (WithLp.toLp 2 z) :=
    extendedRetainedCarrier_eq T z₀ hρ
      (closedBall_subset_closedBall (by linarith : ρ / 4 ≤ ρ) hpair.1)
  have hκ := hplateau 1 x (measured_point_in_carrier_cutoff hμ ha hsep Q x hx)
    _ hz 0 (by simp only [norm_zero]; positivity)
  simp only [hcoord,add_zero] at hκ
  rw [hcar,hκ,one_smul]

private theorem nonzero_right {E : Type*} [Zero E] {a b : E}
    (h : a = b) (ha : a ≠ 0) : b ≠ 0 := h ▸ ha

private theorem observation_baseline_eq_cut {n N : ℕ}
    (base native cut : Matrix (Fin N) (Fin n) ℂ) (ψ : ℝ)
    (hbase : base = ψ • native) (hψ : ψ = 1) (hcut : native = cut) :
    base = cut := by
  rw [hbase,hψ,one_smul,hcut]

end JanetCartan.PhysicalMean.OriginalCanonicalActiveBaseline
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalActiveBaseline
open Lean Meta Elab Command OriginalBackgroundHermitianTemplate

private def ns := `JanetCartan.PhysicalMean.OriginalCanonicalActiveBaseline
private def bg := `JanetCartan.PhysicalMean.OriginalCanonicalBaseline
private def meas := `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
private def mp := `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (tail h j)

private def telescope (type : Expr) (count : Nat)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := go count type #[]
where
  go : Nat → Expr → Array Expr → MetaM Unit
    | 0, result, xs => next xs result
    | remaining + 1, type, xs => do
      let .forallE name domain body bi := type.consumeMData
        | throwError "actual active baseline: telescope ended at {xs.size}"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        go remaining (body.instantiate1 x) (xs.push x)

private def store (params : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual active baseline: missing producer constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual active baseline: open or assumed matrix identity"
  let name := ns ++ `positiveBaseline_eq_cutAmplitude
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME unscaled positive baseline equals the actual Row64 background matrix on its active carrier and nonzero common measurement; the original observation, joint κ cutoff, and retained carrier extension are each removed using their own native plateau (app:ch_mean_pairs:defn:mean-canonical)."
  logInfo m!"checked actual active positive baseline matrix identity/{params.size}; no baseline scaling, sample weights, or background-success premise"

elab "construct_original_active_baseline" : command => liftTermElabM do
  withActualRow fun d => do
    let baseHead := app (bg ++ `positiveBaseline) d.parameters
    telescope (← inferType baseHead) 3 fun extra _ => do
      unless extra.size == 3 do throwError "actual active baseline: missing color/node/outer support"
      let color := extra[0]!
      let node := extra[1]!
      let params := d.parameters ++ extra
      unless params.size == 54 do throwError "actual active baseline: changed baseline54"
      let factor := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.factor
        (d.native64[:22].toArray ++ #[d.row,node])
      let activeType ← mkAppM ``Ne #[factor,← mkNumeral (mkConst ``Real) 0]
      withLocalDeclNoLocalInstanceUpdate `hActive .default activeType fun hActive => do
        let n := d.raw13[0]!
        let N := d.raw13[1]!
        withLocalDeclNoLocalInstanceUpdate `z .default (mkApp (mkConst `JanetCartan.Torus) n) fun z => do
          let Cper := app (meas ++ `Cper) d.parameters[:50].toArray
          let Cz := mkApp Cper z
          let nonzero ← mkAppM ``Ne #[Cz,← mkNumeral (← inferType Cz) 0]
          withLocalDeclNoLocalInstanceUpdate `hCper .default nonzero fun hCper => do
            let x := app `JanetCartan.AmplitudeBound.centeredTorusRepresentative #[n,z]
            let hCnative := app (meas ++ `Cper_native) (d.parameters[:50].toArray.push z)
            let hC ← mkAppM ``nonzero_right #[hCnative,hCper]
            let hobs := app (meas ++ `observation_eq_one) (d.parameters[:50].toArray ++ #[x,hC])
            let hbase := app (bg ++ `positiveBaseline_native) (params.push z)
            let raw ← bodyAt `JanetCartan.PhysicalSampling.OriginalMeasuredFamily.Row.kernel d.native64
            unless raw.isAppOfArity `JanetCartan.CanonicalRowComparison.correctedColoredCrossBandData 45 do
              throwError "actual active baseline: native Row64 is not the original corrected data45"
            let r := raw.getAppArgs
            let physical := d.mean70[37]!
            unless physical.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do
              throwError "actual active baseline: changed physical measurement"
            let c := physical.getAppArgs
            unless c[3]!.isAppOfArity `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure 21 do
              throwError "actual active baseline: changed common measurement radius"
            let selected := c[3]!.getAppArgs
            let ha := app `JanetCartan.PhysicalSeed.SelectedBoundary.ha' (selected.push d.row)
            let hsep := app `JanetCartan.PhysicalSeed.SelectedBoundary.fact60 (selected.push d.row)
            let a := (← inferType ha).getAppArgs[3]!
            let admission := app `JanetCartan.PhysicalSampling.OriginalAdmission.cutoff_on_actual_selected_row
              (d.native64[:22].toArray.push d.row)
            let A := mkApp (nativeAmplitude d) (mkApp d.native64[61]! color)
            let cutProof := app ``active_cut_background
              (r[:6].toArray ++ #[A,r[15]!,r[34]!,r[35]!,a,c[2]!,r[36]!,ha,c[3]!,hsep,
                part admission 3,part admission 4,c[1]!,node,hActive,x,hC])
            let baseType ← inferType hbase
            let cutType ← inferType cutProof
            unless baseType.isAppOfArity ``Eq 3 && cutType.isAppOfArity ``Eq 3 do
              throwError "actual active baseline: changed literal matrix equality"
            let b := baseType.getAppArgs
            let k := cutType.getAppArgs
            let observed := b[2]!.getAppArgs
            let proof := app ``observation_baseline_eq_cut
              #[n,N,b[1]!,k[1]!,k[2]!,observed[observed.size-2]!,hbase,hobs,cutProof]
            let coord ← nodeAt node
            let extended ← mkAppM `JanetCartan.Sampling.MeasuredAmplitude.extendedRetainedCarrier
              #[r[5]!,r[34]!,r[36]!,coord]
            let w ← mkAppM ``Prod.mk #[x,← mkAppM ``Prod.mk #[coord,extended]]
            let named := mkApp (app (mp ++ `cutAmplitude) (d.parameters.push color)) w
            let target ← mkEq b[1]! named
            store (params ++ #[hActive,z,hCper]) proof target

end JanetCartan.PhysicalMean.OriginalCanonicalActiveBaseline
end

construct_original_active_baseline
