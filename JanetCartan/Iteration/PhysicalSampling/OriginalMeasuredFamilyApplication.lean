module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBandBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedProfileBounds
public meta import Lean

/-!
# Family constants for the actual measured common event

Take the finite sums of the actual retained row constants, before any physical
history or frequency. The column bound is the exact numerical right-hand side
of `correctedColoredCrossBandData_uniform_bounds_of_profiles` with the retained
five profiles, Mκ=1 and MC=Cmeasure(0). It never compares against the arbitrary
qualitative compactness witness in the kernel record. The consumer is the
original physical scalar/measured event with amplitude bounds
(`app:ch_waves:eq:sampling-operator-bounds`, `app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.PhysicalSampling.OriginalMeasuredFamilyApplication

private def columnBudget (n N : ℕ) (C A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ) (MC : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) *
    (2 * MC * ((1 : ℝ) * (RawPrimary.AmplitudeGrades.Polynomial.derivativeProfile n N C A₀ A₁ B₀ B₁ 0 + Cresp 0)) ^ 2)

private theorem columnBudget_nonnegative (n N : ℕ) (C A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ)
    {MC : ℝ} (h : 0 ≤ MC) : 0 ≤ columnBudget n N C A₀ A₁ B₀ B₁ Cresp MC := by
  unfold columnBudget
  positivity

private def supportOf {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (κ : X × Y → ℝ) : Set X := Prod.fst '' tsupport κ

private theorem supportOf_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {κ : X × Y → ℝ} (h : HasCompactSupport κ) : IsCompact (supportOf κ) := h.image continuous_fst

end JanetCartan.PhysicalSampling.OriginalMeasuredFamilyApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredFamilyApplication
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalSampling.OriginalMeasuredFamily
private def mean := `JanetCartan.PhysicalSampling.OriginalMeasuredMean
private def band := `JanetCartan.PhysicalSampling.OriginalMeasuredBand

private def store (label : Name) (params : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let n := root ++ label
  let type ← match expected with
    | some t => pure t
    | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars params type)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "original measured family: incomplete actual data/proof {label}"
  if data then
    addDecl (.defnDecl {name := n, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name := n, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked original measured family {label} at {params.size} before-history inputs"
  return mkAppN (mkConst n) params

private def withFamily (k : Array Expr → Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let source := mean ++ `initialized
  forallBoundedTelescope (← getConstInfo source).type (some 32) fun fixed tail => do
    unless fixed.size == 32 do throwError "measured family: expected weights22 plus native10 on one source scale"
    forallBoundedTelescope tail (some 1) fun row _ => do
      let i := row[0]!
      let base := mkAppN (mkConst source) (fixed.push i)
      let profileType := (← whnf (← inferType base)).bindingDomain!
      withLocalDeclD `Ar (← mkForallFVars row profileType) fun Ar => do
        let first := mkApp base (mkApp Ar i)
        withLocalDeclD `hAr (← mkForallFVars row (← whnf (← inferType first)).bindingDomain!) fun hAr => do
          let next := mkApp first (mkApp hAr i)
          let responseType := (← whnf (← inferType next)).bindingDomain!
          withLocalDeclD `Cresp (← mkForallFVars row responseType) fun Cresp => do
            let next := mkApp next (mkApp Cresp i)
            withLocalDeclD `hCresp (← mkForallFVars row (← whnf (← inferType next)).bindingDomain!) fun hCresp => do
              k (fixed ++ #[Ar, hAr, Cresp, hCresp]) i
                (fixed ++ #[i, mkApp Ar i, mkApp hAr i, mkApp Cresp i, mkApp hCresp i])

/-- The family bound is an actual sum over the selected finite row index.
The source-scale profile constants can vary per row; no uniformity in the
source scale is needed. -/
elab "cache_original_measured_family_bound " which:num : command =>
    liftTermElabM <| withTransparency .reducible <| withFamily fun params i actual => do
  let isMean := which.getNat == 0
  unless isMean || which.getNat == 1 do throwError "measured family: invalid sum"
  let src := if isMean then mean else band
  let short : Name := if isMean then `Cmean else `Csharp
  let sign : Name := if isMean then `positive else `nonnegative
  let value := mkAppN (mkConst (src ++ short)) actual
  let values ← mkLambdaFVars #[i] value
  let univ ← mkAppOptM `Finset.univ #[some (← inferType i), none]
  let total ← store short params (← mkAppM `Finset.sum #[univ, values]) true
  let positive := mkAppN (mkConst (src ++ sign)) actual
  let nonnegative ← if isMean then mkAppM `le_of_lt #[positive] else pure positive
  let hi ← mkAppM `Finset.mem_univ #[i]
  let positiveAll ← withLocalDeclD `hi (← inferType hi) fun hx => mkLambdaFVars #[i, hx] nonnegative
  let signAll ← mkAppM `Finset.sum_nonneg #[positiveAll]
  let zero := (← inferType signAll).appFn!.appArg!
  discard <| store (if isMean then `hCmean else `hCsharp) params signAll false
    (some (← mkAppM ``LE.le #[zero, total]))
  discard <| store (if isMean then `Cmean_le else `Csharp_le) (params.push i)
    (← mkAppM `Finset.single_le_sum #[positiveAll, hi]) false (some (← mkAppM ``LE.le #[value, total]))

/-- Retain the actual compact support and the original Fourier-normalized,
whole-kernel amplitude constant at the same row and profile budget. -/
elab "cache_original_measured_family_kernel_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible <| withFamily fun params i actual => do
  let info ← getConstInfo (mean ++ `initialized)
  let some body := info.value? (allowOpaque := true) | throwError "measured family: original mean application missing"
  let applied := (body.beta actual).headBeta
  unless applied.isAppOfArity `JanetCartan.PhysicalSampling.OriginalChoices.Mean.continuation 62 do
    throwError "measured family: actual mean source geometry changed"
  let xs := applied.getAppArgs
  let geometry := params[:22].toArray.push i
  let S := mkAppN (mkConst (root ++ `support)) geometry
  let family := params.push i
  let Cmeasure := xs[60]!
  let n := Cmeasure.getAppArgs[0]!
  let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
  let mc := mkApp Cmeasure (mkNatLit 0)
  let columnArgs := #[n, N] ++ xs[16:22].toArray ++ #[mc]
  match which.getNat with
  | 0 => discard <| store `support geometry (← mkAppM ``supportOf #[xs[33]!]) true
  | 1 =>
    let compact := ← mkAppM ``supportOf_compact #[xs[35]!]
    discard <| store `compact_support geometry compact false (some (← mkAppM `IsCompact #[S]))
  | 2 => discard <| store `amplitudeBound family (mkAppN (mkConst ``columnBudget) columnArgs) true
  | 3 =>
    let result := mkAppN (mkConst ``columnBudget_nonnegative) (columnArgs.push (mkApp xs[61]! (mkNatLit 0)))
    let bound := mkAppN (mkConst (root ++ `amplitudeBound)) family
    let zero ← mkNumeral (mkConst ``Real) 0
    discard <| store `amplitudeBound_nonnegative family result false (some (← mkAppM ``LE.le #[zero, bound]))
  | _ => throwError "measured family: invalid kernel field"

end JanetCartan.PhysicalSampling.OriginalMeasuredFamilyApplication
