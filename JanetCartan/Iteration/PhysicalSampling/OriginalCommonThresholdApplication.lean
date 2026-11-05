module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamily
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarFamily
public import JanetCartan.Iteration.PhysicalSampling.OriginalScalarCutoffs
public import JanetCartan.Iteration.PhysicalSampling.OriginalWindow
public import JanetCartan.Iteration.PhysicalSampling.UniformOriginalEvent
public meta import Lean

/-!
# One physical threshold for both original finite families

Apply the already proved amplitude version of the common-event theorem to
all actual prehistory numerical data. Scalar and measured use their own
fixed supported kernels and take the maximum only of the numerical sharp and
mean sums. The cutoff/window, original inner masses and unscaled Fourier
factor are unchanged. The output is still a continuation in the actual
current kernels, not a chosen successful shift (`app:ch_waves:thm:sampling`,
`new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
namespace JanetCartan.PhysicalSampling.OriginalCommonThresholdApplication

private theorem one_of_five {n : ℕ} (h : 5 ≤ n) : 1 ≤ n := by omega
private theorem scalar_support_compact {n : ℕ} {χ : Euclidean n → ℝ} (h : HasCompactSupport χ) :
    IsCompact (tsupport χ) := h
private theorem mask_nonnegative : (0 : ℝ) ≤ 1 := zero_le_one
private theorem fourier_nonnegative (n : ℕ) : (0 : ℝ) ≤ (2 * Real.pi) ^ (-(n : ℝ) / 2) := by positivity

end JanetCartan.PhysicalSampling.OriginalCommonThresholdApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalCommonThresholdApplication
open Lean Meta Elab Command

private def base := `JanetCartan.PhysicalSampling
private def target := base ++ `OriginalCommonThreshold
private def measured := base ++ `OriginalMeasuredFamily
private def scalar := base ++ `OriginalScalarFamily

private def store (name : Name) (xs : Array Expr) (term : Expr) (data := false)
    (result : Option Expr := none) : MetaM Expr := do
  let name := target ++ name
  let type ← match result with
    | some t => pure t
    | none => inferType term
  let type ← instantiateMVars (← mkForallFVars xs type)
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar ||
      type.hasFVar || value.hasFVar || type.hasSorry || value.hasSorry then
    throwError "original common threshold: incomplete {name}"
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked original common-event prehistory field {name} at {xs.size} fixed inputs"
  return mkAppN (mkConst name) xs

private def withActualBudgets (graph : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  let source := mkConst (measured ++ `Csharp)
  let w := graph[:22].toArray
  let start := w.push graph[27]!
  forallBoundedTelescope (← inferType (mkAppN source start)) (some 2) fun caps _ => do
    let start := start ++ caps ++ graph[29:33].toArray
    forallBoundedTelescope (← inferType (mkAppN source start)) (some 1) fun canonical _ => do
      let start := start ++ canonical ++ #[graph[35]!]
      forallBoundedTelescope (← inferType (mkAppN source start)) (some 1) fun leading _ => do
        let fixed := start ++ leading
        let scalarPrefix := graph[:26].toArray ++ graph[27:36].toArray
        forallBoundedTelescope (← inferType (mkAppN (mkConst (scalar ++ `Csharp)) scalarPrefix)) (some 1) fun reserve _ => do
          forallBoundedTelescope (← inferType (mkAppN source fixed)) (some 4) fun families _ => do
            withLocalDeclD `hp (← mkAppM ``LT.lt #[mkNatLit 0, graph[2]!]) fun hp => do
              let xs := graph ++ caps ++ canonical ++ leading ++ reserve ++ families ++ #[hp]
              unless fixed.size == 32 && families.size == 4 && xs.size == 46 do
                throwError "original common threshold: graph36 + native caps4 + scalar reserve + fixed profiles4 + positive order required"
              k xs (scalarPrefix ++ reserve) (fixed ++ families) hp

/-- All numerical hypotheses of the single joint sampling theorem are proved
on the original geometry; in particular no probability, sample-success or
uniform auxiliary compactness-witness bound occurs as an input. -/
elab "apply_actual_original_common_threshold" : command => liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (base ++ `OriginalPhaseMargins.raw_frame_margin)).type (some 36) fun graph _ =>
    withActualBudgets graph fun xs sb mb hp => do
      let weights := graph[:22].toArray
      let weight (n : Name) := mkAppN (mkConst (base ++ `OriginalWeights ++ n)) weights
      let ms (n : Name) := mkAppN (mkConst (measured ++ n)) mb
      let sc (n : Name) := mkAppN (mkConst (scalar ++ n)) sb
      let win (n : Name) := mkConst (base ++ `OriginalWindow ++ n)
      let hn ← mkAppM ``one_of_five #[graph[1]!]
      let n := (← inferType hn).appArg!
      let A := weight `Index
      withLocalDeclD `i A fun i => do
        let Cband ← mkAppM ``Max.max #[ms `Csharp, sc `Csharp]
        let Cmean ← mkAppM ``Max.max #[ms `Cmean, sc `Cmean]
        let hCband ← mkAppM `le_trans #[ms `hCsharp, ← mkAppM `le_max_left #[ms `Csharp, sc `Csharp]]
        let hFC := mkApp (mkConst ``fourier_nonnegative) n
        let FC := (← inferType hFC).appArg!
        let each (e : Expr) := mkLambdaFVars #[i] e
        let hOne := mkConst ``mask_nonnegative
        let one := (← inferType hOne).appArg!
        let ones ← each one
        let hOnes ← each hOne
        let fixed := weights.push i
        let hScalarS ← mkAppM ``scalar_support_compact
          #[mkAppN (mkConst (base ++ `OriginalScalarCutoffs.compact_χstar)) fixed]
        let scalarSupport ← each (← inferType hScalarS).appArg!
        let cont ← each (← mkAppM `ContDiff.continuous #[mkApp (weight `smooth) i])
        let datum : Array (Option Expr) := #[some A, none, some n, some graph[2]!, some hn, some (mkConst ``Real),
          none, none, none, some (win `mollifier), some (win `compact), some (win `smooth), some (win `mass),
          some (win `nonneg), some (win `support), some hp, some (weight `φ), some (weight `B), some Cband,
          some Cmean, some ones, some (ms `amplitudeBound), some (← each FC), some ones, some ones,
          some (← mkAppM `le_of_lt #[weight `hB]), some (weight `patchBounds), some cont, some hCband,
          some (mkAppN (mkConst (measured ++ `support)) weights), some scalarSupport,
          some (mkAppN (mkConst (measured ++ `compact_support)) weights), some (← each hScalarS),
          some (ms `amplitudeBound_nonnegative), some (← each hFC), some hOnes, some hOnes]
        let proof ← mkAppOptM (base ++ `exists_threshold_original_common_scalar_native_of_amplitude) datum
        discard <| store `initialized xs proof

/-- Name the numeric bounds and the continuation of the SAME threshold proof.
The eventual choice of the actual shift occurs only after both original
current families are supplied. -/
elab "cache_actual_original_threshold_field " which:num : command => liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (target ++ `initialized)).type (some 46) fun xs _ => do
    let a (n : Name) := mkAppN (mkConst (target ++ n)) xs
    match which.getNat with
    | 0 => discard <| store `C xs (← mkAppM ``Classical.choose #[a `initialized]) true
    | 1 =>
      let t := (← whnf (← inferType (a `initialized))).appArg!.beta #[a `C]
      discard <| store `Cspec xs (← mkAppM ``Classical.choose_spec #[a `initialized]) false (some t)
    | 2 => discard <| store `C_pos xs (.proj ``And 0 (a `Cspec))
    | 3 => discard <| store `T₀ xs (← mkAppM ``Classical.choose #[Expr.proj ``And 1 (a `Cspec)]) true
    | 4 =>
      let h := Expr.proj ``And 1 (a `Cspec)
      let t := (← whnf (← inferType h)).appArg!.beta #[a `T₀]
      discard <| store `Tspec xs (← mkAppM ``Classical.choose_spec #[h]) false (some t)
    | 5 => discard <| store `T₀_ge_one xs (.proj ``And 0 (a `Tspec))
    | 6 => discard <| store `continuation xs (.proj ``And 1 (a `Tspec))
    | _ => throwError "original common threshold: invalid numerical field"

end JanetCartan.PhysicalSampling.OriginalCommonThresholdApplication
