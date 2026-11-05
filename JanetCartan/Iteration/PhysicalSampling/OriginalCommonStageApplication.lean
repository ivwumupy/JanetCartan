module

public import JanetCartan.Iteration.PhysicalSampling.OriginalCommonThreshold
public import JanetCartan.Iteration.PhysicalSampling.OriginalColoredRates
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrent
public meta import Lean

/-!
# A single original initial threshold for the known current and rate conditions

After the true simultaneous concentration threshold is chosen, but before any
history, take the maximum of its frequency-admission scale, the scalar-history
scale, and the finite sum of all true measured/current scales. The parent may
still have to dominate additional numerical thresholds from the actual density
and uncut-response producers; this maximum does not prove their estimates.
Retain the
wide `2*Lambda/lam` buffer for the continuum comparison as well as every
literal colored dyadic rate, rather than merely asserting an admissible
sample (`new:sec:order-of-choices`, `app:ch_waves:thm:sampling`).
-/

@[expose] public noncomputable section
namespace JanetCartan.PhysicalSampling.OriginalCommonStageApplication
open RawInputPartition

private theorem positive_one : (0 : ℝ) < 1 := zero_lt_one
private theorem nonnegative_two : (0 : ℝ) ≤ 2 := by norm_num
private theorem one_of_two {S R : ℝ} (hS : 2 ≤ S) (hR : S ≤ R) : 1 ≤ R :=
  (by norm_num : (1 : ℝ) ≤ 2).trans (hS.trans hR)

private theorem original_colored_stage {A : Type*} {p : ℕ} {R0 T₀ ε : ℝ}
    (radial : A → (Fin 3 → Fin (p + 1)) → ℝ) (hrad : ∀ i c, 1 ≤ radial i c)
    (hR : 1 ≤ R0) (stage : ℕ)
    (h : let T := historyScale R0 growthExponent stage
      let Λ := T ^ fineExponent
      let lam := T ^ carrierExponent
      T₀ ≤ T ∧ 1 ≤ Λ ∧ 0 < lam ∧ (∀ _i : A, 2 * Λ / (1 * lam) ≤ ε) ∧
      ∀ (r : A → (Fin 3 → Fin (p + 1)) → ℝ), (∀ i c, 1 ≤ r i c) → ∀ i c,
        0 < (r i c * lam)⁻¹ ∧ (r i c * lam)⁻¹ ≤ 1 ∧
        ∀ j : Fin (cutoffCount Λ), (r i c * lam)⁻¹ * (2 : ℝ) ^ j.val ≤ ε) :
    let T := historyScale R0 growthExponent stage
    let Λ := T ^ fineExponent
    let lam := T ^ carrierExponent
    let L := currentCoefficientScale R0 stage
    let rate := fun i c ↦ (radial i c * lam)⁻¹
    T₀ ≤ T ∧ 1 ≤ Λ ∧ 0 < lam ∧ 1 ≤ L ∧ L ≤ Λ ∧
      (∀ _i : A, 2 * Λ / lam ≤ ε) ∧
      ∀ i c, 0 < rate i c ∧ rate i c ≤ 1 ∧ L ≤ (rate i c)⁻¹ ∧
        ∀ j : Fin (cutoffCount Λ), rate i c * (2 : ℝ) ^ j.val ≤ ε := by
  intro T Λ lam L rate
  obtain ⟨hevent, hfine, hlam, hbuffer, hrates⟩ := h
  have hL := OriginalRates.current_scale_bounds_for_radial_rate hR (le_refl (1 : ℝ)) stage
  refine ⟨hevent, hfine, hlam, hL.1, hL.2.1, ?_, ?_⟩
  · intro i
    simpa only [one_mul] using hbuffer i
  · intro i c
    obtain ⟨ht, ht', hband⟩ := hrates radial hrad i c
    exact ⟨ht, ht', (OriginalRates.current_scale_bounds_for_radial_rate hR (hrad i c) stage).2.2, hband⟩

end JanetCartan.PhysicalSampling.OriginalCommonStageApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalCommonStageApplication
open Lean Meta Elab Command

private def pre := `JanetCartan.PhysicalSampling
private def ns := pre ++ `OriginalCommonStage
private def event := pre ++ `OriginalCommonThreshold
private def cur := `JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrent

private def save (name : Name) (xs : Array Expr) (term : Expr) (data := false)
    (result : Option Expr := none) : MetaM Expr := do
  let name := ns ++ name
  let t ← match result with
    | some r => pure r
    | none => inferType term
  let type ← instantiateMVars (← mkForallFVars xs t)
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "original common stage: incomplete field {name}"
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked actual original initial threshold {name} at {xs.size} inputs"
  return mkAppN (mkConst name) xs

private def withEvent (k : Array Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (event ++ `T₀)).type (some 46) fun xs _ => do
    unless xs.size == 46 do throwError "common stage: expected original prehistory46"
    k xs

private def scalarS (xs : Array Expr) : Expr :=
  mkAppN (mkConst (pre ++ `OriginalScalarHistory.S))
    (xs[:26].toArray ++ xs[27:36].toArray ++ #[xs[40]!])

private def row (xs : Array Expr) (i : Expr) : Array Expr :=
  xs[:40].toArray ++ #[i, mkApp xs[41]! i, mkApp xs[42]! i]

/-- Choose the frequency threshold only once, for the previously fixed joint
event threshold; retain the quantitative Rmin=1 wide buffer. -/
elab "cache_original_common_rate_field " which:num : command => liftTermElabM <| withTransparency .reducible <| withEvent fun x => do
  let a (n : Name) := mkAppN (mkConst (ns ++ n)) x
  match which.getNat with
  | 0 =>
    let one := (← inferType (mkConst ``positive_one)).appArg!
    let source := mkAppN (mkConst (pre ++ `OriginalRates.exists_fine_threshold))
      (x[:22].toArray ++ #[one, mkConst ``positive_one, mkAppN (mkConst (event ++ `T₀)) x])
    discard <| save `rate_source x source
  | 1 => discard <| save `Srate x (← mkAppM ``Classical.choose #[a `rate_source]) true
  | 2 =>
    let r := (← whnf (← inferType (a `rate_source))).appArg!.beta #[a `Srate]
    discard <| save `rate_spec x (← mkAppM ``Classical.choose_spec #[a `rate_source]) false (some r)
  | _ => throwError "original common stage: invalid rate data"

/-- Sum the actual reached threshold of each measured row (every summand is
at least two). The sum is only a numerical upper bound, not a new current. -/
elab "cache_original_common_current_sum " which:num : command => liftTermElabM <| withTransparency .reducible <| withEvent fun x => do
  let A := mkAppN (mkConst (pre ++ `OriginalWeights.Index)) x[:22].toArray
  withLocalDeclD `i A fun i => do
    let Srow := mkAppN (mkConst (cur ++ `S)) (row x i)
    let hrow := mkAppN (mkConst (cur ++ `hS)) (row x i)
    if which.getNat == 0 then
      let univ ← mkAppOptM `Finset.univ #[some A, none]
      discard <| save `currentSum x (← mkAppM `Finset.sum #[univ, ← mkLambdaFVars #[i] Srow]) true
    else
      let positive ← mkAppM `le_trans #[mkConst ``nonnegative_two, hrow]
      let hi ← mkAppM `Finset.mem_univ #[i]
      let all ← withLocalDeclD `hi (← inferType hi) fun j => mkLambdaFVars #[i, j] positive
      let b ← mkAppM `Finset.single_le_sum #[all, hi]
      let sum := mkAppN (mkConst (ns ++ `currentSum)) x
      discard <| save `current_le_sum (x.push i) b false (some (← mkAppM ``LE.le #[Srow, sum]))

/-- Reach the scalar, all native measured/current, and wide frequency
thresholds on exactly the SAME initial scale. -/
elab "cache_original_common_stage_field " which:num : command => liftTermElabM <| withTransparency .reducible <| withEvent fun x => do
  let a (n : Name) := mkAppN (mkConst (ns ++ n)) x
  let rate := a `Srate
  let scalar := scalarS x
  let total := a `currentSum
  let both ← mkAppM ``Max.max #[scalar, total]
  let S := a `S
  let le (v : Expr) := mkAppM ``LE.le #[v, S]
  match which.getNat with
  | 0 => discard <| save `S x (← mkAppM ``Max.max #[rate, both]) true
  | 1 => discard <| save `S_rate x (← mkAppM `le_max_left #[rate, both]) false (some (← le rate))
  | 2 =>
    let h ← mkAppM `le_trans #[← mkAppM `le_max_left #[scalar, total], ← mkAppM `le_max_right #[rate, both]]
    discard <| save `S_scalar x h false (some (← le scalar))
  | 3 =>
    let A := mkAppN (mkConst (pre ++ `OriginalWeights.Index)) x[:22].toArray
    withLocalDeclD `i A fun i => do
      let h ← mkAppM `le_trans #[mkApp (a `current_le_sum) i, ← mkAppM `le_max_right #[scalar, total]]
      let h ← mkAppM `le_trans #[h, ← mkAppM `le_max_right #[rate, both]]
      discard <| save `S_current (x.push i) h false (some (← le (mkAppN (mkConst (cur ++ `S)) (row x i))))
  | 4 => discard <| save `hS x (← mkAppM `le_trans #[Expr.proj ``And 0 (a `rate_spec), a `S_rate])
  | _ => throwError "original common stage: invalid threshold field"

/-- The actual protected color family supplies each radial label; there is no
post-choice radial lower bound, asymptotic, or event-success premise. -/
elab "apply_original_common_stage_rates" : command => liftTermElabM <| withTransparency .reducible <| withEvent fun x => do
  let a (n : Name) := mkAppN (mkConst (ns ++ n)) x
  let w := x[:22].toArray
  let col (n : Name) := mkAppN (mkConst (`JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication ++ n)) w
  let A := mkAppN (mkConst (pre ++ `OriginalWeights.Index)) w
  let pairT ← withTransparency .default <| whnf (← whnf (← inferType (col `Rcolor))).bindingDomain!
  unless pairT.isAppOfArity ``Prod 2 do throwError "original common stage: actual68 index-color product missing"
  withLocalDeclD `i A fun i => withLocalDeclD `c pairT.getAppArgs[1]! fun c => do
    let ic ← mkAppM ``Prod.mk #[i, c]
    let radial ← mkLambdaFVars #[i, c] (mkApp (col `Rcolor) ic)
    let hrad ← mkLambdaFVars #[i, c] (mkApp (col `radial_ge_one) ic)
    withLocalDeclD `Rinit (mkConst ``Real) fun R => do
      withLocalDeclD `hR (← mkAppM ``LE.le #[a `S, R]) fun hR =>
        withLocalDeclD `stage (mkConst ``Nat) fun stage => do
          let hRate ← mkAppM `le_trans #[a `S_rate, hR]
          let hstage := mkAppN (Expr.proj ``And 1 (a `rate_spec)) #[R, hRate, stage]
          let hOne ← mkAppM ``one_of_two #[a `hS, hR]
          let result ← withTransparency .default <| mkAppM ``original_colored_stage #[radial, hrad, hOne, stage, hstage]
          discard <| save `stage_rates (x ++ #[R, hR, stage]) result

end JanetCartan.PhysicalSampling.OriginalCommonStageApplication
