module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledPairs
public meta import Lean

/-!
# The actual sampled pair at its v2 carrier and true beat

The outer nodes use the common inner event shift. The signed pair is selected
without looking at the current; both evaluations use exactly that pair. The
result gives the projected frequency, norm bounds and compact normalized
source inclusion on all of the actual χ₂ support, with positive
`ρ = R^carrierExponent * beat` (`app:ch_regular:thm:no-return`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalInitialization.OriginalSampledPairs
open SignedPairs

private theorem stage_one {S R : ℝ} (hS : 2 ≤ S) (hR : S ≤ R) (j : ℕ) :
    1 ≤ historyScale R growthExponent j := by
  have h := (by norm_num : (1:ℝ) ≤ 2).trans (hS.trans hR)
  exact h.trans (le_historyScale h j)

/-- The true frequency measured against the actual coarse carrier. The loss of
one mesh affects only the lower bound; the annulus and subspace gaps concern
the normalized true beat. -/
private theorem at_stage_frequency {n : ℕ} {T a A beat : ℝ} {v : Euclidean n} {K : Set (Euclidean n)}
    (hT : 1 ≤ T) (hsep : T^(-separationExponent) / 2 ≤ beat)
    (bound : (∀ L ∈ cubeBadSubspaces n, a*beat ≤ ‖projectAway L v‖) ∧ v ≠ 0 ∧
      (∀ lam : ℝ, 0 ≤ lam → a*(lam*beat) ≤ ‖lam • v‖ ∧ ‖lam • v‖ ≤ A*(lam*beat)) ∧
      beat⁻¹ • v ∈ K) :
    let lam := T^carrierExponent
    let trueFrequency := lam*beat
    0 < trueFrequency ∧ lam*(T^(-separationExponent)/2) ≤ trueFrequency ∧
      a*trueFrequency ≤ ‖lam • v‖ ∧ ‖lam • v‖ ≤ A*trueFrequency ∧
      (∀ L ∈ cubeBadSubspaces n, a*beat ≤ ‖projectAway L v‖) ∧ beat⁻¹ • v ∈ K := by
  intro lam trueFrequency
  have hT0 := zero_lt_one.trans_le hT
  have hp : 0 < lam := Real.rpow_pos_of_pos hT0 _
  have hb := (half_pos (Real.rpow_pos_of_pos hT0 (-separationExponent))).trans_le hsep
  exact ⟨mul_pos hp hb,mul_le_mul_of_nonneg_left hsep hp.le,
    (bound.2.2.1 lam hp.le).1,(bound.2.2.1 lam hp.le).2,bound.1,bound.2.2.2⟩

end JanetCartan.PhysicalInitialization.OriginalSampledPairs
end

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledPairs
open Lean Meta Elab Command OriginalProtectedTemplate
private def root := `JanetCartan.PhysicalInitialization.OriginalSampledPairs
private def applied (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs

/- One pair for the actual extended shift, before evaluating any current.
   No resampling on the larger outer cube. -/
run_cmd liftTermElabM do
  let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
  let existsName := root ++ `exists_on_outer_sample
  forallBoundedTelescope (← getConstInfo existsName).type (some 25) fun xs _ => do
    let p := xs[:22].toArray
    let mesh ← mkAppM ``HPow.hPow #[xs[23]!,← mkAppM ``Neg.neg #[mkConst `JanetCartan.separationExponent]]
    let innerB := applied `JanetCartan.PhysicalSampling.OriginalWeights.B p
    let J := applied (outer ++ `Index) p
    let ξspace := applied `JanetCartan.Sampling.ShiftSpace #[p[2]!,innerB,mesh]
    withLocalDeclD `ξ (← mkArrow J ξspace) fun ξ => do
      let U ← withLocalDeclD `i J fun i =>
        mkLambdaFVars #[i] (applied `JanetCartan.Sampling.extendedShift #[p[2]!,innerB,mesh,mkApp ξ i])
      let raw := applied existsName (xs.push U)
      forallBoundedTelescope (← inferType raw) (some 4) fun signs _ => do
        let ex := mkAppN raw signs
        let args := xs ++ #[ξ] ++ signs
        let q ← store (root ++ `pair) args (← mkAppM ``Classical.choose #[ex]) true
        let pred := (← whnf (← inferType ex)).appArg!
        discard <| store (root ++ `pair_spec) args (← mkAppM ``Classical.choose_spec #[ex]) false
          (some (pred.beta #[q]))

/- Quantify over the same native ξ that the common event must supply. This
   statement needs no successful-event, frequency-bound or source-cone premise. -/
run_cmd liftTermElabM do
  let name := root ++ `on_actual_source
  let graph := `JanetCartan.PhysicalInitialization.OriginalRegular.Graph
  forallBoundedTelescope (← getConstInfo name).type (some 42) fun x _ => do
    let s := (← inferType x[37]!).getAppArgs[2]!
    unless s.isAppOfArity (graph ++ `S) 34 do throwError "missing original graph threshold"
    let hT ← mkAppM ``stage_one #[applied (graph ++ `hS) s.getAppArgs,x[37]!,x[38]!]
    let T := (← inferType hT).appArg!
    let source := applied name x
    withLocalDeclD `hp (← mkAppM ``LT.lt #[mkNatLit 0,x[2]!]) fun hp => do
      let init := x[:22].toArray ++ #[hp,T,hT]
      let p0 := applied (root ++ `pair) init
      forallBoundedTelescope (← inferType p0) (some 5) fun sample _ => do
        let q := mkAppN p0 sample
        let spec := applied (root ++ `pair_spec) (init ++ sample)
        let h ← forallBoundedTelescope (← inferType source) (some 2) fun y _ => do
          let bounds := mkAppN source (y.push q)
          let hbeat := Expr.proj ``And 0 spec
          let beat := (← inferType hbeat).appArg!
          let ne := (← inferType bounds).appArg!.getAppArgs[0]!
          unless ne.isAppOfArity ``Ne 3 do throwError "missing nonzero native signed vector"
          let col (k : Name) := applied (`JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication ++ k) x[:22].toArray
          let n := mkApp (mkConst ``Nat.succ) x[0]!
          mkLambdaFVars y (applied ``at_stage_frequency
            #[n,T,col `aColor,col `AColor,beat,ne.getAppArgs[1]!,col `Ksource,hT,hbeat,bounds])
        discard <| store (root ++ `actual_colored_frequency) (x ++ #[hp] ++ sample) h
          -- q was chosen from geometry alone, BEFORE the physical point.
        logInfo "Original outer sample on same inner ξ: one pair before the current, exact signed scalar identities, true beat/canonical radial frequency and normalized paired covector on the whole original χ₂ support."

end JanetCartan.PhysicalInitialization.OriginalSampledPairs
end

#print axioms JanetCartan.PhysicalInitialization.OriginalSampledPairs.exists_on_outer_sample
#print axioms JanetCartan.PhysicalInitialization.OriginalSampledPairs.on_actual_source
#print axioms JanetCartan.PhysicalInitialization.OriginalSampledPairs.pair
#print axioms JanetCartan.PhysicalInitialization.OriginalSampledPairs.pair_spec
#print axioms JanetCartan.PhysicalInitialization.OriginalSampledPairs.actual_colored_frequency
