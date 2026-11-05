module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSignedPackets
public import JanetCartan.Iteration.PhysicalPairs.Assembly

/-! # The SAME sampled family's original finite signed correction

`primaryWaves` is supplied once at the common eight-field physical sample
stem: it precedes the sign and BOTH nodes. The actual external sample weights
and the revised factor `δ R^A` multiply the original normal-completed packets;
there is no frequency, accuracy, history-label or solution re-selection. All
ordered plus pairs are present. Only minus repetitions are removed.
`main:prop:pairs`, `app:ch_pairs:eq:pairs-exact-offself`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric MeasureTheory FourierTransform
open scoped SchwartzMap NNReal ENNReal BigOperators
namespace JanetCartan.PhysicalPairs.OriginalSignedSum
open PhysicalSampling CanonicalRowComparison SeparatedSampling SamplingKernelBounds Pseudodifferential PhysicalCutoff

variable {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
local notation "E" => Euclidean n
local notation "V" => Euclidean N

def trueWeight {J : Type} (p : ℕ) (B : ℝ) (ψ : J → Point → ℝ) (R : ℝ) (U : J → Lattice → Point) :
    SampleIndex p B ψ (OriginalWindow.window p) (R^(-separationExponent)) U → ℝ :=
  sampleWeight B ψ (OriginalWindow.window p) (R^(-separationExponent)) U

theorem trueWeight_nonneg {J : Type} (p : ℕ) (B : ℝ) (ψ : J → Point → ℝ) (R : ℝ) (U : J → Lattice → Point)
    (P : J → ℝ) (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hp : 0 < p) (hR : 1 ≤ R) :
    ∀ i, 0 ≤ trueWeight p B ψ R U i := sampleWeight_nonneg U (OriginalWindow.window_bounds hp) hψ (Real.rpow_nonneg (zero_le_one.trans hR) _)

@[instance_reducible] def sampleBasis {J : Type} [Fintype J] (p : ℕ) (B : ℝ) (ψ : J → Point → ℝ) (R : ℝ) (U : J → Lattice → Point) :
    Fintype (SampleIndex p B ψ (OriginalWindow.window p) (R^(-separationExponent)) U) := inferInstance

abbrev Members (n N : ℕ) (I : Type) := (minus : Bool) → (i j : I) → (minus = true → i ≠ j) → 𝓢(Euclidean n,Euclidean N)

def ordinaryMinus (packet : Members n N I) (i j : I) : 𝓢(E,V) := if h : i ≠ j then packet true i j (fun _ ↦ h) else 0

def sum (packet : Members n N I) (δ R : ℝ) (μ : I → ℝ) : 𝓢(E,V) := -ProductSum.weightedSignedSum
  (δ*R^(RevisedScales.forcingExponent n)) μ (fun i j ↦ packet false i j (by simp)) (ordinaryMinus packet)

/-- Exact finite price on the physical field above. Individual physical bounds
are used only after the SAME finite family has already been constructed. -/
theorem sum_size (packet : Members n N I) (δ R : ℝ) (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i) (s B : ℝ) (hB : 0 ≤ B)
    (hp : ∀ minus i j hd, (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2*Real.pi) • ξ) •
      𝓕 (complexify (packet minus i j hd)) ξ) 2 volume).toReal ≤ B) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2*Real.pi) • ξ) • 𝓕 (complexify (sum packet δ R μ)) ξ) 2 volume).toReal ≤
      2*B*(δ*R^(RevisedScales.forcingExponent n))^2 * ProductSum.coefficientMass μ := by
  apply physicalWeightedNorm_signedSum_le _ _ _ hμ _ _ hB (fun i j ↦ hp false i j _)
  intro i j hji
  simpa only [ordinaryMinus,dite_eq_left (Ne.symm hji)] using hp true i j (fun _ ↦ Ne.symm hji)
end JanetCartan.PhysicalPairs.OriginalSignedSum
end

public meta section
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 16000
namespace JanetCartan.PhysicalPairs.OriginalSignedSum
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def pkt := `JanetCartan.PhysicalPairs.OriginalSignedPackets
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def samples := `JanetCartan.PhysicalInitialization.OriginalSampledPairs
private def outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
elab "assemble_original_signed_sum " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun p _ => do
    let stem := p[:45].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := a `JanetCartan.embeddingDimension #[n]
    let some pair := (← inferType (a (hist ++ `native_window) p)).find? (fun e => e.isAppOfArity (samples ++ `pair) 30)
      | throwError "lost external same-shift actual pair"
    let qa := pair.getAppArgs
    let I ← inferType p[46]!
    unless I.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do throwError "lost original SampleIndex and extended shift"
    let w := #[a (outer ++ `Index) p[:22].toArray,p[2]!,a (outer ++ `B) p[:22].toArray,a (outer ++ `ψ) p[:22].toArray,qa[23]!,I.getAppArgs.back!]
    if piece.getNat == 0 then
      let original := a (ns ++ `trueWeight) w
      discard <| store (ns ++ `weight) stem original true
      return
    let μ := a (ns ++ `weight) stem
    if piece.getNat == 1 then
      let hpatch := a (outer ++ `patchBounds) p[:22].toArray
      let profile ← forallBoundedTelescope (← inferType hpatch) (some 1) fun z ty => mkLambdaFVars z ty.appArg!
      let pf := a (ns ++ `trueWeight_nonneg) (w ++ #[profile,hpatch,p[43]!,qa[24]!])
      let weight := a (ns ++ `trueWeight) w
      discard <| store (ns ++ `weight_nonneg) stem pf false (some ((← inferType pf).replace fun e => if e == weight then some μ else none))
      return
    let full := (← inferType (a (pkt ++ `packet) p)).bindingDomain!
    withLocalDeclD `primaryWaves full fun Z => do
      let valid := p[45:49].toArray
      let all ← mkLambdaFVars valid (a (pkt ++ `packet) (p.push Z))
      withLocalDeclD `δ (mkConst ``Real) fun δ => do
        let inputs := stem ++ #[Z,δ]
        let raw := ((← getConstInfo (outer ++ `Index)).value! (allowOpaque := true)).beta p[:22].toArray
        let atlas ← synthInstance (mkApp (mkConst `Fintype [.zero]) raw)
        let fin := a (ns ++ `sampleBasis) (#[w[0]!,atlas] ++ w[1:].toArray)
        let eq ← mkAppM ``Classical.typeDecidableEq #[I]
        let args := #[n,N,I,fin,eq,all,δ,qa[23]!,μ]
        let total := a (ns ++ `sum) args
        if piece.getNat == 2 then
          discard <| store (ns ++ `correction) inputs total true
          return
        let pf := a (ns ++ `sum_size) (args.push (a (ns ++ `weight_nonneg) stem))
        let named := a (ns ++ `correction) inputs
        discard <| store (ns ++ `exact_coefficient_mass_bound) inputs pf false (some ((← inferType pf).replace fun e => if e == total then some named else none))
assemble_original_signed_sum 0
assemble_original_signed_sum 1
assemble_original_signed_sum 2
assemble_original_signed_sum 3
end JanetCartan.PhysicalPairs.OriginalSignedSum
end
