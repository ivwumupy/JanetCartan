module
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageMetric

/-! # Use the actual primary's node jets on its admitted external samples

A constructive primary estimate may hold only after its own threshold or on
the chosen sampling event. It need not supply final waves on impossible
histories or on failed trial shifts. Extend an admitted family by zero solely
at discarded labels to apply the simultaneous signed estimates. On EVERY
admitted prefix the extension is *equal in Schwartz space* to the supplied
waves before any signs or nodes. No selected solution or sampling mass is
changed. The only quantitative primary input is its actual single-node full
demodulated derivative estimate (`main:prop:current-waves`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set
open scoped SchwartzMap Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalSelectedWaves
open UniformStep
variable {n N : ℕ} {I : Type}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin N)

def nodeJets (U : Set E) (C : ℕ → ℝ) (L : ℝ) (θ : I → E → ℝ) (W : I → 𝓢(E,V)) : Prop :=
  ∀ i x, x ∈ U → ∀ k, ‖iteratedFDeriv ℝ k (sampledDerivativeAmplitude (fun i ↦ (W i : E → V)) θ i) x‖ ≤ C k*L^k

noncomputable def atSelected (G : Prop) (w : G → I → 𝓢(E,V)) : I → 𝓢(E,V) := by
  classical
  exact if h : G then w h else 0

theorem agrees {G : Prop} (w : G → I → 𝓢(E,V)) (h : G) : atSelected G w = w h := by classical simp [atSelected,h]

theorem admitted_jets {U : Set E} {C : ℕ → ℝ} {L : ℝ} {θ : I → E → ℝ} {G : Prop} {w : G → I → 𝓢(E,V)}
    (hw : ∀ h : G, nodeJets U C L θ (w h)) (hC : ∀ k, 0 ≤ C k) (hL : 1 ≤ L) : nodeJets U C L θ (atSelected G w) := by
  classical
  by_cases h : G
  · rw [agrees w h]; exact hw h
  · simp only [atSelected,dite_eq_right h]
    intro i x _ k
    have hz : sampledDerivativeAmplitude (fun a ↦ (((0 : I → 𝓢(E,V)) a) : E → V)) θ i = 0 := by
      funext y
      ext b c
      simp [sampledDerivativeAmplitude,sampledDerivative,partialDeriv]
    rw [hz]
    simpa using mul_nonneg (hC k) (pow_nonneg (zero_le_one.trans hL) k)
end JanetCartan.PhysicalPairs.OriginalSelectedWaves
end
public meta section
set_option maxHeartbeats 1100000
set_option maxRecDepth 18000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalSelectedWaves
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSelectedWaves
private def hs := `JanetCartan.PhysicalPairs.SampledHistory
private def cw := `JanetCartan.PhysicalPairs.OriginalCommonWaves
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def met := `JanetCartan.PhysicalPairs.OriginalStageMetric
private def a (k : Name) (v : Array Expr) := mkAppN (mkConst k) v
private def part (h : Expr) : Nat → Expr | 0 => .proj ``And 0 h | k+1 => part (.proj ``And 1 h) k
elab "admit_genuine_primary_samples " piece:num : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (sum ++ `correction)).type (some 46) fun p _ => do
    let b := p[:37].toArray
    let stem := p[:45].toArray
    let dyn := p[37:45].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let N := a `JanetCartan.embeddingDimension #[n]
    let Wtype ← inferType p[45]!
    let I := Wtype.bindingDomain!
    if piece.getNat == 0 then
      discard <| store (ns ++ `Gate) b (← mkForallFVars dyn (mkSort .zero)) true (some (mkSort .one))
      return
    withLocalDeclD `admittedSample (a (ns ++ `Gate) b) fun G => do
      let gate := mkAppN G dyn
      if piece.getNat == 1 then
        discard <| store (ns ++ `AdmittedWaves) (b.push G) (← mkForallFVars dyn (← mkArrow gate Wtype)) true (some (mkSort .one))
        return
      withLocalDeclD `actualPrimary (a (ns ++ `AdmittedWaves) (b.push G)) fun w => do
        let pre := b ++ #[G,w]
        let localW := mkAppN w dyn
        let ext := a (ns ++ `atSelected) #[n,N,I,gate,localW]
        if piece.getNat == 2 then
          discard <| store (ns ++ `extend) pre (← mkLambdaFVars dyn ext) true (some (a (cw ++ `Waves) b))
          return
        let W := a (ns ++ `extend) pre
        if piece.getNat == 3 then
          withLocalDeclD `admitted gate fun h => do
            let pf := a (ns ++ `agrees) #[n,N,I,gate,localW,h]
            discard <| store (ns ++ `at_genuine_sample) (pre ++ dyn ++ #[h]) pf false (some (← mkEq (mkAppN W dyn) (mkApp localW h)))
          return
        let z := a (cw ++ `onLabels) (b.push W)
        forallBoundedTelescope (← inferType (a (fm ++ `first_mask) (b.push z))) (some 2) fun c _ => do
          let gf := (← inferType (a (hs ++ `historyMap) b)).bindingBody!
          let chart := a `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart gf.getAppArgs[:23].toArray
          let R := a `JanetCartan.historyScale #[p[37]!,mkConst `JanetCartan.growthExponent,p[39]!]
          let L := a `JanetCartan.PhysicalPairs.OriginalWindow.fineScale #[b[36]!,R]
          let jTy ← withLocalDeclD `admission gate fun h =>
            mkForallFVars (dyn.push h) (a (ns ++ `nodeJets) #[n,N,I,chart,c[0]!,L,a (met ++ `angles) stem,mkApp localW h])
          if piece.getNat == 4 then
            discard <| store (ns ++ `GenuineNodeProfile) (pre.push c[0]!) jTy true (some (mkSort .zero))
            return
          withLocalDeclD `trueSingleNodeEstimates (a (ns ++ `GenuineNodeProfile) (pre.push c[0]!)) fun hJ => do
            let ledger := (← inferType (a (fm ++ `first_mask) (b ++ #[z] ++ c))).bindingDomain!
            let proof ← forallBoundedTelescope (← whnfR ledger) (some 4) fun y _ => do
              let mut pair := #[]
              let mut t := y[0]!
              for _ in [:12] do
                pair := pair.push (.proj ``PSigma 0 t)
                t := .proj ``PSigma 1 t
              let ps := pair[:8].toArray
              let full := b ++ pair
              let window := part (a (hs ++ `native_window) full) 0
              let hL ← mkAppM ``le_trans #[part window 0,part window 1]
              let good ← mkAppM (ns ++ `admitted_jets) #[mkAppN hJ ps,c[1]!,hL]
              mkLambdaFVars y (← mkAppM ``And.intro #[mkAppN good (#[pair[9]!] ++ y[1:].toArray),mkAppN good (#[pair[10]!] ++ y[1:].toArray)])
            discard <| store (ns ++ `full_profile) (pre ++ c ++ #[hJ]) proof false (some ledger)
admit_genuine_primary_samples 0
admit_genuine_primary_samples 1
admit_genuine_primary_samples 2
admit_genuine_primary_samples 3
admit_genuine_primary_samples 4
admit_genuine_primary_samples 5
end JanetCartan.PhysicalPairs.OriginalSelectedWaves
end
