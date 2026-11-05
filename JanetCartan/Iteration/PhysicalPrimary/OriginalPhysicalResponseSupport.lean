module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalResponseProfiles

/-! # Genuine native output support extends the response jet profiles
No sampling radius is changed. The native output lies strictly inside the
protected source, so its complement has a joint zero germ. Consequently the
local reconstruction bounds hold on the full original current window. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseSupport
open CorrectedAtoms ResponseSourceExtension PrimarySourceAdmission
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

theorem complex_response_support {n N : ℕ}
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (t : Euclidean n → Matrix (Fin n) (Fin n) ℂ) {K : Set (Euclidean n)} (hK : IsClosed K)
    (hr : tsupport (B (tensorFieldRealPart t)) ⊆ K)
    (hi : tsupport (B (tensorFieldImagPart t)) ⊆ K) :
    tsupport (complexifyResponse B t) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hk
  have hre := image_eq_zero_of_notMem_tsupport (fun hh ↦ hk (hr hh))
  have him := image_eq_zero_of_notMem_tsupport (fun hh ↦ hk (hi hh))
  apply hx
  simp [complexifyResponse, hre, him]

theorem output_in_source_interior {n : ℕ} {K X : Set (Euclidean n)} {r : ℝ}
    (hK : K ⊆ ball 0 r) (hX : closedBall 0 r ⊆ X) : K ⊆ interior X :=
  hK.trans (isOpen_ball.subset_interior_iff.mpr (ball_subset_closedBall.trans hX))

/-- Both true response amplitudes have a zero joint germ off the same native
compact output. The arbitrary carrier need not even be regular there. -/
theorem amplitude_jets_zero {n d N : ℕ} {V : Set (Euclidean 3 × Euclidean d)}
    (hV : IsOpen V) {K : Set (Euclidean n)} (hK : IsClosed K)
    (f : (Euclidean 3 × Euclidean d) → Euclidean n → EuclideanSpace ℂ (Fin N))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ K)
    (ψ : Euclidean n × (Euclidean 3 × Euclidean d) → ℂ)
    {q : Euclidean n × (Euclidean 3 × Euclidean d)} (hq : q.2 ∈ V) (hx : q.1 ∉ K) (k : ℕ) :
    iteratedFDeriv ℝ k (fun p ↦ ψ p • f p.2 p.1) q = 0 ∧
      iteratedFDeriv ℝ k (fun p ↦ ψ p • (fun l i ↦
        fderiv ℝ (f p.2) p.1 (EuclideanSpace.single i 1) l : Matrix (Fin N) (Fin n) ℂ)) q = 0 := by
  have hz c (hc : c ∈ V) x (hx : x ∉ K) : f c =ᶠ[𝓝 x] (fun _ ↦ 0) :=
    notMem_tsupport_iff_eventuallyEq.mp (fun hh ↦ hx (hs c hc hh))
  have hd c (hc : c ∈ V) x (hx : x ∉ K) : fderiv ℝ (f c) x = 0 := by
    rw [(hz c hc x hx).fderiv_eq]
    simp
  have hnd : Kᶜ ×ˢ V ∈ 𝓝 q := (hK.isOpen_compl.prod hV).mem_nhds ⟨hx,hq⟩
  have hdisp : (fun p ↦ ψ p • f p.2 p.1) =ᶠ[𝓝 q] (fun _ ↦ 0) := by
    filter_upwards [hnd] with p hp
    simp [(hz p.2 hp.2 p.1 hp.1).self_of_nhds]
  have hderiv : (fun p ↦ ψ p • (fun l i ↦
        fderiv ℝ (f p.2) p.1 (EuclideanSpace.single i 1) l : Matrix (Fin N) (Fin n) ℂ)) =ᶠ[𝓝 q]
        (fun _ ↦ 0) := by
    filter_upwards [hnd] with p hp
    rw [hd p.2 hp.2 p.1 hp.1]
    change ψ p • (0 : Matrix (Fin N) (Fin n) ℂ) = 0
    exact smul_zero _
  exact ⟨by rw [(hdisp.iteratedFDeriv ℝ k).self_of_nhds]; simp,
    by rw [(hderiv.iteratedFDeriv ℝ k).self_of_nhds]; simp⟩

theorem primary_amplitude_jets_zero
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (χ : Euclidean n → ℝ) (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n-1) × Euclidean 3 → ℝ) (τ : ℝ)
    {V : Set (Euclidean 3 × Euclidean (n-1))} (hV : IsOpen V)
    {K : Set (Euclidean n)} (hK : IsClosed K)
    (hs : ∀ c ∈ V, tsupport (fullPrimaryResponse T Q F row col Φ Y χ B τ r c) ⊆ K)
    {q : Euclidean n × (Euclidean 3 × Euclidean (n-1))} (hq : q.2 ∈ V) (hx : q.1 ∉ K) (k : ℕ) :
    iteratedFDeriv ℝ k (fullPrimaryResponseDisplacementAmplitude T Q F row col Φ Y χ B r τ) q = 0 ∧
      iteratedFDeriv ℝ k (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) q = 0 := by
  exact amplitude_jets_zero hV hK (fullPrimaryResponse T Q F row col Φ Y χ B τ r) hs
    (fun p ↦ Complex.exp (-Complex.I * (phase T Q p.1 p.2.2 / τ : ℝ))) hq hx k

/-- Extend a genuine pointwise grade by the actual zero germ, without multiplying
the response by an auxiliary cutoff and without changing the sampled set. -/
theorem extend_native_grade {n d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set (Euclidean n × (Euclidean 3 × Euclidean d))}
    {X K : Set (Euclidean n)} {V : Set (Euclidean 3 × Euclidean d)}
    (hKX : K ⊆ interior X) (f : Euclidean n × (Euclidean 3 × Euclidean d) → F)
    (hz : ∀ k q, q.2 ∈ V → q.1 ∉ K → iteratedFDeriv ℝ k f q = 0)
    {C : ℕ → ℝ} {small L : ℝ} {reserve : ℕ} (hC : ∀ k, 0 ≤ C k) (hs : 0 ≤ small) (hL : 0 ≤ L)
    (h : ∀ k q, q ∈ O ∩ (interior X ×ˢ V) →
      ‖iteratedFDeriv ℝ k f q‖ ≤ C k*small*L^(k-reserve)) :
    ∀ k q, q ∈ O ∩ (univ ×ˢ V) → ‖iteratedFDeriv ℝ k f q‖ ≤ C k*small*L^(k-reserve) := by
  intro k q hq
  by_cases hx : q.1 ∈ interior X
  · exact h k q ⟨hq.1,hx,hq.2.2⟩
  · rw [hz k q hq.2.2 (fun hh ↦ hx (hKX hh)),norm_zero]
    exact mul_nonneg (mul_nonneg (hC _) hs) (pow_nonneg hL _)

theorem singleton_norm_le {n d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d))}
    (f : Euclidean n × (Euclidean 3 × Euclidean d) → F) (k : ℕ) {C : ℝ}
    (h : ∀ J ⊆ Ω, cNorm J k f ≤ C) : ∀ q ∈ Ω, ‖iteratedFDeriv ℝ k f q‖ ≤ C := by
  intro q hq
  apply (norm_iteratedFDeriv_le_cNorm_of_bddAbove (s := {q})
    (by simp only [image_singleton]; exact bddAbove_singleton) (mem_singleton q) (le_refl k)).trans
  exact h {q} (singleton_subset_iff.mpr hq)

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseSupport
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseSupportTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate OriginalPhysicalReducedProfilesTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseSupport
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def family := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def cmp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def support := `JanetCartan.PhysicalPrimary.OriginalSolverSupport
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  logInfo m!"native supported amplitude: checked {k}"
  addDocStringCore (ns ++ k) "The genuine original output support gives a joint zero germ for both original response amplitudes; no auxiliary response recut or posthistory sampling-radius change (app:ch_response:eq:current-atomic-amplitudes)."
  return h

elab "prove_original_supported_response_amplitude_jets" : command => liftTermElabM do
  withNativePhysicalInputs fun xs _p old s _pt => do
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let fixed := s[:23].toArray
    let pp := old[:44].toArray.push (app (ind ++ `point) old)
    let ph ← bodyAt (family ++ `Point.φ) pp
    let residual ← bodyAt (family ++ `Point.R) pp
    let weak := residual.getAppArgs[:32].toArray ++ #[s[39]!,residual.getAppArgs[33]!] ++ s[41:45].toArray
    let hInterior ← mkAppM (ns ++ `output_in_source_interior)
      #[app (support ++ `outputSupport_in_physical_ball) fixed,
        app (cmp ++ `Actual.physical_ball_in_source) (fixed.push ph.getAppArgs[32]!)]
    discard <| emit `output_in_interior xs hInterior
    let hKclosed ← mkAppM `IsCompact.isClosed #[app (support ++ `outputSupport_compact) fixed]
    let nativeB := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.B weak
    let χ := (← inferType (app (masks ++ `χ₂_smooth) fixed)).appArg!
    let wc (k : Name) := app (wave ++ k) s
    let base := (#[`T,`Q,`F,`row,`col,`Φ,`Y].map wc) ++ #[χ,nativeB,wc `scalar,s[47]!]
    let Z := (← inferType (app (ind ++ `phase) old)).bindingDomain!
    let va := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let ws := app (cmp ++ `parameterComparisonWindow_spec) #[n,s[1]!,va[23]!,va[24]!]
    let V := (← inferType (.proj ``And 0 ws)).appArg!
    let hSub := Expr.proj ``And 0 (.proj ``And 1 ws)
    let hs ← withLocalDeclD `c Z fun c => do
      withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc => do
        let admissions := app (wave ++ `source_quadratures) (s ++ #[c,mkAppN hSub #[c,hc]])
        let tensor := mkApp (app `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation.tensor old) c
        let rr := (← inferType (.proj ``And 0 admissions)).appArg!
        let ii := (← inferType (.proj ``And 1 admissions)).appArg!
        let rs ← mkAppM ``Subtype.mk #[rr,.proj ``And 0 admissions]
        let isrc ← mkAppM ``Subtype.mk #[ii,.proj ``And 1 admissions]
        let hr := app `JanetCartan.PhysicalPrimary.OriginalFullResponseCompact.support (weak.push rs)
        let hi := app `JanetCartan.PhysicalPrimary.OriginalFullResponseCompact.support (weak.push isrc)
        let proof ← mkAppM (ns ++ `complex_response_support) #[nativeB,tensor,hKclosed,hr,hi]
        mkLambdaFVars #[c,hc] proof
    let hs ← emit `response_support xs hs
    let jt := mkApp2 (mkConst ``Prod [.zero,.zero]) (mkApp (mkConst `JanetCartan.Euclidean) n) Z
    let K := app (support ++ `outputSupport) fixed
    let zero ← withLocalDeclD `q jt fun q => do
      withLocalDeclD `hq (← mkAppM `Membership.mem #[V,.proj ``Prod 1 q]) fun hq => do
        withLocalDeclD `hx (mkNot (← mkAppM `Membership.mem #[K,.proj ``Prod 0 q])) fun hx => do
          withLocalDeclD `k (mkConst ``Nat) fun k => do
            let h ← mkAppM (ns ++ `primary_amplitude_jets_zero) (base ++ #[.proj ``And 0 ws,hKclosed,hs,hq,hx,k])
            mkLambdaFVars #[q,hq,hx,k] h
    discard <| emit `amplitude_jets_zero_off_output xs zero
  logInfo "actual native full response is supported strictly inside the original protected source; both amplitude families vanish to all joint orders off this same output"

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseSupportTemplate
end
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
prove_original_supported_response_amplitude_jets
