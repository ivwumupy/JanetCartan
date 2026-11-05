module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity

/-! # Literal same-source physical response reconstruction
The source plateau is only the native pointwise `chi3_on_chi2` identity. No
inclusion of the source shoulders in the smaller defect core is assumed.
The proof-only response is compared to the globally uncut response before
reporting the original displacement and derivative amplitudes. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseReconstruction
open CorrectedAtoms CanonicalAtomRealization ResponsePrimarySources ResponseSourceExtension ResponseTransfer
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- The native original tensor is exactly the full matrix source in the
reconstruction theorem; `chiEnv` is only one on the actual source support. -/
theorem native_primary_remodulation
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (r : Euclidean (n-1) × Euclidean 3 → ℝ) (χ : Euclidean n → ℝ)
    (τ : ℝ) (c : Euclidean 3 × Euclidean (n-1)) (φ : Euclidean n → ℝ)
    (hφ : EqOn φ (fun x ↦ phase T Q x c.2) (tsupport χ))
    {core chart : Set (Euclidean n)} (χenv : OutputCutoff core chart)
    (henv : ∀ x ∈ tsupport χ, χenv.toFun x = 1) :
    complexAtomicSource F χ (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (x,c.2)) =
      fun x ↦ waveCarrier τ⁻¹ φ x • ((χ x : ℂ) • fullStrainEnvelope T Q F row col Φ Y r χenv τ c x) := by
  rw [OriginalUncutReconstruction.complexAtomicSource_eq_native_envelope_modulated
    T Q F row col Φ Y r χ τ c φ hφ χenv henv]
  funext x
  simp only [SourceNegative.modulatedSource, carrier_eq_waveCarrier]
  rw [smul_comm]
  rfl

/-- Equality on the original parameter window transfers *all* the joint
coordinate jets, including the physical derivative, to the unchanged uncut
operator. No regularity or agreement of arbitrary algebraic extensions is used. -/
theorem native_coordinate_profiles {n d N : ℕ} {V : Set (Euclidean 3 × Euclidean d)}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d))} (hΩ : IsOpen Ω)
    (hΩV : Ω ⊆ univ ×ˢ V)
    (f g : (Euclidean 3 × Euclidean d) → Euclidean n → EuclideanSpace ℂ (Fin N))
    (he : ∀ c ∈ V, f c = g c) (φ : Euclidean n × (Euclidean 3 × Euclidean d) → ℝ)
    {τ size K : ℝ} (D E : ℕ → ℝ) (reserve m : ℕ)
    (h : ContDiffOn ℝ ∞ (fun p ↦ g p.2 p.1) Ω ∧
      (∀ l r, r ≤ m+1 → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 • g p.2 p.1) l) q‖ ≤
          D r*(τ^2*size)*K^(r-reserve)) ∧
      (∀ l i r, r ≤ m → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
          fderiv ℝ (g p.2) p.1 (EuclideanSpace.single i 1)) l) q‖ ≤ E r*(τ*size)*K^(r-reserve))) :
    ContDiffOn ℝ ∞ (fun p ↦ f p.2 p.1) Ω ∧
      (∀ l r, r ≤ m+1 → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 • f p.2 p.1) l) q‖ ≤
          D r*(τ^2*size)*K^(r-reserve)) ∧
      (∀ l i r, r ≤ m → ∀ q ∈ Ω,
        ‖iteratedFDeriv ℝ r (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
          fderiv ℝ (f p.2) p.1 (EuclideanSpace.single i 1)) l) q‖ ≤ E r*(τ*size)*K^(r-reserve)) := by
  refine ⟨h.1.congr (fun p hp ↦ congrFun (he p.2 (hΩV hp).2) p.1),?_,?_⟩
  · intro l r hr q hq
    have hlocal : (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 • f p.2 p.1) l) =ᶠ[𝓝 q]
        (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 • g p.2 p.1) l) := by
      filter_upwards [hΩ.mem_nhds hq] with p hp
      rw [he p.2 (hΩV hp).2]
    rw [(hlocal.iteratedFDeriv ℝ r).self_of_nhds]
    exact h.2.1 l r hr q hq
  · intro l i r hr q hq
    have hlocal : (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
        fderiv ℝ (f p.2) p.1 (EuclideanSpace.single i 1)) l) =ᶠ[𝓝 q]
        (fun p ↦ (waveCarrier (-τ⁻¹) (fun x ↦ φ (x,p.2)) p.1 •
        fderiv ℝ (g p.2) p.1 (EuclideanSpace.single i 1)) l) := by
      filter_upwards [hΩ.mem_nhds hq] with p hp
      rw [he p.2 (hΩV hp).2]
    rw [(hlocal.iteratedFDeriv ℝ r).self_of_nhds]
    exact h.2.2 l i r hr q hq

theorem region_in_larger_parameter_window {n d : ℕ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d))} {V V' : Set (Euclidean 3 × Euclidean d)}
    (h : Ω ⊆ univ ×ˢ V) (hv : V ⊆ V') : Ω ⊆ univ ×ˢ V' :=
  fun _ hp ↦ ⟨mem_univ _,hv (h hp).2⟩

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseReconstruction
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseReconstructionTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate OriginalPhysicalReducedProfilesTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseReconstruction
private def profiles := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def family := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def phase := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def phy := `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
private def cmp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def comparison := `JanetCartan.PhysicalPrimary.OriginalComparisonResponse
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def reduce := `JanetCartan.PhysicalPrimary.OriginalPhysicalReducedProfiles
private def strain := `JanetCartan.PhysicalPrimary.OriginalFullStrainProfiles
private def canonical := `JanetCartan.CanonicalAtomRealization
private def app (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  logInfo m!"literal physical reconstruction: checked {k}"
  addDocStringCore (ns ++ k) "Literal original full primary response reconstructed from the same native complete inverse and full tensor, including both original quadratures, source shoulders and globally uncut operator (app:ch_response:eq:current-atomic-amplitudes)."
  return h
private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | k+1 => part (.proj ``And 1 e) k
private def named (n : Name) (xs : Array (Name × Expr)) : MetaM Expr := do
  let rec go : Expr → MetaM (Array Expr)
    | .forallE k _ b _ => do
      let some (_,v) := xs.find? (fun kv => kv.1 == k) | throwError "native reconstruction argument {k} of {n}"
      return #[v] ++ (← go b)
    | .mdata _ e => go e
    | _ => pure #[]
  return app n (← go (← getConstInfo n).type)
private def profileSmooth (h : Expr) (arity : Nat) : MetaM Expr := do
  forallBoundedTelescope (← inferType h) (some arity) fun xs _ => mkLambdaFVars xs (.proj ``And 0 (mkAppN h xs))
private def profileBound (h : Expr) (arity : Nat) (m : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType h) (some arity) fun xs _ => do
    let hb := Expr.proj ``And 1 (mkAppN h xs)
    forallBoundedTelescope (← inferType hb) (some 1) fun r _ => do
      withLocalDeclD `hr (← mkAppM ``LE.le #[r[0]!,m]) fun hr =>
        mkLambdaFVars (xs ++ r ++ #[hr]) (mkAppN hb r)

elab "reconstruct_actual_physical_primary_response_part " st:num : command => liftTermElabM do
  let st := st.getNat
  withNativePhysicalInputs fun xs p old s _pt => do
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let fixed := s[:23].toArray
    let nat := mkConst ``Nat
    let base := old[:44].toArray
    let member := app (ind ++ `point) old
    let pp := base.push member
    let wc (k : Name) := app (wave ++ k) s
    let mask (k : Name) := app (masks ++ k) fixed
    let va := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let cn := #[n,s[1]!,va[23]!,va[24]!]
    let V := app (cmp ++ `parameterComparisonWindow) cn
    let wspec := app (cmp ++ `parameterComparisonWindow_spec) cn
    let hV := Expr.proj ``And 0 wspec
    let hSub := Expr.proj ``And 0 (.proj ``And 1 wspec)
    let φ := app (ind ++ `phase) old
    let Z := (← inferType φ).bindingDomain!
    let E := (← inferType φ).bindingBody!.bindingDomain!
    let jt ← mkAppM ``Prod.mk #[← mkFreshExprMVar E,← mkFreshExprMVar Z]
    let jointType ← inferType jt
    let jointφ ← withLocalDeclD `q jointType fun q => do
      mkLambdaFVars #[q] (mkApp2 φ (.proj ``Prod 1 q) (.proj ``Prod 0 q))
    let Ω := app (profiles ++ `region) xs
    let region := app (profiles ++ `region_geometry_actual) xs
    let hΩ := part region 0
    let hΩV := part region 3
    let χ := (← inferType (mask `χ₂_smooth)).appArg!
    let tensor := app (phy ++ `tensor) old
    let env := app (strain ++ `envelope) s
    if st == 0 then
      let source ← withLocalDeclD `c Z fun c => do
        withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc => do
          let hp := app (cmp ++ `Physical.phase_on_source) (old ++ #[c,mkAppN hSub #[c,hc]])
          let eq ← mkAppM (ns ++ `native_primary_remodulation)
            ((#[`T,`Q,`F,`row,`col,`Φ,`Y,`scalar].map wc) ++
              #[χ,s[47]!,c,mkApp φ c,hp,mask `χenv,mask `χ₃_on_χ₂])
          mkLambdaFVars #[c,hc] eq
      discard <| emit `source_remodulation xs source
      return
    withLocalDeclD `reserve nat fun res => do
      let rs := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) res n) (mkNatLit 1)
      withLocalDeclD `hSourceReserve (← mkEq rs s[37]!) fun hr => do
        let static := p ++ #[res,hr]
        let S := app (profiles ++ `S) static
        withLocalDeclD `hResponseReached (← mkAppM ``LE.le #[S,s[39]!]) fun hR => do
          let all := xs ++ #[res,hr,hR]
          let input (k : Name) := app (profiles ++ k) all
          let C := app (profiles ++ `C) static
          let B := app (profiles ++ `B) static
          let hC := app (profiles ++ `C_nonneg) static
          let hB := app (profiles ++ `B_nonneg) static
          let hK := app (family ++ `Point.hK) pp
          let reduced := app (reduce ++ `reduced) xs
          let hsmooth := app (reduce ++ `smooth) xs
          let hg ← mkAppM `ContDiffOn.mono #[hsmooth,hΩV]
          let hentries := input `strain_entries
          let fullV := app (geo ++ `parameter_window) s
          let hVBig ← withLocalDeclD `q jointType fun q => do
            withLocalDeclD `hq (← mkAppM `Membership.mem #[Ω,q]) fun hq => do
              let hc := Expr.proj ``And 1 (mkAppN hΩV #[q,hq])
              mkLambdaFVars #[q,hq] (mkAppN hSub #[.proj ``Prod 1 q,hc])
          let hBig ← mkAppM (ns ++ `region_in_larger_parameter_window) #[hΩV,hSub]
          let ha ← forallBoundedTelescope (← inferType (.proj ``And 0 hentries)) (some 1) fun ij _ => do
            mkLambdaFVars ij (← mkAppM `ContDiffOn.mono #[mkAppN (.proj ``And 0 hentries) ij,hBig])
          let hRA := app (profiles ++ `reserve_le_source) #[res,n,s[37]!,hr]
          let hp := input `reduced_jets
          let hgB ← forallBoundedTelescope (← inferType hp) (some 3) fun rq _ => do
            let hpair := mkAppN hp rq
            let raw := Expr.proj ``And 1 hpair
            forallBoundedTelescope (← inferType raw) (some 1) fun j _ => do
              let hh ← mkAppM (profiles ++ `enlarge_amplitude_grade)
                #[app `JanetCartan.CanonicalAtomRealization.reducedProfileClassicalBudget_nonneg
                    #[n,s[0]!,n,app (reduce ++ `FourierCost) p,app (reduce ++ `FourierCost_nonneg) p,rq[0]!],
                  mkApp (app (profiles ++ `reduced_cost_le) static) rq[0]!,s[48]!,s[51]!,hK,
                  ← mkAppM `Nat.le_refl #[res],mkAppN raw j]
              mkLambdaFVars (j ++ rq) hh
          let haB ← forallBoundedTelescope (← inferType (.proj ``And 1 hentries)) (some 3) fun ijrq tail => do
            let ij := ijrq[0]!
            let r := ijrq[1]!
            let q := ijrq[2]!
            withLocalDeclD `hq (← mkAppM `Membership.mem #[Ω,q]) fun hq => do
              let bound := mkAppN (.proj ``And 1 hentries) (ijrq.push (mkAppN hVBig #[q,hq]))
              let hh ← mkAppM (profiles ++ `enlarge_amplitude_grade)
                #[app (strain ++ `C_nonneg) (s[:39].toArray.push r),
                  mkApp (app (profiles ++ `strain_cost_le) static) r,s[48]!,s[51]!,hK,hRA,bound]
              let _ := tail
              let _ := ij
              mkLambdaFVars (ijrq.push hq) hh
          if st == 1 then
            discard <| emit `reduced_coordinate_bounds all hgB
            discard <| emit `strain_coordinate_bounds all haB
            discard <| emit `strain_coordinate_smooth all ha
            discard <| emit `reduced_smooth all hg
            return
          let _ := env
          let _ := reduced
          let _ := fullV
          let _ := hV
          let _ := hΩ
          let _ := jointφ
          let _ := tensor
          let _ := C
          let _ := B
          let _ := hC
          let _ := hB
  logInfo "actual literal response reconstruction input part checked; native source shoulders kept"

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseReconstructionTemplate
end
set_option Elab.async false
set_option maxHeartbeats 2600000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
reconstruct_actual_physical_primary_response_part 0
reconstruct_actual_physical_primary_response_part 1
