module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalResponseSupport

/-! # Uniform all-order jets of the original full primary response
The response is never cut off. Its genuine original output support extends the
native reconstruction grade to the whole original current window, exactly as
needed on the original root-centered sampled working compact. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseJets

def derivativeCost (n N : ℕ) (E : ℕ → ℝ) (k : ℕ) : ℝ := (N*n : ℕ)*E k

def displacementCost (N : ℕ) (D : ℕ → ℝ) (k : ℕ) : ℝ := (N : ℝ)*∑ j ∈ Finset.range (k+1), D j

theorem derivativeCost_nonneg (n N : ℕ) {E : ℕ → ℝ} (hE : ∀ k, 0 ≤ E k) (k : ℕ) :
    0 ≤ derivativeCost n N E k := mul_nonneg (Nat.cast_nonneg _) (hE _)

theorem displacementCost_nonneg (N : ℕ) {D : ℕ → ℝ} (hD : ∀ k, 0 ≤ D k) (k : ℕ) :
    0 ≤ displacementCost N D k :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun j _ ↦ hD j))

theorem window_geometry {n d : ℕ} {O : Set (Euclidean n × (Euclidean 3 × Euclidean d))}
    {V V' : Set (Euclidean 3 × Euclidean d)} (hO : IsOpen O) (hV : IsOpen V) (hVV' : V ⊆ V') :
    IsOpen (O ∩ (univ ×ˢ V)) ∧ O ∩ (univ ×ˢ V) ⊆ O ∩ (univ ×ˢ V') :=
  ⟨hO.inter (isOpen_univ.prod hV),fun _ h ↦ ⟨h.1,mem_univ _,hVV' h.2.2⟩⟩

theorem physical_sizes_nonneg {τ size K : ℝ} (hτ : 0 < τ) (hs : 0 ≤ size) (hK : 1 ≤ K) :
    0 ≤ τ^2*size ∧ 0 ≤ τ*size ∧ 0 ≤ K :=
  ⟨mul_nonneg (sq_nonneg _) hs,mul_nonneg hτ.le hs,zero_le_one.trans hK⟩

theorem graded_cNorm {n d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Euclidean n × (Euclidean 3 × Euclidean d) → F)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean d))}
    {C : ℕ → ℝ} {small K : ℝ} {reserve : ℕ}
    (hC : ∀ k, 0 ≤ C k) (hs : 0 ≤ small) (hK : 1 ≤ K)
    (h : ∀ k q, q ∈ Ω → ‖iteratedFDeriv ℝ k f q‖ ≤ C k*small*K^(k-reserve))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean d))} (hJ : J ⊆ Ω) (r : ℕ) :
    cNorm J r f ≤ (∑ k ∈ Finset.range (r+1), C k)*small*K^(r-reserve) := by
  calc
    cNorm J r f ≤ ∑ k ∈ Finset.range (r+1), C k*small*K^(k-reserve) :=
      cNorm_le_sum_of_bounds (fun k _ ↦ mul_nonneg (mul_nonneg (hC k) hs)
        (pow_nonneg (zero_le_one.trans hK) _)) (fun k _ q hq ↦ h k q (hJ hq))
    _ ≤ ∑ k ∈ Finset.range (r+1), C k*small*K^(r-reserve) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK
        (Nat.sub_le_sub_right (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) _)) (mul_nonneg (hC _) hs)
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_mul]

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseJets
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseJetsTemplate
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate OriginalPhysicalReducedProfilesTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseJets
private def localProfile := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseProfiles
private def input := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
private def support := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseSupport
private def family := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def cmp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  logInfo m!"original full response jets: checked {k}"
  addDocStringCore (ns ++ k) "All-order actual full primary response amplitude profiles on the whole unchanged original current window; native output support supplies all missing spatial zero germs and every numerical cost is fixed before histories (app:ch_response:eq:response-graded-displacement; app:ch_response:eq:response-graded-derivative)."
  return h
private def subsetRefl (A : Expr) : MetaM Expr := do
  let T := (← inferType A).appArg!
  withLocalDeclD `q T fun q => do
    withLocalDeclD `hq (← mkAppM `Membership.mem #[A,q]) fun hq => mkLambdaFVars #[q,hq] hq

elab "publish_original_full_response_jets_part " st:num : command => liftTermElabM do
  let stage := st.getNat
  if stage == 0 then
    forallBoundedTelescope (← getConstInfo (localProfile ++ `S)).type (some 44) fun fixed _ => do
      let n := mkApp (mkConst ``Nat.succ) fixed[0]!
      let N := app `JanetCartan.embeddingDimension #[n]
      let E := app (localProfile ++ `derivative_coordinate_cost) fixed
      let D := app (localProfile ++ `displacement_coordinate_cost) fixed
      discard <| emit `S fixed (app (localProfile ++ `S) fixed) true
      discard <| emit `S_ge_two fixed (app (localProfile ++ `S_ge_two) fixed)
      discard <| emit `Cresp fixed (app (ns ++ `derivativeCost) #[n,N,E]) true
      discard <| emit `Cdisp fixed (app (ns ++ `displacementCost) #[N,D]) true
      discard <| emit `Cresp_nonneg fixed (app (ns ++ `derivativeCost_nonneg)
        #[n,N,E,app (localProfile ++ `derivative_cost_nonneg) fixed])
      discard <| emit `Cdisp_nonneg fixed (app (ns ++ `displacementCost_nonneg)
        #[N,D,app (localProfile ++ `displacement_cost_nonneg) fixed])
    return
  withNativePhysicalInputs fun xs p old s _pt => do
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let nat := mkConst ``Nat
    let pp := old[:44].toArray.push (app (ind ++ `point) old)
    let rr ← bodyAt (family ++ `Point.R) pp
    let weak := rr.getAppArgs[:32].toArray ++ #[s[39]!,rr.getAppArgs[33]!] ++ s[41:45].toArray
    let source57 := s ++ #[weak[24]!,weak[29]!,weak[30]!,weak[33]!]
    let va := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    let ws := app (cmp ++ `parameterComparisonWindow_spec) #[n,s[1]!,va[23]!,va[24]!]
    let hV := Expr.proj ``And 0 ws
    let hsub := Expr.proj ``And 0 (.proj ``And 1 ws)
    let hO := app (geo ++ `current_open) s
    let window ← mkAppM (ns ++ `window_geometry) #[hO,hV,hsub]
    let Ω := (← inferType (.proj ``And 0 window)).appArg!
    let Ω ← emit `region xs Ω true
    discard <| emit `region_open xs (.proj ``And 0 window)
    let origSmooth (k : Name) := app (`JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity ++ k) source57
    let pointType := (← inferType Ω).appArg!
    let responseSubset ← withLocalDeclD `q pointType fun q => do
      withLocalDeclD `hq (← mkAppM `Membership.mem #[Ω,q]) fun hq =>
        mkLambdaFVars #[q,hq] (.proj ``And 1 (mkAppN (.proj ``And 1 window) #[q,hq]))
    discard <| emit `response_smooth xs (← mkAppM `ContDiffOn.mono #[origSmooth `full_response_smooth,responseSubset])
    discard <| emit `displacement_smooth xs (← mkAppM `ContDiffOn.mono #[origSmooth `displacement_amplitude_smooth,.proj ``And 1 window])
    discard <| emit `derivative_smooth xs (← mkAppM `ContDiffOn.mono #[origSmooth `derivative_amplitude_smooth,.proj ``And 1 window])
    let wc (k : Name) := app (wave ++ k) s
    let χ := (← inferType (app (masks ++ `χ₂_smooth) s[:23].toArray)).appArg!
    let nativeB := app `JanetCartan.PhysicalPrimary.OriginalFullResponse.B weak
    let base := (#[`T,`Q,`F,`row,`col,`Φ,`Y].map wc) ++ #[χ,nativeB,wc `scalar,s[47]!]
    let disp ← mkAppM `JanetCartan.CorrectedAtoms.fullPrimaryResponseDisplacementAmplitude base
    let deriv ← mkAppM `JanetCartan.CorrectedAtoms.fullPrimaryResponseDerivativeAmplitude base
    let jointType := (← inferType disp).bindingDomain!
    let smallΩ := app (input ++ `region) xs
    let hRefl ← subsetRefl smallΩ
    withLocalDeclD `reserve nat fun res => do
      let rs := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) res n) (mkNatLit 1)
      withLocalDeclD `hSourceReserve (← mkEq rs s[37]!) fun hr => do
        let static := p ++ #[res,hr]
        let S := app (ns ++ `S) static
        withLocalDeclD `hResponseReached (← mkAppM ``LE.le #[S,s[39]!]) fun hR => do
          let all := xs ++ #[res,hr,hR]
          let hK := app (family ++ `Point.hK) pp
          let small := app (ns ++ `physical_sizes_nonneg) #[s[47]!,s[50]!,s[45]!,s[48]!,s[51]!,hK]
          let localD ← withLocalDeclD `k nat fun k => do
            let atRegion := app (localProfile ++ `on_sets) (all ++ #[k,smallΩ,hRefl])
            let h := Expr.proj ``And 0 (.proj ``And 1 atRegion)
            let h := mkAppN h #[k,← mkAppM `Nat.le_refl #[k]]
            mkLambdaFVars #[k] h
          let localDisp ← withLocalDeclD `k nat fun k => do
            let allsets := app (localProfile ++ `on_sets) (all.push k)
            let hCN ← forallBoundedTelescope (← inferType allsets) (some 2) fun Jh _ => do
              let z := Expr.proj ``And 0 (mkAppN allsets Jh)
              mkLambdaFVars Jh (mkAppN z #[k,← mkAppM `Nat.le_succ #[k]])
            let h ← mkAppM (support ++ `singleton_norm_le) #[disp,k,hCN]
            mkLambdaFVars #[k] h
          let zero := app (support ++ `amplitude_jets_zero_off_output) xs
          for (label,f,hlocal,hn,nn,index) in [
              (`displacement_jets,disp,localDisp,app (ns ++ `Cdisp_nonneg) static,Expr.proj ``And 0 small,0),
              (`derivative_jets,deriv,localD,app (ns ++ `Cresp_nonneg) static,Expr.proj ``And 0 (.proj ``And 1 small),1)] do
            let hz ← withLocalDeclD `k nat fun k => do
              withLocalDeclD `q jointType fun q => do
                let qzero := mkApp zero q
                forallBoundedTelescope (← inferType qzero) (some 2) fun hh _ => do
                  mkLambdaFVars (#[k,q] ++ hh) (.proj ``And index (mkAppN qzero (hh.push k)))
            let whole ← mkAppM (support ++ `extend_native_grade)
              #[app (support ++ `output_in_interior) xs,f,hz,hn,nn,.proj ``And 1 (.proj ``And 1 small),hlocal]
            let whole ← emit label all whole
            discard <| emit (if index == 0 then `displacement_cNorm else `derivative_cNorm) all
              (← mkAppM (ns ++ `graded_cNorm) #[f,hn,nn,hK,whole])
    let _ := Ω
  logInfo "actual quadratic displacement and linear full derivative jet grades on the whole original current window; no response assumptions, source-dependent maxima, radius change or output recut"

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseJetsTemplate
end
set_option Elab.async false
set_option maxHeartbeats 2600000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
publish_original_full_response_jets_part 0
publish_original_full_response_jets_part 1
