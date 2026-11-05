module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutReconstruction
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.L2
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-! # Reassembly of the original positive source

No inverse is applied until the two actual admitted tensor quadratures are
identified with the same native local class. The command below discharges the
source smoothness and cutoff hypotheses using the actual Source53/leading
witnesses (`app:ch_response:eq:response-actual-solver-formula`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
namespace JanetCartan.PhysicalPrimary.OriginalStressClass
open MeasureTheory LocalSobolev

/-- Reassemble a pair of admitted quadratures into the *given* local source,
not an independently selected realization. -/
theorem reassemble {n : ℕ} {W : Set (Euclidean n)}
    {u v : LocalL2 W (EuclideanSpace ℂ (Fin n))} {re im : LocalL2 W (Euclidean n)}
    (hs : u = v) (hr : re = l2RealPart (volume.restrict W) v)
    (hi : im = l2RealPart (volume.restrict W) (-Complex.I • v)) :
    l2ComplexInclusion (volume.restrict W) re +
        Complex.I • l2ComplexInclusion (volume.restrict W) im = u := by
  rw [hr,hi,RegularSector.Realization.quadrature_decomposition,hs]

end JanetCartan.PhysicalPrimary.OriginalStressClass
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalStressClassTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalStressClass
private def src := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def waves := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def appl (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (name : Name) (xs : Array Expr) (h : Expr) : MetaM Expr := do
  let result ← store (ns ++ name) xs h
  addDocStringCore (ns ++ name) "Native uncut admitted primary stress on the original cutoff plateau. Its local class is exactly Source.realization at the original physical rate, without another chi2 or a new representative (app:ch_response:eq:response-actual-solver-formula)."
  return result

/-- Take the original full-strain quadrature theorem all the way to the SAME
Source.realization seen by the normalized positive inverse. The remaining two
comparison inputs are geometric (retained phase and theta=1) and are discharged
on the native open cell in the concrete physical-index application. -/
elab "identify_original_source53_stress_class" : command => liftTermElabM do
  withSourcePrefix 53 fun s => do
    let fixed := s[:23].toArray
    let wave (name : Name) := appl (waves ++ name) s
    let geom (name : Name) := appl (geo ++ name) s
    let mask (name : Name) := appl (masks ++ name) fixed
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let χ₂ := (← inferType (mask `χ₂_smooth)).appArg!
    let χ₃ := (← inferType (mask `χ₃_smooth)).appArg!
    let χsrc := (← inferType (mask `χsrc_smooth)).appArg!
    let hProduct ← mkAppM ``congrFun #[mask `source_product]
    let w := appl (src ++ `W) fixed
    let parameterData := (← bodyAt (geo ++ `parameter_window) s).getAppArgs
    unless parameterData.size == 25 do throwError "original stress: lost selected parameter cell"
    let θspec := appl `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.parameterCutoff_spec
      #[n,s[1]!,parameterData[23]!,parameterData[24]!]
    let θ := (← inferType (Expr.proj ``And 0 θspec)).appArg!
    let V := geom `parameter_window
    let rate := s[47]!
    let ρ ← mkAppM ``Inv.inv #[rate]
    let leaf := `JanetCartan.PhysicalPrimary.OriginalUncutReconstruction.fullPrimary_cutoffStressSmoothSource_native_quadratures
    forallBoundedTelescope (← inferType (appl (src ++ `realization) s)) (some 3) fun cf _ => do
      let c := cf[0]!
      let φ := cf[1]!
      let physical := s ++ cf ++ #[ρ]
      let waveData := #[wave `T,wave `Q,wave `F,wave `row,wave `col,wave `Φ,wave `Y,
        wave `scalar,χ₂,rate,c,φ]
      let q0 ← mkAppM leaf waveData
      let t ← whnf (← inferType q0)
      withLocalDeclD `hRetainedPhase t.bindingDomain! fun hφ => do
        withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc => do
          let hs ← mkAppM (geo ++ `source_slice_mem) #[geom `source_product_in_current,mask `χ₂_support_chart,hc]
          withLocalDeclD `hPlateau (← mkEq (mkApp θ c) (← mkNumeral (mkConst `Real) 1)) fun hθ => do
            let xs := s ++ cf ++ #[hφ,hc,hθ]
            let q ← mkAppM leaf (waveData ++ #[hφ,geom `current_open,geom `current_space,geom `current_phase,
              wave `current_map_smooth,wave `current_immersion,wave `current_full_rank,
              wave `scalar_smooth,wave `nullvectors_nonzero,mask `χ₂_smooth,mask `χ₂_compact,hs,
              χsrc,χ₃,mask `χsrc_smooth,hProduct,mask `χ₃_on_χ₂,θ,hθ])
            let q ← emit `native_stress_quadratures xs q
            let spec ← mkAppM ``Classical.choose_spec #[q]
            let spec ← mkAppM ``Classical.choose_spec #[spec]
            let spec ← mkAppM ``Classical.choose_spec #[spec]
            let pair := mkApp spec w
            let classEq := appl (src ++ `realization_eq) physical
            let sides := (← inferType classEq).getAppArgs
            let re := Expr.proj ``And 0 pair
            let im := Expr.proj ``And 1 pair
            let left := (← inferType re).getAppArgs[1]!
            let right := (← inferType im).getAppArgs[1]!
            let he := appl (ns ++ `reassemble) #[n,w,sides[1]!,sides[2]!,left,right,classEq,re,im]
            discard <| emit `source53_class xs he
  logInfo "reassembled both native full-strain stress admissions into the SAME Source.realization at tau^-1; all source and native cutoff regularity supplied by the original Source53/leading datum"

end JanetCartan.PhysicalPrimary.OriginalStressClassTemplate
end
