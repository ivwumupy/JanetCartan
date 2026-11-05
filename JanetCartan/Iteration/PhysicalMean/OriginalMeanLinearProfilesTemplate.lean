module

public import JanetCartan.Iteration.PhysicalBackground.NativeDensityProfiles
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalNormalSourceTail
public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalPrefix
public import JanetCartan.Iteration.PhysicalNormalInverse.NormalizedComparison
public import JanetCartan.Iteration.PhysicalMean.CarrierOnlyTail
public import JanetCartan.Iteration.PhysicalMean.LinearProfilesTemplate
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-! Actual positive-current common-measurement inverse. Consumer: the literal
fixedSourceLinear low defect and all-order source profile
(new:sec:mean-source-equation, new:eq:source-bound). -/

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearProfilesTemplate
open Lean Meta Elab Command Term
open PhysicalInitialization.OriginalProtectedTemplate (store)
open PhysicalBackground.NativeReferenceSourceTemplate (termWith)

private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles
private def admission := `JanetCartan.PhysicalBackground.NativeAdmission

private def part (h : Expr) : Nat → Expr
  | 0 => .proj ``And 0 h
  | j+1 => part (.proj ``And 1 h) j

private def save (name : Name) (x : Array Expr) (v : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let result ← store (root ++ name) x v data target
  addDocStringCore (root ++ name)
    "The SAME actual positive-current common-measurement inverse selected from NativeAdmission, with original coefficient/cutoffs and unchanged density. No inverse success is assumed (new:sec:mean-source-equation)."
  return result

elab "construct_original_mean_positive_current" : command => liftTermElabM do
  let info ← getConstInfo (admission ++ `positive_inverse_exists)
  forallBoundedTelescope info.type (some 39) fun x result => do
    unless x.size == 39 do throwError "original mean current: expected actual admission39"
    let existsNative := mkAppN (mkConst (admission ++ `positive_inverse_exists)) x
    let result ← whnf result
    unless result.isAppOfArity ``Exists 2 do
      throwError "original mean current: actual positive carrier existential disappeared"
    let Vop ← save `Current.Vop x (← mkAppM ``Classical.choose #[existsNative]) true
    let native ← save `Current.native x (← mkAppM ``Classical.choose_spec #[existsNative]) false
      (some (result.appArg!.beta #[Vop]))
    discard <| save `Current.representation x (.proj ``And 0 native)
    let ops := Expr.proj ``And 1 native
    for (name,j) in #[(`coefficient_smooth,0), (`physical_bound,1), (`gap,2),
        (`inverse_norm,3), (`elliptic,4), (`inverse_spec,5), (`adjoint_spec,6),
        (`right_inverse,7), (`paired_spec,8), (`normal_inverse,9),
        (`inverse_normal,10), (`raw_regular,11)] do
      discard <| save (`Current ++ name) x (part ops j)
    let gap := part ops 2
    let ((image,carriers,psi),gamma) ← forallBoundedTelescope (← inferType gap) (some 1) fun _ out => do
      let out ← Core.betaReduce (← zetaReduce out)
      let some row := out.find? (·.isAppOf `JanetCartan.ContinuumRow.augmentedRow)
        | throwError "original mean current: lost actual augmented common-measurement row"
      let a := row.getAppArgs
      unless out.isAppOfArity ``LE.le 4 do
        throwError "original mean current: lost native adjoint gap"
      let lhs := out.getAppArgs[2]!
      unless lhs.isAppOf ``HMul.hMul do
        throwError "original mean current: gap no longer has gamma*norm^2"
      return ((a[a.size-3]!,a[a.size-2]!,a.back!),lhs.getAppArgs[lhs.getAppNumArgs-2]!)
    let imargs := image.getAppArgs
    unless image.isAppOf `JanetCartan.ContinuumRow.imageChannel do
      throwError "original mean current: image channel changed"
    let c ← save `Current.coefficient x imargs[imargs.size-3]! true
    let meas ← save `Current.measurement x[:21].toArray imargs[imargs.size-2]! true
    let source ← save `Current.source x[:21].toArray imargs.back! true
    let exterior ← save `Current.exterior x[:21].toArray psi true
    let U ← save `Current.carriers x carriers true
    let image ← save `Current.image x
      (← mkAppM `JanetCartan.ContinuumRow.imageChannel #[c,meas,source]) true
    let row ← save `Current.row x
      (← mkAppM `JanetCartan.ContinuumRow.augmentedRow #[image,U,exterior]) true
    let normal ← save `Current.normal x
      (← mkAppM `JanetCartan.ContinuumRow.augmentedNormal #[image,U,exterior]) true
    let Q0 ← save `Current.Q0 x (← mkAppM `ContinuousLinearMap.inverse #[normal]) true
    let gamma ← save `Current.gamma x[:21].toArray gamma true
    let original := x[:21].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[original[0]!,original[1]!,original[20]!]
    let selected := original.set! 20 capped
    let hMeasure := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) selected
    let hCell := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hMeasureCell) selected
    for (name,i) in #[(`measurement_smooth,1),(`source_smooth,2)] do
      discard <| save (`Current ++ name) original (← termWith
        [(`n,x[0]!),(`hr,hMeasure),(`hcell,hCell)]
        s!"JanetCartan.ContinuumRow.FixedCutoffs.periodic_smooth (n := n) hr hcell {i}")
    let hInner := mkAppN (mkConst `JanetCartan.PhysicalSeed.SourceInverseBoundary.hrInner) selected
    let hInnerCell := mkAppN (mkConst `JanetCartan.PhysicalSeed.SourceInverseBoundary.hInnerCell) selected
    discard <| save `Current.exterior_smooth original (← termWith
      [(`n,x[0]!),(`hr,hInner),(`hcell,hInnerCell)]
      "JanetCartan.ContinuumNormal.innerCutoff_smooth (n := n) hr hcell")
    let hGlobal := mkAppN (mkConst `JanetCartan.PhysicalSeed.SourceInverseBoundary.fact8) selected
    discard <| save `Current.gamma_pos original
      (← termWith [(`gamma,gamma),(`hGlobal,hGlobal)]
        "(half_pos (half_pos hGlobal) : 0 < gamma)")
    let raw := part ops 11
    let Qreg ← forallBoundedTelescope (← inferType (part ops 5)) (some 3) fun w _ => do
      mkLambdaFVars w (.proj ``And 0 (mkAppN (part ops 5) w))
    discard <| save `Current.Q0_regular x Qreg
    let hrow ← mkAppM
      `JanetCartan.PhysicalNormalInverse.OriginalNormalSourceTail.augmentedRow_norm_of_physical
      #[image,U,exterior,part ops 1]
    discard <| save `Current.row_bound x hrow
    let ht ← inferType hrow
    unless ht.isAppOfArity ``LE.le 4 do throwError "original mean current: row budget missing"
    discard <| save `Current.Crow original ht.appArg! true
    let closed ← termWith [(`row,row),(`Q0,Q0),(`raw,raw)]
      "show ∀ (e : JanetCartan.CurrentMean.SmoothResidual _ ) (s : ℕ), row.adjoint (Q0 (JanetCartan.CurrentMean.smoothResidualToL2 _ e)) ∈ JanetCartan.CarrierSobolev.augmentedInputLevel _ _ s from raw"
    discard <| save `Current.source_regular x closed
  logInfo "actual positive current: one Vop, COMMON measured carriers, exact Q0, gamma/gap, all-order regularity and uncut row budget; no v=0 estimate"

private def bodyAt (name : Name) (xs : Array Expr) : MetaM Expr := do
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true)
    | throwError "original mean profile: missing actual producer body {name}"
  Core.betaReduce (← zetaReduce (body.beta xs))

/-- Close the shifted positive-current paired bound from the actual native
map and the SAME admitted positive initial scalar. All new premises are only
numerical reserves; the high profiles themselves are applied, not assumed. -/
elab "construct_original_mean_current_source_profiles" : command => liftTermElabM do
  let density := `JanetCartan.PhysicalBackground.NativeDensityProfiles
  let nativeDensity := `JanetCartan.PhysicalBackground.NativeDensity
  let leading := `JanetCartan.PhysicalInitialization.CurrentLeading
  let leadingProfile := `JanetCartan.PhysicalBackground.NativeLeadingProfiles
  let originalCurrent := `JanetCartan.PhysicalInitialization.OriginalCurrent
  let info ← getConstInfo (density ++ `initial_profile)
  forallBoundedTelescope info.type (some 45) fun x _ => do
    unless x.size == 45 do throwError "original mean source: expected actual high-density45"
    let original := x[:21].toArray
    let admissionArgs := x[:33].toArray ++ x[38:44].toArray
    let current (name : Name) := mkAppN (mkConst (root ++ `Current ++ name)) admissionArgs
    let pair := current `paired_spec
    let (coefHead,coefArgs) ← forallBoundedTelescope (← inferType pair) (some 3) fun _ out => do
      let out ← Core.betaReduce (← zetaReduce out)
      let some coef := out.find? (·.isAppOf `JanetCartan.ContinuumCommutator.retainedCoefficientProfile)
        | throwError "original mean source: positive pair lost the retained coefficient profile"
      pure (coef.getAppFn,coef.getAppArgs[:coef.getAppNumArgs-1].toArray)
    let K := coefArgs[coefArgs.size-5]!
    let Kimage := coefArgs[coefArgs.size-4]!
    let Kin := coefArgs[coefArgs.size-3]!
    let F := coefArgs[coefArgs.size-2]!
    let initial := coefArgs.back!
    let H := mkAppN coefHead coefArgs
    let index := mkAppN (mkConst (nativeDensity ++ `geometryIndex)) original
    let mut cur := mkAppN (mkConst (admission ++ `current)) (admissionArgs.push index)
    for _ in [:8] do
      if cur.isAppOfArity (leading ++ `Selected.current) 38 then break
      cur ← bodyAt cur.getAppFn.constName! cur.getAppArgs
    unless cur.isAppOfArity (leading ++ `Selected.current) 38 do
      throwError "original mean source: lost same actual selected leading current38"
    let leadingArgs := cur.getAppArgs
    let cell ← bodyAt (leading ++ `Selected.current) leadingArgs
    unless cell.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingCell.current 36 do
      throwError "original mean source: lost retained current36"
    let hdata := cell.getAppArgs[34]!
    unless hdata.isAppOfArity (leading ++ `AtPatch.fact0) 38 do
      throwError "original mean source: lost original map profile patch"
    let patch := hdata.getAppArgs.back!
    let Amap := mkAppN (mkConst (leading ++ `Amap)) (x[:31].toArray.push patch)
    let hAmap := mkAppN (mkConst (leading ++ `fact1)) (x[:31].toArray.push patch)
    let hF := mkAppN (mkConst (leadingProfile ++ `map_smooth)) leadingArgs
    let mapProfile := mkAppN (mkConst (leadingProfile ++ `map_profile)) leadingArgs
    unless ← isDefEq F (mkAppN (mkConst (leadingProfile ++ `map)) leadingArgs) do
      throwError "original mean source: pair/map profile use different physical maps"
    let prehistory := x[:38].toArray
    let initialType ← whnf (← inferType initial)
    let .forallE _ I _ _ := initialType
      | throwError "original mean source: lost native carrier index"
    let scalarC ← withLocalDeclD `i I fun i => do
      let C := mkAppN (mkConst (density ++ `initialC)) (prehistory.push i)
      mkLambdaFVars #[i] (← termWith [(`sigma,x[21]!),(`C,C)] "fun s : ℕ ↦ sigma*C s")
    let scalarC ← save `Source.scalarC prehistory scalarC true
    let hScalarC ← withLocalDeclD `i I fun i => do
      let hi := mkAppN (mkConst (density ++ `initialC_nonneg)) (prehistory.push i)
      mkLambdaFVars #[i] (← termWith [(`hSigma,x[23]!),(`hi,hi)]
        "fun s : ℕ ↦ mul_nonneg (And.left hSigma).le (hi s)")
    let hScalarC ← save `Source.scalarC_nonneg prehistory hScalarC
    let scalarProfile ← withLocalDeclD `i I fun i => do
      mkLambdaFVars #[i] (mkAppN (mkConst (density ++ `initial_profile)) (x.push i))
    let hK ← termWith [(`K,K)] "(ProperSpace.isCompact_closedBall _ _ : IsCompact K)"
    let buffer := mkAppN (mkConst `JanetCartan.PhysicalBackground.NativeSourceGeometry.measurement_buffer) original
    let hImage ← termWith [(`buffer,buffer),(`K,K),(`Kimage,Kimage)]
      "(Set.Subset.trans buffer Metric.ball_subset_closedBall : Kimage ⊆ K)"
    let T := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[x[38]!,x[40]!]
    let hT ← termWith [(`R0,x[38]!),(`stage,x[40]!),(`hReached,x[39]!),
        (`hS,mkAppN (mkConst (admission ++ `hS)) x[:32].toArray)]
      "(JanetCartan.one_le_currentCoefficientScale (by linarith [hS.trans hReached]) stage : 1 ≤ JanetCartan.currentCoefficientScale R0 stage)"
    let shift := mkApp (mkConst `JanetCartan.ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder) x[0]!
    let Ccoef ← save `Source.Ccoef prehistory
      (← termWith [(`Amap,Amap),(`Ascalar,scalarC),(`shift,shift)]
        "fun s : ℕ ↦ 1 + 2*Amap (s+shift) + ∑ i, Ascalar i (s+shift)") true
    let hCcoef ← save `Source.Ccoef_nonneg prehistory
      (← termWith [(`Ccoef,Ccoef),(`hAmap,hAmap),(`hScalar,hScalarC)]
        "(by intro s; exact add_nonneg (add_nonneg zero_le_one (mul_nonneg (by norm_num) (hAmap _))) (Finset.sum_nonneg fun i _ ↦ hScalar i _) : ∀ s, 0 ≤ Ccoef s)")
    let Cp := mkAppN (mkConst (originalCurrent ++ `Cpair)) x[:31].toArray
    let hCp := mkAppN (mkConst (originalCurrent ++ `nonnegative2)) x[:31].toArray
    let Craw ← save `Source.Craw prehistory
      (← termWith [(`Cp,Cp),(`Ccoef,Ccoef)] "fun s : ℕ ↦ Cp s*(1+Ccoef s)") true
    discard <| save `Source.Craw_nonneg prehistory
      (← termWith [(`Craw,Craw),(`hCp,hCp),(`hCcoef,hCcoef)]
        "(fun s ↦ mul_nonneg (hCp s) (add_nonneg zero_le_one (hCcoef s)) : ∀ s, 0 ≤ Craw s)")
    withLocalDeclD `rSource (mkConst ``Nat) fun rSource => do
      let hmType ← termWith [(`r,rSource),(`shift,shift),(`rMap,x[26]!)] "r+shift ≤ rMap"
      withLocalDeclD `hMapReserve hmType fun hm => do
        let hsType ← termWith [(`r,rSource),(`shift,shift),(`rScalar,x[33]!)] "r+shift ≤ rScalar"
        withLocalDeclD `hScalarReserve hsType fun hs => do
          let params := prehistory ++ #[rSource,hm,hs] ++ x[38:].toArray
          let hcoef ← mkAppM (root ++ `retained_source_profile_of_original_profiles)
            #[hK,hImage,Kin,hF,initial,hm,hs,hT,Amap,hAmap,scalarC,hScalarC,mapProfile,scalarProfile]
          let hcoef ← save `Source.coefficient_profile params hcoef
          let pairBound ← forallBoundedTelescope (← inferType pair) (some 3) fun w _ => do
            mkLambdaFVars w (.proj ``And 1 (mkAppN pair w))
          let hp := mkAppN (mkConst (root ++ `paired_source_profile_of_retained) [.zero])
            #[x[0]!,I,coefArgs[3]!,current `row,current `Q0,H,Cp,Ccoef,hCp,hCcoef,T,hT,rSource,shift,hcoef,pairBound]
          let hp ← save `Source.paired_profile params hp
          let common := #[x[0]!,I,coefArgs[3]!,current `row,current `Q0,Craw,T,rSource]
          discard <| save `Source.raw_profile params
            (mkAppN (mkConst (root ++ `raw_source_profile_of_pair) [.zero]) (common.push hp))
          discard <| save `Source.inverse_profile params
            (mkAppN (mkConst (root ++ `inverse_source_profile_of_pair) [.zero])
              (common ++ #[current `Q0_regular,hp]))
          let hPhysical := current `physical_bound
          let M := (← inferType hPhysical).appArg!
          discard <| save `Source.carrier_normal_tail params
            (mkAppN (mkConst (root ++ `carrier_tail_of_paired_source_profile) [.zero])
              #[x[0]!,I,coefArgs[3]!,current `image,current `carriers,
                mkAppN (mkConst (root ++ `Current.exterior)) original,M,hPhysical,Craw,T,rSource,
                current `source_regular,hp])
  logInfo "actual positive source pair: original map + SAME sigma-scaled positive initial profile applied; arbitrary retained source reserve, constants prehistory history, one unchanged Q0"

/-- The leading zero endpoint is the same measured carrier used by Q0, with
its original squared dyadic prefixLemma and exact Fourier factor. -/
elab "construct_original_mean_current_prefix" : command => liftTermElabM do
  let prefixLemma := `JanetCartan.PhysicalNormalInverse.OriginalPrefix.of_native
  forallBoundedTelescope (← getConstInfo prefixLemma).type (some 22) fun base _ => do
    unless base.size == 22 do throwError "positive current prefixLemma: expected original sample22"
    let n := (← inferType base[2]!).appArg!
    let capped := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
      #[base[0]!,base[2]!,base[1]!,base[21]!]
    let original := (#[n] ++ base[2:22].toArray).set! 20 capped
    let positive := mkAppN (mkConst (admission ++ `positive_inverse_exists)) original
    forallBoundedTelescope (← inferType positive) (some 18) fun tail _ => do
      let params := base ++ tail
      let actual := original ++ tail
      unless params.size == 40 && actual.size == 39 do
        throwError "positive current prefixLemma: expected same sampled40/admission39"
      let native ← bodyAt (admission ++ `positive_inverse_exists) actual
      unless native.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.all_densities 52 do
        throwError "positive current prefixLemma: changed actual all-density producer"
      let native ← bodyAt native.getAppFn.constName! native.getAppArgs
      unless native.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalCurrent.continuation 44 do
        throwError "positive current prefixLemma: expected original44 native positive application"
      let nativeArgs := native.getAppArgs
      let hNative := mkAppN (mkConst (root ++ `Current.native)) actual
      unless ← isDefEq (← inferType (mkAppN (mkConst (root ++ `Current.Vop)) actual))
          ((← whnf (← inferType native)).getAppArgs[0]!) do
        throwError "positive current prefixLemma: native carrier index changed"
      let applied := mkAppN (mkConst prefixLemma)
        (base ++ nativeArgs[21:44].toArray ++
          #[mkAppN (mkConst (root ++ `Current.Vop)) actual,hNative])
      discard <| save `Current.prefix_normal params applied
      let pair := mkAppN (mkConst (root ++ `Current.paired_spec)) actual
      let type ← inferType pair
      let some retained := type.find? (·.isAppOf `JanetCartan.ContinuumCommutator.retainedCoefficientProfile)
        | throwError "positive current prefix: retained finite index disappeared"
      let I := retained.getAppArgs[2]!
      let inst := retained.getAppArgs[3]!
      forallBoundedTelescope (← inferType applied) (some 1) fun ix _ => do
        forallBoundedTelescope (← inferType (mkAppN applied ix)) (some 3) fun cut _ => do
          unless ix.size == 1 && cut.size == 3 do
            throwError "positive current prefix: expected i,J,K,hK"
          let h0 := Expr.proj ``And 1 (mkAppN applied (ix ++ cut))
          let h0type ← whnf (← inferType h0)
          unless h0type.isAppOfArity ``Eq 3 do
            throwError "positive current prefix: lost endpoint identity: {h0type.getAppFn}"
          let lhs := h0type.getAppArgs[1]!
          let four := lhs.appArg!
          unless four.isAppOfArity ``HSMul.hSMul 6 do
            throwError "positive current prefix: original real four-factor changed"
          let realMean := four.getAppArgs[5]!
          unless realMean.isAppOf `JanetCartan.realOutputCompression do
            throwError "positive current prefix: original real compression changed"
          let p := params ++ cut
          let E0 ← save `Transport.leadingMean p (← mkLambdaFVars ix realMean.appArg!) true
          let h0 ← mkLambdaFVars ix h0
          let current (key : Name) := mkAppN (mkConst (root ++ `Current ++ key)) actual
          let common := #[n,I,inst,current `image,current `carriers,
            mkAppN (mkConst (root ++ `Current.exterior)) original,cut[1]!]
          discard <| save `Transport.leading_normal p
            (mkAppN (mkConst (root ++ `leading_normal_eq_normalized_mean) [.zero])
              (common ++ #[E0,h0]))
          withLocalDeclD `correctedMean (← inferType E0) fun E => do
            discard <| save `Transport.of_original_comparisons (p.push E)
              (mkAppN (mkConst (root ++ `corrected_transport_of_original_comparisons) [.zero])
                (common ++ #[E,E0,h0]))
  logInfo "SAME positive-current zero endpoint: actual OriginalPrefix.of_native on the literal native44 density/current application; no new Vop, exact original squared carrier prefixLemma"

/-- Close the image/exterior coefficient producer on the literal current c,
not on a newly selected coefficient family. -/
elab "construct_original_mean_auxiliary_profiles" : command => liftTermElabM do
  let profileInfo ← getConstInfo (root ++ `Source.paired_profile)
  forallBoundedTelescope profileInfo.type (some 48) fun x _ => do
    unless x.size == 48 do throwError "original auxiliary: expected exact source48"
    let static := x[:41].toArray
    let original := x[:21].toArray
    let actual := x[:33].toArray ++ x[41:47].toArray
    let current (key : Name) := mkAppN (mkConst (root ++ `Current ++ key)) actual
    let cutoff (key : Name) := mkAppN (mkConst (root ++ `Current ++ key)) original
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[x[0]!,x[1]!,x[20]!]
    let selected := original.set! 20 capped
    let field (key : Name) := mkAppN (mkConst (`JanetCartan.PhysicalSeed.SelectedBoundary ++ key)) selected
    let Gref := mkAppN (mkConst `JanetCartan.PhysicalBackground.NativeCoefficientProfiles.Gref) x[:23].toArray
    let radii := mkAppN (mkConst (root ++ `auxiliary_radius_geometry))
      #[field `rMeasure,field `hrMeasure,field `fact59]
    let orders := mkAppN (mkConst (root ++ `auxiliary_reserve)) #[x[0]!,x[26]!,x[38]!,x[39]!]
    let producer ← mkAppM `JanetCartan.PhysicalMean.exists_history_auxiliary_source_coefficients
      #[Gref,part radii 0,part radii 1,field `fact58,.proj ``And 1 (.proj ``And 1 radii),
        field `χcoeff,field `fact62,field `fact65,
        cutoff `measurement,cutoff `source,cutoff `exterior,
        cutoff `measurement_smooth,cutoff `source_smooth,cutoff `exterior_smooth,
        x[25]!,part orders 0,.proj ``And 1 orders,x[29]!]
    let producer ← save `Auxiliary.exists_profiles static producer
    let S ← save `Auxiliary.S static (← mkAppM ``Classical.choose #[producer]) true
    let spec ← mkAppM ``Classical.choose_spec #[producer]
    discard <| save `Auxiliary.hS static (.proj ``And 0 spec)
    let budgetExists := Expr.proj ``And 1 spec
    let Ccoef ← save `Auxiliary.Ccoef static (← mkAppM ``Classical.choose #[budgetExists]) true
    let full ← mkAppM ``Classical.choose_spec #[budgetExists]
    let nn ← save `Auxiliary.Ccoef_nonneg static (.proj ``And 0 full)
    discard <| save `Auxiliary.M static (mkApp Ccoef (mkNatLit 0)) true
    discard <| save `Auxiliary.M_nonneg static (mkApp nn (mkNatLit 0))
    let continuation := Expr.proj ``And 1 full
    let native ← bodyAt (admission ++ `positive_inverse_exists) actual
    unless native.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.all_densities 52 do
      throwError "original auxiliary: literal same-coefficient producer changed"
    let formula := mkAppN (mkConst `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.coefficient_formula)
      native.getAppArgs[:47].toArray
    withLocalDeclD `hAuxiliaryReached (← mkAppM ``LE.le #[S,x[41]!]) fun hAux => do
      let value := mkAppN continuation (#[x[41]!,hAux] ++ x[43:47].toArray ++ #[current `coefficient,formula])
      let params := x.push hAux
      discard <| save `Auxiliary.coefficient_smooth params (.proj ``And 0 value)
      discard <| save `Auxiliary.image_jets params (.proj ``And 0 (.proj ``And 1 value))
      discard <| save `Auxiliary.exterior_jets params (.proj ``And 1 (.proj ``And 1 value))
  logInfo "actual uncut auxiliary profiles: SAME current coefficient formula, original fixed masks/exterior, genuine physical-history producer; constants before history and only numeric threshold reach"

/-- A typed downstream consequence, explicitly conditional only on the real
row and the two original comparison producers; the actual current/raw inverse
hypotheses are already discharged. The parent must apply those remaining
producers before this becomes the complete E theorem. -/
elab "construct_original_mean_low_error_consumer" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (root ++ `Source.raw_profile)).type (some 48) fun x _ => do
    let actual := x[:33].toArray ++ x[41:47].toArray
    let original := x[:21].toArray
    let current (key : Name) := mkAppN (mkConst (root ++ `Current ++ key)) actual
    let fixed (key : Name) := mkAppN (mkConst (root ++ `Current ++ key)) original
    let pairType ← inferType (current `paired_spec)
    let some retained := pairType.find? (·.isAppOf `JanetCartan.ContinuumCommutator.retainedCoefficientProfile)
      | throwError "original low consumer: positive carrier index disappeared"
    let name := `JanetCartan.PhysicalMean.fixedSourceLinear_low_error
    let info ← getConstInfo name
    let applied := mkAppN (mkConst name (info.levelParams.map fun _ => .zero))
      #[x[0]!,retained.getAppArgs[2]!,retained.getAppArgs[3]!]
    forallBoundedTelescope (← inferType applied) (some 8) fun rawTypes _ => do
      let applied := mkAppN applied (rawTypes ++ #[current `coefficient,current `coefficient_smooth,
        fixed `measurement,fixed `source,fixed `exterior,fixed `measurement_smooth,
        fixed `source_smooth,fixed `exterior_smooth,current `carriers,fixed `gamma,
        fixed `gamma_pos,current `gap,current `source_regular])
      forallBoundedTelescope (← inferType applied) (some 8) fun row _ => do
        let applied := mkAppN applied row
        forallBoundedTelescope (← inferType applied) (some 1) fun q _ => do
          let applied := mkAppN applied (q.push x[38]!)
          forallBoundedTelescope (← inferType applied) (some 1) fun K _ => do
            let T := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[x[41]!,x[43]!]
            let Cq := mkAppN (mkConst (root ++ `Source.Craw)) (x[:38].toArray ++ q)
            let applied := mkAppN applied (K ++ #[T,fixed `Crow,Cq])
            forallBoundedTelescope (← inferType applied) (some 3) fun errors _ => do
              let applied := mkAppN applied (errors.push (current `row_bound))
              forallBoundedTelescope (← inferType applied) (some 6) fun compare _ => do
                let hp := mkAppN (mkConst (root ++ `Source.raw_profile)) (x ++ q ++ #[compare[5]!])
                let result := mkAppN applied (compare.push hp)
                discard <| save `Linear.low_error_of_original_row_comparisons
                  (x ++ rawTypes ++ row ++ q ++ K ++ errors ++ compare) result
  logInfo "actual current/raw part of low source error discharged; remaining exact row identity and transport/sampling producers are explicit, not an E bound"

end JanetCartan.PhysicalMean.OriginalMeanLinearProfilesTemplate
end
