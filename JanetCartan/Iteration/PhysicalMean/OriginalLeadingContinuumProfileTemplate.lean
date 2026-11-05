module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationColorMasks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PreparationIntegralBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparedSource.Sobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Envelope
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets
public import JanetCartan.Iteration.PhysicalMean.OriginalLeadingContinuum
public import JanetCartan.Iteration.PhysicalMean.OriginalLeadingContinuumTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalPeriodicBackground
public import JanetCartan.Iteration.PhysicalMean.OriginalWeightedHermitianProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveJets
import all JanetCartan.Iteration.PhysicalMean.OriginalParentCorrectedProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalWeightedHermitianProfiles
public meta import Lean

/-!
# Sharp profile of the complete original signed colored continuum

This leaf persists the concrete analytic producer for the transported-leading
minus corrected-continuum term in `new:eq:mean-source`. It retains the same
native event, full original outer square, genuine carrier, measurement, rows
and normalized original colors. No colored counting loss or analytic output
hypothesis is introduced. Its static44 `Ccomparison` is the sum of the actual
row costs. The checked native50 source profile retains the sharp coefficient
scale `h * T^(q-sourceOrder n)`; no `T ≤ R` relaxation occurs here.

The final identification with the literal selected leading comparison is a
separate consumer, so fixing an alias/value join cannot rerun these analytic
constructions. Every declaration below is checked at the default limits.
-/

public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-! ## PeriodicError -/
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate

private meta def retain (key : Name) (p : Array Expr) (proof : Expr)
    (data := false) (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← mkForallFVars p target
  let value ← mkLambdaFVars p proof
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "unclosed actual periodic leading field {key}"
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking exact periodic leading {key}"
  out.flush
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed exact periodic leading {key}"
  out.flush

run_meta do
  withWeightedParent fun p _ _ _ => do
    let some body := (← getConstInfo `JanetCartan.PhysicalMean.OriginalLeadingContinuum.weightedError).value? |
      throwError "missing actual signed weighted field"
    let field := (body.beta p).headBeta
    lambdaTelescope field fun w rhs => do
      unless w.size == 1 do throwError "changed original weighted pair field"
      let rhs := JanetCartan.PhysicalMean.OriginalWeightedHermitianProfilesTemplate.rootLets rhs
      unless rhs.isAppOf ``HSMul.hSMul do throwError "original outer scalar weight missing"
      retain `physical p (← mkLambdaFVars w rhs.appArg!) true

run_meta do
  withWeightedParent fun p a _ _ => do
    let H := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.physical) p
    let periodic := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalPeriodicBackground.periodicH) #[a[0]!,H]
    retain `periodic p periodic true

run_meta do
  withWeightedParent fun p a g d => do
    let H := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.physical) p
    let some body := (← getConstInfo `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.physical).value? | throwError "missing signed factor"
    let Hbody := (body.beta p).headBeta
    let pair := (← inferType H).bindingDomain!
    let M ← withLocalDeclNoLocalInstanceUpdate `w .default pair fun w => do
      let raw := (Hbody.beta #[w]).headBeta
      mkLambdaFVars #[w] raw.appArg!
    let physical := (← inferType d[0]!).bindingDomain!
    let point := mkConst `JanetCartan.SeparatedSampling.Point
    let factor ← withLocalDeclNoLocalInstanceUpdate `x .default physical fun x =>
      withLocalDeclNoLocalInstanceUpdate `z .default point fun z => do
        let w ← mkAppM ``Prod.mk #[x,z]
        mkLambdaFVars #[x,z] (← mkEqRefl (mkApp H w))
    let ns := `JanetCartan.PhysicalMean.OriginalPeriodicBackground
    let support := mkAppN (mkConst (ns ++ `weighted_support_of_factor))
      #[a[0]!,g[3]!,g[6]!,H,d[0]!,M,d[2]!,factor]
    let some xbody := (← getConstInfo g[3]!.getAppFn.constName!).value? | throwError "missing original measurement compact"
    let X := (xbody.beta g[3]!.getAppArgs).headBeta
    unless X.isAppOf ``Metric.closedBall do throwError "changed original measurement support ball"
    let weighted := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuum.weightedError) p
    let gap := mkAppN (mkConst (ns ++ `support_gap_of_closedBall)) #[a[0]!,X.appArg!,weighted,support]
    retain `support p gap

private meta def checkPeriodicProfile (mode : Nat) : MetaM Unit := do
  withWeightedParent fun p a g d => do
    let ns := `JanetCartan.PhysicalMean.OriginalPeriodicBackground
    let H := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.physical) p
    let support := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.support) p
    let base := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
    let gap := mkAppN (mkConst (base ++ `X_cell_gap)) p[:51].toArray
    let some xbody := (← getConstInfo g[3]!.getAppFn.constName!).value? | throwError "missing original measurement compact"
    let X := (xbody.beta g[3]!.getAppArgs).headBeta
    let profile := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuum.weighted_error_profile) p
    let (key,proof) ← if mode == 0 then
        pure (`smooth,mkAppN (mkConst (ns ++ `weighted_periodic_smooth))
          #[a[0]!,X.appArg!,g[6]!,H,support,.proj ``And 0 profile,gap])
      else if mode == 1 then do
        let D := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuum.D) (p[:44].toArray.push p[50]!)
        let cost ← withLocalDeclNoLocalInstanceUpdate `j .default (mkConst ``Nat) fun j => do
          let two ← mkNumeral (mkConst ``Real) 2
          let twice ← mkAppM ``HMul.hMul #[two,mkApp D j]
          mkLambdaFVars #[j] (← mkAppM ``HMul.hMul #[a[38]!,twice])
        pure (`jets,mkAppN (mkConst (ns ++ `weighted_periodic_jets))
          #[a[0]!,X.appArg!,g[6]!,H,support,gap,cost,d[5]!,d[6]!,.proj ``And 1 profile])
      else
        pure (`on_cell,mkAppN (mkConst (ns ++ `weighted_periodic_eq))
          #[a[0]!,X.appArg!,g[6]!,H,support,gap])
    let raw := mkAppN (mkConst (ns ++ `periodicH)) #[a[0]!,H]
    let named := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.periodic) p
    let target := (← inferType proof).replace fun e => if e == raw then some named else none
    retain key p proof false (some target)

run_meta checkPeriodicProfile 0
run_meta checkPeriodicProfile 1
run_meta checkPeriodicProfile 2


/-! ## RateMesh -/
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate

/-- The genuine colored inverse frequency is smaller than the original mesh;
the static radial factor is only bounded below, never replaced by a new rate. -/
theorem radial_rate_le_original_mesh {Rinit radial : ℝ}
    (hR : 2 ≤ Rinit) (hradial : 1 ≤ radial) (stage : ℕ) :
    (radial * historyScale Rinit growthExponent stage ^ carrierExponent)⁻¹ ≤
      historyScale Rinit growthExponent stage ^ (-separationExponent) := by
  have hRone : 1 ≤ Rinit := (by norm_num : (1 : ℝ) ≤ 2).trans hR
  have hscale : 1 ≤ historyScale Rinit growthExponent stage :=
    hRone.trans (le_historyScale hRone stage)
  have hrate := (PhysicalPrimary.OriginalCorrectedWaveJets.radial_rate_bounds
    hRone hradial (le_refl radial) stage).2.2.1
  apply hrate.trans
  rw [← Real.rpow_neg (zero_le_one.trans hscale)]
  exact Real.rpow_le_rpow_of_exponent_le hscale
    (by norm_num [carrierExponent,separationExponent])

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate

open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
run_meta do
  withWeightedParent fun p a g _ => do
    let outer := g[7]!.getAppArgs
    unless outer.size == 23 do throwError "changed original outer weight23"
    let group ← mkAppM ``Prod.mk #[p[50]!,p[51]!]
    let hradial := mkAppN (mkConst
      `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.radial_ge_one)
      (outer[:22].toArray.push group)
    let ht ← inferType hradial
    unless ht.isAppOfArity ``LE.le 4 do throwError "changed original radial lower bound"
    let radial := ht.getAppArgs[3]!
    unless a[42]!.isAppOfArity
        `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le 3 do
      throwError "changed actual coefficient scale proof"
    let hR := a[42]!.getAppArgs[1]!
    let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.radial_rate_le_original_mesh)
      #[p[44]!,radial,hR,hradial,p[46]!]
    let target ← inferType proof
    unless ← isDefEq target.getAppArgs[2]! a[38]! do
      throwError "radial bound changed original tau"
    let type ← mkForallFVars p target
    let value ← mkLambdaFVars p proof
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "unclosed actual original mesh comparison"
    let out ← IO.getStdout
    out.putStrLn "kernel checking original radial rate <= original mesh"
    out.flush
    addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Rate.to_mesh,levelParams := [],type,value}) (forceExpose := true)
    out.putStrLn "kernel passed original radial rate <= original mesh"
    out.flush


/-! ## ColoredContinuum -/
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate
open ContinuumRow CurrentMean SeparatedSampling LatticeQuadrature
open Sampling.ColoredNormalComparison Sampling.BackgroundQuadrature

private theorem weighted_carrier_lift_smooth {n p : ℕ}
    (χ : CarrierParameter → ℝ)
    (H : (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hH : ∀ c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      χ (carrierSamplingEquiv.symm w.2)^2 • H c (torusQuotient w.1,w.2))) (c) :
    ContDiff ℝ ∞ (fun w : Euclidean n × CarrierParameter ↦
      χ w.2^2 • H c (torusQuotient w.1,carrierSamplingEquiv w.2)) := by
  have he : ContDiff ℝ ∞ carrierSamplingEquiv :=
    carrierSamplingLinearEquiv.toContinuousLinearEquiv.contDiff
  simpa only [Function.comp_def,carrierSamplingEquiv.symm_apply_apply] using
    (hH c).comp (contDiff_fst.prodMk (he.comp contDiff_snd))

private theorem continuous_of_joint_periodic_lift {n : ℕ}
    {f : Torus n × CarrierParameter → Euclidean n}
    (hf : Continuous (fun w : Euclidean n × CarrierParameter ↦
      f (torusQuotient w.1,w.2))) : Continuous f := by
  have hquot : IsOpenQuotientMap (@torusQuotient n) :=
    (IsOpenQuotientMap.piMap (fun _ : Fin n ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  exact (hquot.prodMap (.id : IsOpenQuotientMap (@id CarrierParameter))).isQuotientMap.continuous_iff.mpr hf

/-- The literal original colored continuum, using the normalized original
support partition, has no cost counting colors. Only the same compact
carrier mass and the weighted joint jets enter (new:eq:mean-source). -/
theorem original_colored_continuum_profile
    {n p : ℕ} {κ : ℝ → ℝ} (hκc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    (hp : 0 < p) (χ : CarrierParameter → ℝ) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) {B P h : ℝ}
    (hpatch : PatchBounds (fun z : Point ↦ χ (carrierSamplingEquiv.symm z)^2) B P)
    (hh : 0 < h) (hh1 : h ≤ 1)
    (H : (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hH : ∀ c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      χ (carrierSamplingEquiv.symm w.2)^2 • H c (torusQuotient w.1,w.2)))
    (s : ℕ) (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j)
    (hjet : ∀ c j, j ≤ s → ∀ x ∈ fundamentalCell n, ∀ z : Point,
      ‖iteratedFDeriv ℝ j (fun w : Euclidean n × Point ↦
        χ (carrierSamplingEquiv.symm w.2)^2 • H c (torusQuotient w.1,w.2)) (x,z)‖ ≤ A j) :
    let g : Torus n → Euclidean n := fun x ↦ ∑ c,
      ∫ z : Point, coloredBlockMask p (integerCube (blockCutoff p B h))
        (convolvedBoxWindow κ p) h c z •
          (χ (carrierSamplingEquiv.symm z)^2 • H c (x,z))
    IsSmoothPeriodic g ∧ periodicSobolevNorm s g ≤
      sobolevPeriodicJetConstant n s * (s+1 : ℕ) *
        ((∑ j ∈ Finset.range (s+1), A j) * (volume.prod volume).real (tsupport χ)) := by
  classical
  let mask := preparationCarrierColorMask p B (convolvedBoxWindow κ p) h χ
  let f : (Fin 3 → Fin (p+1)) → Torus n × CarrierParameter → Euclidean n :=
    fun c w ↦ χ w.2^2 • H c (w.1,carrierSamplingEquiv w.2)
  have hm : ∀ c, Measurable (mask c) :=
    measurable_preparationCarrierColorMask hκc hκ p B h hχ.measurable
  have hm0 : ∀ c z, 0 ≤ mask c z :=
    preparationCarrierColorMask_nonneg B h (convolvedBoxWindow_nonneg hκ0 p) χ
  have hm1 : ∀ z, ∑ c, mask c z = 1 :=
    sum_preparationCarrierColorMask (hκ.continuous.integrable_of_hasCompactSupport hκc)
      hκint hκ0 hκsupp hp hpatch hh hh1
  have hfs : ∀ c, ContDiff ℝ ∞ (fun w : Euclidean n × CarrierParameter ↦
      f c (torusQuotient w.1,w.2)) := weighted_carrier_lift_smooth χ H hH
  have hfc : ∀ c, Continuous (f c) :=
    fun c ↦ continuous_of_joint_periodic_lift (hfs c).continuous
  have hz : ∀ c x z, z ∉ tsupport χ → f c (x,z) = 0 := by
    intro c x z hz
    simp only [f,image_eq_zero_of_notMem_tsupport hz,zero_pow (by decide : 2 ≠ 0),zero_smul]
  have hmask1 : ∀ c z, mask c z ≤ 1 := by
    intro c z
    exact (Finset.single_le_sum (fun a _ ↦ hm0 a z) (Finset.mem_univ c)).trans_eq (hm1 z)
  have hi (c) (x : Torus n) : Integrable (fun z ↦ mask c z • f c (x,z)) (volume.prod volume) :=
    integrable_preparationMaskedSection (mask c) (hm c) (hm0 c) (hmask1 c) (f c) (hfc c) hχc (hz c) x
  have he : (fun x : Torus n ↦ ∑ c,
      ∫ z : Point, coloredBlockMask p (integerCube (blockCutoff p B h))
        (convolvedBoxWindow κ p) h c z •
          (χ (carrierSamplingEquiv.symm z)^2 • H c (x,z))) =
      fun x ↦ ∫ z, ∑ c, mask c z • f c (x,z) ∂(volume.prod volume) := by
    funext x
    rw [integral_finsetSum _ (fun c _ ↦ hi c x)]
    apply Finset.sum_congr rfl
    intro c _
    rw [← integral_carrierSamplingEquiv]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [f,carrierSamplingEquiv.symm_apply_apply,smul_smul,mask,
      preparationCarrierColorMask_mul_sq]
  dsimp only
  rw [he]
  refine ⟨isSmoothPeriodic_preparationColoredIntegral mask hm hm0 hm1 f hfc hfs hχc hz, ?_⟩
  apply periodicSobolevNorm_preparationColoredIntegral_le_cNorm mask hm hm0 hm1 f hfc hfs hχc hz s
    (Finset.sum_nonneg fun j _ ↦ hA j)
  intro c z _
  apply cNorm_le_sum_of_bounds (fun j _ ↦ hA j)
  intro j hj x hx
  simpa only [f,carrierSamplingEquiv.symm_apply_apply] using
    (RawPrimary.AmplitudeGrades.norm_iteratedFDeriv_physical_slice_le isOpen_univ
      (hH c).contDiffOn (mem_univ (x,carrierSamplingEquiv z)) j).trans
        (hjet c j hj x hx (carrierSamplingEquiv z))

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate


/-! ## ActualColoredProfile -/
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate

private theorem positive_scale_nonneg {T : ℝ} (hT : 1 ≤ T) : 0 ≤ T := zero_le_one.trans hT

private theorem scaled_leading_cost_nonneg (h T : ℝ) (r : ℕ) (D : ℕ → ℝ)
    (hh : 0 ≤ h) (hT : 0 ≤ T) (hD : ∀ j, 0 ≤ D j) :
    ∀ j, 0 ≤ h*(2*D j)*T^(j-r) := by
  intro j
  exact mul_nonneg (mul_nonneg hh (mul_nonneg (by norm_num) (hD j))) (pow_nonneg hT _)

private theorem rate_scaled_leading_jet_le {v τ h D T : ℝ} (j r : ℕ)
    (hτ : τ ≤ h) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hv : v ≤ τ*(2*D)*T^(j-r)) : v ≤ h*(2*D)*T^(j-r) :=
  hv.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hτ (mul_nonneg (by norm_num) hD)) (pow_nonneg hT _))

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate
open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate

private meta def retainColored (key : Name) (p : Array Expr) (term target : Expr) (data := false) : MetaM Unit := do
  let type ← mkForallFVars p target
  let value ← mkLambdaFVars p term
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "unclosed actual colored continuum {key}"
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking exact original colored continuum {key}"
  out.flush
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Row ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed exact original colored continuum {key}"
  out.flush

run_meta do
  withWeightedParent fun p a g d => do
    let args := p[:51].toArray
    let fixed := p[:44].toArray.push p[50]!
    let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
    let oa := g[7]!.getAppArgs
    unless oa.size == 23 do throwError "changed original outer-weight input23"
    let static := oa[:22].toArray
    let χ := mkAppN (mkConst (outer ++ `χ)) oa
    let hχsmooth := mkAppN (mkConst (outer ++ `χ_smooth)) oa
    let hχ ← mkAppM ``ContDiff.continuous #[hχsmooth]
    let hχc := mkAppN (mkConst (outer ++ `χ_compact)) oa
    let B := mkAppN (mkConst (outer ++ `B)) static
    let hpatch := mkAppN (mkConst (outer ++ `patchBounds)) oa
    let hTwo := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS) p[:44].toArray
    let facts ← mkAppM `JanetCartan.PhysicalMean.OriginalPeriodicBackground.original_scale_facts #[hTwo,p[45]!,p[46]!]
    let hh := Expr.proj ``And 0 (.proj ``And 1 facts)
    let hh1 := Expr.proj ``And 1 (.proj ``And 1 facts)
    let hRate := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Rate.to_mesh) p
    let rt ← inferType hRate
    unless rt.isAppOfArity ``LE.le 4 do throwError "lost original true-rate/mesh inequality"
    let h := rt.getAppArgs[3]!
    if (h.find? (· == p[51]!)).isSome then throwError "original mesh retained color"
    let hh0 ← mkAppM ``le_of_lt #[hh]
    let hT0 := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.positive_scale_nonneg) #[d[5]!,d[7]!]
    let D := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuum.D) fixed
    let hD := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuum.D_nonneg) fixed
    let hA := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.scaled_leading_cost_nonneg)
      #[h,d[5]!,d[6]!,D,hh0,hT0,hD]
    let A ← forallBoundedTelescope (← inferType hA) (some 1) fun j result => do
      unless j.size == 1 && result.isAppOfArity ``LE.le 4 do throwError "changed scaled cost shape"
      mkLambdaFVars j result.getAppArgs[3]!
    let H := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.periodic) args
    let hH ← mkLambdaFVars #[p[51]!] (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.smooth) p)
    withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
      let jets := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Periodic.jets) p
      let hjet ← forallBoundedTelescope (← inferType jets) (some 1) fun js rest => do
        unless js.size == 1 do throwError "changed actual periodic jet order"
        let hjType ← mkAppM ``LE.le #[js[0]!,q]
        withLocalDeclNoLocalInstanceUpdate `hj .default hjType fun hj => do
          forallBoundedTelescope rest (some 3) fun points _ => do
            unless points.size == 3 do throwError "changed actual periodic jet point"
            let bound := mkAppN jets (js ++ points)
            let bt ← inferType bound
            unless bt.isAppOfArity ``LE.le 4 do throwError "lost actual signed jet inequality"
            let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.rate_scaled_leading_jet_le)
              #[bt.getAppArgs[2]!,rt.getAppArgs[2]!,h,mkApp D js[0]!,d[5]!,js[0]!,d[6]!,hRate,mkApp hD js[0]!,hT0,bound]
            mkLambdaFVars (#[p[51]!] ++ js ++ #[hj] ++ points) proof
      let window := `JanetCartan.PhysicalSampling.OriginalWindow
      let one ← mkNumeral (mkConst ``Real) 1
      let generic := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.original_colored_continuum_profile
      discard <| getConstInfo generic
      let proof := mkAppN (mkConst generic)
        #[a[0]!,static[2]!,mkConst (window ++ `mollifier),mkConst (window ++ `compact),mkConst (window ++ `smooth),
          mkConst (window ++ `mass),mkConst (window ++ `nonneg),mkConst (window ++ `support),p[43]!,χ,hχ,hχc,
          B,one,h,hpatch,hh,hh1,H,hH,q,A,hA,hjet]
      let target := JanetCartan.PhysicalMean.OriginalWeightedHermitianProfilesTemplate.rootLets (← inferType proof)
      unless target.isAppOfArity ``And 2 do throwError "lost exact colored smoothness/profile pair"
      let smooth := target.getAppArgs[0]!
      unless smooth.isAppOf `JanetCartan.IsSmoothPeriodic do throwError "lost actual colored smoothness"
      let field := smooth.appArg!
      retainColored `continuum args field (← inferType field) true
      let named := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Row.continuum) args
      let namedTarget := target.replace fun e => if e == field then some named else none
      retainColored `profile (args.push q) proof namedTarget


/-! ## IntegralBudget -/
open Set MeasureTheory
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate
open ContinuumRow CurrentMean

/-- Static row cost for the exact signed colored integral. -/
noncomputable def leadingContinuumRowBudget (n : ℕ) (χ : CarrierParameter → ℝ)
    (D : ℕ → ℝ) (q : ℕ) : ℝ :=
  sobolevPeriodicJetConstant n q * (q+1 : ℕ) *
    ((∑ j ∈ Finset.range (q+1), 2*D j) * (volume.prod volume).real (tsupport χ))

private theorem leadingContinuumRowBudget_nonneg (n : ℕ) (χ : CarrierParameter → ℝ)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) (q : ℕ) :
    0 ≤ leadingContinuumRowBudget n χ D q := by
  unfold leadingContinuumRowBudget
  exact mul_nonneg (mul_nonneg (zero_le_one.trans (one_le_sobolevPeriodicJetConstant n q)) (by positivity))
    (mul_nonneg (Finset.sum_nonneg (fun j _ ↦ mul_nonneg (by norm_num) (hD j))) (by positivity))

private theorem leading_source_reserve (n : ℕ) :
    RevisedScales.sourceOrder n ≤ RawPrimary.SliceBounds.rawSliceParameterOrder n :=
  (Nat.le_add_right _ 1).trans (OriginalPeriodicBackground.sampling_order_one_reserve n)

/-- Keep the coefficient scale T; no T≤R relaxation occurs here. -/
private theorem sharp_leading_continuum_row_budget
    (n q r s₀ : ℕ) (χ : CarrierParameter → ℝ) (hr : s₀ ≤ r)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) (T h : ℝ) (hT : 1 ≤ T) (hh : 0 ≤ h) :
    sobolevPeriodicJetConstant n q * (q+1 : ℕ) *
      ((∑ j ∈ Finset.range (q+1), h*(2*D j)*T^(j-r)) *
        (volume.prod volume).real (tsupport χ)) ≤
      leadingContinuumRowBudget n χ D q * h * T^(q-s₀) := by
  have hsum : (∑ j ∈ Finset.range (q+1), h*(2*D j)*T^(j-r)) ≤
      h*(∑ j ∈ Finset.range (q+1), 2*D j)*T^(q-s₀) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (q+1), h*(2*D j)*T^(q-s₀) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hT (show j-r ≤ q-s₀ by omega))
          (mul_nonneg hh (mul_nonneg (by norm_num) (hD j)))
      _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]
  calc
    _ ≤ sobolevPeriodicJetConstant n q * (q+1 : ℕ) *
        ((h*(∑ j ∈ Finset.range (q+1), 2*D j)*T^(q-s₀)) *
          (volume.prod volume).real (tsupport χ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum (by positivity))
        (mul_nonneg (zero_le_one.trans (one_le_sobolevPeriodicJetConstant n q)) (by positivity))
    _ = _ := by unfold leadingContinuumRowBudget; ring

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate

open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
private meta def retainIntegralBudget (key : Name) (p : Array Expr)
    (term target : Expr) (data := false) : MetaM Unit := do
  let type ← mkForallFVars p target
  let value ← mkLambdaFVars p term
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "unclosed original integral budget {key}"
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking actual sharp integral budget {key}"
  out.flush
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.RowBudget ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed actual sharp integral budget {key}"
  out.flush

private meta def checkIntegralBudget (mode : Nat) : MetaM Unit := do
  withWeightedParent fun p a g d => do
    let fixed := p[:44].toArray.push p[50]!
    let χ := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalOuterWeights.χ) g[7]!.getAppArgs
    let D := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuum.D) fixed
    let hD := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuum.D_nonneg) fixed
    let rawCost := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.leadingContinuumRowBudget) #[a[0]!,χ,D]
    let namedCost := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.RowBudget.CRow) fixed
    if mode == 0 then
      retainIntegralBudget `CRow fixed rawCost (← inferType rawCost) true
    else if mode == 1 then
      let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.leadingContinuumRowBudget_nonneg) #[a[0]!,χ,D,hD]
      let target := (← inferType proof).replace fun e => if e == rawCost then some namedCost else none
      retainIntegralBudget `CRow_nonneg fixed proof target
    else
      let hTwo := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS) p[:44].toArray
      let facts ← mkAppM `JanetCartan.PhysicalMean.OriginalPeriodicBackground.original_scale_facts #[hTwo,p[45]!,p[46]!]
      let hh := Expr.proj ``And 0 (.proj ``And 1 facts)
      let h := (← inferType hh).getAppArgs[3]!
      let hh0 ← mkAppM ``le_of_lt #[hh]
      let s₀ := mkApp (mkConst `JanetCartan.RevisedScales.sourceOrder) a[0]!
      let hr := mkApp (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.leading_source_reserve) a[0]!
      unless ← isDefEq (← inferType hr).getAppArgs[3]! d[6]! do
        throwError "changed actual raw parameter reserve"
      withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
        let raw := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Row.profile) (p[:51].toArray.push q)
        let estimate := Expr.proj ``And 1 raw
        let sharp := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.sharp_leading_continuum_row_budget)
          #[a[0]!,q,d[6]!,s₀,χ,hr,D,hD,d[5]!,h,d[7]!,hh0]
        let proof ← mkAppM ``le_trans #[estimate,sharp]
        let target := (← inferType proof).replace fun e => if e == rawCost then some namedCost else none
        retainIntegralBudget `sharp (p[:51].toArray.push q) proof target

run_meta checkIntegralBudget 0
run_meta checkIntegralBudget 1
run_meta checkIntegralBudget 2


/-! ## RowSum -/
open Set MeasureTheory
namespace JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate

private theorem leading_sobolev_add {n : ℕ} {f g : Torus n → Euclidean n}
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) (q : ℕ) :
    periodicSobolevNorm q (f+g) ≤ periodicSobolevNorm q f + periodicSobolevNorm q g := by
  have hfLp : MemLp f 2 := hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hgLp : MemLp g 2 := hg.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have hfg : IsSmoothPeriodic (f+g) := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  rw [← hf.gradeNorm_toLp q hfLp,← hg.gradeNorm_toLp q hgLp,
    ← hfg.gradeNorm_toLp q (hfLp.add hgLp),MemLp.toLp_add]
  exact ResponseTransfer.gradeNorm_add_le (periodicSobolevScale n (Euclidean n))
    (hf.toLp_mem_periodicSobolevLevel q hfLp) (hg.toLp_mem_periodicSobolevLevel q hgLp)

private theorem leading_sobolev_zero (n q : ℕ) :
    periodicSobolevNorm q (0 : Torus n → Euclidean n) = 0 := by
  have hz : IsSmoothPeriodic (0 : Torus n → Euclidean n) := ⟨continuous_const,contDiff_const⟩
  have hlp : MemLp (0 : Torus n → Euclidean n) 2 := MemLp.zero
  rw [← hz.gradeNorm_toLp q hlp,hlp.toLp_zero]
  rw [(periodicSobolevScale n (Euclidean n)).gradeNorm_eq
    (((periodicSobolevScale n (Euclidean n)).level q).zero_mem)]
  exact map_zero _

private theorem original_row_sum_sobolev (n : ℕ) (I : Type) (s : Finset I)
    (f : I → Torus n → Euclidean n) (hf : ∀ i ∈ s, IsSmoothPeriodic (f i)) (q : ℕ) :
    IsSmoothPeriodic (fun x ↦ ∑ i ∈ s, f i x) ∧
      periodicSobolevNorm q (fun x ↦ ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, periodicSobolevNorm q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : IsSmoothPeriodic (0 : Torus n → Euclidean n) := ⟨continuous_const,contDiff_const⟩
    simpa only [Finset.sum_empty,Pi.zero_def] using And.intro hz (leading_sobolev_zero n q).le
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    obtain ⟨hs,hb⟩ := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    have hsum : IsSmoothPeriodic (f i + (fun x ↦ ∑ j ∈ s, f j x)) :=
      ⟨hfi.1.add hs.1,hfi.2.add hs.2⟩
    have hbound := (leading_sobolev_add hfi hs q).trans (add_le_add le_rfl hb)
    simpa only [Finset.sum_insert hi,Pi.add_def] using And.intro hsum hbound

noncomputable def leadingTotalCost (I : Type) [Fintype I] (C : I → ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ i, C i q

noncomputable def leadingTotalField (n : ℕ) (I : Type) [Fintype I]
    (f : I → Torus n → Euclidean n) : Torus n → Euclidean n := fun x ↦ ∑ i, f i x

private theorem leadingTotalCost_nonneg (I : Type) [Fintype I]
    (C : I → ℕ → ℝ) (hC : ∀ i q, 0 ≤ C i q) (q : ℕ) : 0 ≤ leadingTotalCost I C q :=
  Finset.sum_nonneg (fun i _ ↦ hC i q)

private theorem leadingTotalField_smooth (n : ℕ) (I : Type) [Fintype I]
    (f : I → Torus n → Euclidean n) (hf : ∀ i, IsSmoothPeriodic (f i)) :
    IsSmoothPeriodic (leadingTotalField n I f) :=
  (original_row_sum_sobolev n I Finset.univ f (fun i _ ↦ hf i) 0).1

private theorem leadingTotalField_sharp (n : ℕ) (I : Type) [Fintype I]
    (f : I → Torus n → Euclidean n) (C : I → ℕ → ℝ) (T h : ℝ) (s₀ : ℕ)
    (hf : ∀ i, IsSmoothPeriodic (f i))
    (hbound : ∀ i (q : ℕ), periodicSobolevNorm q (f i) ≤ C i q*h*T^(q-s₀)) (q : ℕ) :
    periodicSobolevNorm q (leadingTotalField n I f) ≤ leadingTotalCost I C q*h*T^(q-s₀) := by
  calc
    _ ≤ ∑ i, periodicSobolevNorm q (f i) :=
      (original_row_sum_sobolev n I Finset.univ f (fun i _ ↦ hf i) q).2
    _ ≤ ∑ i, C i q*h*T^(q-s₀) := Finset.sum_le_sum (fun i _ ↦ hbound i q)
    _ = _ := by unfold leadingTotalCost; rw [← Finset.sum_mul,← Finset.sum_mul]

end JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate

open Lean Meta
open JanetCartan.PhysicalMean.OriginalLeadingContinuumTemplate
private meta def retainActualRowSum (key : Name) (p : Array Expr)
    (term target : Expr) (data := false) : MetaM Unit := do
  let type ← mkForallFVars p target
  let value ← mkLambdaFVars p term
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "unclosed original leading row sum {key}"
  let name := `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile ++ key
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let out ← IO.getStdout
  out.putStrLn s!"kernel checking actual whole-row leading profile {key}"
  out.flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  out.putStrLn s!"kernel passed actual whole-row leading profile {key}"
  out.flush

private meta def checkActualRowSum (mode : Nat) : MetaM Unit := do
  withWeightedParent fun p a _ d => do
    let I ← inferType p[50]!
    let fi ← synthInstance (mkApp (mkConst ``Fintype [.zero]) I)
    let C := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.RowBudget.CRow) p[:44].toArray
    let hC := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.RowBudget.CRow_nonneg) p[:44].toArray
    let rawCost := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.leadingTotalCost) #[I,fi,C]
    let namedCost := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Ccomparison) p[:44].toArray
    let f := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Row.continuum) p[:50].toArray
    let rawField := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.leadingTotalField) #[a[0]!,I,fi,f]
    let namedField := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.signedContinuum) p[:50].toArray
    if mode == 0 then
      retainActualRowSum `Ccomparison p[:44].toArray rawCost (← inferType rawCost) true
    else if mode == 1 then
      let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.leadingTotalCost_nonneg) #[I,fi,C,hC]
      let target := (← inferType proof).replace fun e => if e == rawCost then some namedCost else none
      retainActualRowSum `Ccomparison_nonneg p[:44].toArray proof target
    else if mode == 2 then
      retainActualRowSum `signedContinuum p[:50].toArray rawField (← inferType rawField) true
    else
      let rowSmooth := Expr.proj ``And 0 (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Row.profile) (p[:51].toArray.push (mkNatLit 0)))
      let hSmooth ← mkLambdaFVars #[p[50]!] rowSmooth
      if mode == 3 then
        let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.leadingTotalField_smooth) #[a[0]!,I,fi,f,hSmooth]
        let target := (← inferType proof).replace fun e => if e == rawField then some namedField else none
        retainActualRowSum `signedContinuum_smooth p[:50].toArray proof target
      else
        let hTwo := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS) p[:44].toArray
        let facts ← mkAppM `JanetCartan.PhysicalMean.OriginalPeriodicBackground.original_scale_facts #[hTwo,p[45]!,p[46]!]
        let hh := Expr.proj ``And 0 (.proj ``And 1 facts)
        let h := (← inferType hh).getAppArgs[3]!
        let s₀ := mkApp (mkConst `JanetCartan.RevisedScales.sourceOrder) a[0]!
        let hBounds := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.RowBudget.sharp) p[:50].toArray
        let proof := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalLeadingContinuumProfileTemplate.leadingTotalField_sharp)
          #[a[0]!,I,fi,f,C,d[5]!,h,s₀,hSmooth,hBounds]
        let target := (← inferType proof).replace fun e =>
          if e == rawCost then some namedCost else if e == rawField then some namedField else none
        retainActualRowSum `signedContinuum_source_profile p[:50].toArray proof target

run_meta checkActualRowSum 0
run_meta checkActualRowSum 1
run_meta checkActualRowSum 2
run_meta checkActualRowSum 3
run_meta checkActualRowSum 4

end
