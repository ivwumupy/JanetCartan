module

public import JanetCartan.Iteration.PhysicalMean.CanonicalLowQuadratic
public import JanetCartan.Iteration.PhysicalSampling.OriginalCoefficientTesterKernel
public import JanetCartan.Iteration.PhysicalPrimary.OriginalComparisonResponseBase
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalSampledMomentGeometry
import all JanetCartan.Iteration.PhysicalMean.OriginalSampledMomentGeometry
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActualTemplate
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverSourceBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.MeanCorrectedSource.ObservedCore.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.Identification
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputDilation.Kernel
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# Original geometry for the native mean quadratic application

The numerical consumers are `fixedSourceQuadratic_low_bound` and
`fixedSourceQuadratic_source_profile`. Their scalar tester uses the SAME
selected coefficient cutoff as both original scalar operators. The compact
contains the original whole-derivative observation cutoff; it neither recuts
that physical wave nor changes its source (`app:ch_mean_pairs:eq:block-bilinear`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
open Set Metric AmplitudeBound PeriodicLocalL2

private theorem coefficient_test_support_cell {n : ℕ} {μ : ℝ}
    {χ : Euclidean n → ℝ} (hμ : 0 < μ) (hcell : 6 * μ < 1/2)
    (hχ : tsupport χ ⊆ ball 0 (5 * μ)) : tsupport χ ⊆ halfOpenCell n := by
  intro x hx i
  have hxnorm : ‖x‖ < 5 * μ := mem_ball_zero_iff.mp (hχ hx)
  have hi := (PiLp.norm_apply_le x i).trans_lt hxnorm
  rw [Real.norm_eq_abs] at hi
  have hi' := abs_lt.mp hi
  constructor <;> linarith

private theorem source_box_pos {μ : ℝ} (hμ : 0 < μ) : 0 < 4 * μ :=
  mul_pos (by norm_num) hμ

private theorem source_box_coordinates {n : ℕ} {μ : ℝ} :
    ∀ x ∈ closedBall (0 : Euclidean n) (4 * μ), ∀ i, |x i| ≤ 4 * μ := by
  intro x hx i
  exact (PiLp.norm_apply_le x i).trans (mem_closedBall_zero_iff.mp hx)

private theorem coefficient_test_plateau {n : ℕ} {χ : Euclidean n → ℝ}
    {K : Set (Euclidean n)} (h : K ⊆ interior {x | χ x = 1}) :
    ∀ x ∈ K, χ x = 1 := by
  intro x hx
  exact interior_subset (s := {y | χ y = 1}) (h hx)

open ResponseSmoothParameters ResponseSourceExtension PrimarySourceAdmission CorrectedAtoms
  FixedDomainInverse LocalSobolev RetardedSobolev.Spaces MeasureTheory
  ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

/-- Transfer the existing fixed-solver component bound to the SAME uncut B.
Only admitted tensor quadratures are compared. Its native support, rather than
an added output cutoff, handles observations outside the original physical ball.
The sole consumer is the actual whole-source derivative integral identity. -/
private theorem same_response_tensor_bounds {d N : ℕ}
    (F : Euclidean (d+1) → Euclidean N)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (η : Euclidean (d+1) → ℝ)
    {S U W core chart : Set (Euclidean (d+1))}
    (hS : IsCompact S) (hU : IsOpen U)
    (hQ : ∀ j, ContDiffOn ℝ ∞ (fun y ↦ Q y j) U)
    (hη : ContDiff ℝ ∞ η) (hχU : S ⊆ U)
    (solver : smoothSource W (Euclidean (d+1)) →ₗ[ℝ]
      (Euclidean (d+1) → Euclidean (d+1)))
    (hsolver : ∀ h, ContDiff ℝ ∞ (solver h)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (x : Euclidean (d+1)) (R : ℝ) (hcore : closedBall x R ⊆ core)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hbound : ∀ (h : smoothSource W (Euclidean (d+1))) (m : ℕ),
      cNorm (closedBall x R) m (solver h) ≤ D m *
        (restrictionSobolevNorm W (m+(d+2)) (h : LocalL2 W (Euclidean (d+1))) +
          ‖(h : LocalL2 W (Euclidean (d+1)))‖))
    (K : Set (Euclidean (d+1)))
    (B : MetricField (d+1) →ₗ[ℝ] (Euclidean (d+1) → Euclidean N))
    (_heAgree : ∀ h : compactSmoothSources S, B h =
      fixedSmoothSolverAmbientExtension F Q η hU hQ hη hχU solver hsolver Ξ h)
    (_hBK : ∀ h : compactSmoothSources S, tsupport (B h) ⊆ K)
    (hKR : K ⊆ ball x R) :
    ∀ i j : Fin (d+1), ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (Jcoord d ⁻¹' S), ∀ y : Euclidean (d+1),
        ‖tensorComponentResponse (Jcoord d) S B i j u y‖ ≤ C * ‖ofTest s volume u.val‖ := by
  let a := fun _ : ℕ ↦ (0 : ℝ)
  have ha (m : ℕ) : 0 ≤ a m := le_rfl
  have hb (h : smoothSource W (Euclidean (d+1))) (m : ℕ) :
      cNorm (closedBall x R) m (solver h) ≤ D m *
        (restrictionSobolevNorm W (m+(d+2)) (h : LocalL2 W (Euclidean (d+1))) +
          (1+a (m+(d+2)+0)) * ‖(h : LocalL2 W (Euclidean (d+1)))‖) := by
    simpa only [a, add_zero, one_mul] using hbound h m
  have hfixed := exists_fixedSmoothSolver_tensorComponent_bounds (Jcoord d) (measurePreserving_Jcoord d)
    F Q η hS hU hQ hη hχU solver hsolver Ξ hchart (hF.mono hchartU)
    (fun y hy ↦ hi y (hchartU hy)) (fun y hy ↦ hrank y (hchartU hy))
    x R hcore D a hD ha 0 hb
  intro i j
  obtain ⟨s,C,hC,hb⟩ := hfixed i j 0
  simp only [norm_iteratedFDeriv_zero] at hb
  refine ⟨s,C,hC,?_⟩
  intro u y
  have hquad := tensorTestSource_quadratures_mem (Jcoord d) hS i j u
  change ‖complexifyResponse B (tensorTestSource (Jcoord d) i j u.val) y‖ ≤ _
  by_cases hy : y ∈ K
  · rw [PhysicalPrimary.OriginalComparisonResponse.complex_agreement B _ _heAgree _ hquad.1 hquad.2]
    exact hb u y (ball_subset_closedBall (hKR hy))
  · have hr := image_eq_zero_of_notMem_tsupport (fun hx ↦ hy (_hBK ⟨_,hquad.1⟩ hx))
    have hi' := image_eq_zero_of_notMem_tsupport (fun hx ↦ hy (_hBK ⟨_,hquad.2⟩ hx))
    simp only [complexifyResponse, LinearMap.coe_mk, AddHom.coe_mk, hr, hi', map_zero,
      smul_zero, add_zero, norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

open RawInputRealization RawInputPartition

local instance {n N : ℕ} : ESeminormedAddMonoid (Matrix (Fin N) (Fin n) ℂ) :=
  @SeminormedAddGroup.toESeminormedAddMonoid (Matrix (Fin N) (Fin n) ℂ) inferInstance

local instance {n N : ℕ} : ContinuousENorm (Matrix (Fin N) (Fin n) ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix (Fin N) (Fin n) ℂ) inferInstance).toContinuousENorm

local instance {n N : ℕ} : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin N) (Fin n) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin N → Fin n → ℂ))

private theorem integrable_native_annular_channel {n N : ℕ} {R M : ℝ}
    {β : Euclidean (n-1) → ℂ} (hβ : Measurable β) (hM : ∀ η, ‖β η‖ ≤ M)
    (v : AnnularL2 n R) (B : Euclidean (n-1) → Matrix (Fin N) (Fin n) ℂ)
    (hB : ContinuousOn B (annulus n R)) :
    Integrable (fun η ↦ channelDensity β v η • B η) := by
  have hK : IsCompact (annulus n R) :=
    (isCompact_closedBall _ _).diff isOpen_ball
  have hv := (Lp.memLp v).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hw := hv.bdd_mul hβ.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  have hc : ContinuousOn (fun η ↦ (Real.sqrt ‖η‖ : ℂ) • B η) (annulus n R) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_norm)).continuousOn).smul hB
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  have hi := hw.smul_bdd C (hc.aestronglyMeasurable hK.measurableSet)
    ((ae_restrict_mem hK.measurableSet).mono (fun η hη ↦ hC η hη))
  have hi' : IntegrableOn (fun η ↦ ((Real.sqrt ‖η‖ : ℂ) * β η * v η) • B η)
      (annulus n R) volume := by
    apply hi.congr
    filter_upwards [] with η
    change (β η * v η) • ((Real.sqrt ‖η‖ : ℂ) • B η) = _
    rw [smul_smul]
    congr 1
    ring
  simpa only [channelDensity, ← Set.indicator_smul_left] using
    (integrable_indicator_iff (measurableSet_annulus n R)).mpr hi'

/-- The already retained dyadic rate places every unchanged refined annulus
in the original coefficient-cutoff quarter-radius plateau
(`app:ch_waves:eq:sampling-prefix-normal`). -/
private theorem original_refined_shift_quarter {n J : ℕ} {τ ε ρ : ℝ}
    (hτ : 0 ≤ τ) (hε : ε ≤ ρ / 8)
    (hmargin : ∀ j : Fin J, τ * (2 : ℝ)^j.val ≤ ε)
    (j : RefinedIndex J) {η : Euclidean (n-1)}
    (hη : η ∈ annulus n (refinedRadius j)) : ‖τ • η‖ ≤ ρ / 4 := by
  have hj : j.2.val ≤ 1 := by have h := j.2.isLt; omega
  have hR : refinedRadius j ≤ (2 : ℝ)^(j.1.val + 1) := by
    unfold refinedRadius
    exact pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_left hj _)
  have hη' : ‖η‖ ≤ (2 : ℝ)^(j.1.val + 1) :=
    (mem_closedBall_zero_iff.mp hη.1).trans hR
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
  calc
    τ * ‖η‖ ≤ τ * (2 : ℝ)^(j.1.val+1) := mul_le_mul_of_nonneg_left hη' hτ
    _ = 2 * (τ * (2 : ℝ)^j.1.val) := by rw [pow_succ]; ring
    _ ≤ 2 * ε := mul_le_mul_of_nonneg_left (hmargin j.1) (by norm_num)
    _ ≤ ρ / 4 := by linarith

/-- The observation removes the need for a centered torus point outside
its support to lie in the original physical cell
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
private theorem original_observed_matrix_eq {n N : ℕ} {X : Set (Euclidean n)}
    {ψ : Euclidean n → ℝ} (hψX : tsupport ψ ⊆ X) {x : Euclidean n}
    {A B : Matrix (Fin N) (Fin n) ℂ} (h : x ∈ X → A = B) :
    ψ x • A = ψ x • B := by
  by_cases hψ : ψ x = 0
  · simp only [hψ, zero_smul]
  · rw [h (hψX (subset_tsupport ψ hψ))]

private theorem original_restore_angular_observation {n N : ℕ}
    (a ψ : ℝ) (full bare result : Matrix (Fin N) (Fin n) ℂ)
    (hfull : full = a • bare) (hactive : a ≠ 0 → ψ • bare = result) :
    ψ • full = a • result := by
  rw [hfull, smul_comm ψ a bare]
  by_cases ha : a = 0
  · simp only [ha, zero_smul]
  · rw [hactive ha]

private def original_refined_input (n J : ℕ) (v : RefinedInput n J) : WideInput n J :=
  (wideRefinement n J).symm v

private theorem original_ceiling_contains_zero {n J : ℕ} {V : Set (Euclidean (n-1))}
    (hceil : closedBall 0 ((2 : ℝ)^J) ⊆ V) : (0 : Euclidean (n-1)) ∈ V :=
  hceil (mem_closedBall_self (by positivity))

private theorem original_annular_sections {n N J : ℕ}
    {X : Set (Euclidean n)} {V : Set (Euclidean (n-1))}
    {B : Euclidean n × Euclidean (n-1) → Matrix (Fin N) (Fin n) ℂ}
    (hB : ContinuousOn B (X ×ˢ V)) (hceil : closedBall 0 ((2 : ℝ)^J) ⊆ V)
    {x : Euclidean n} (hx : x ∈ X) :
    ∀ j : RefinedIndex J, ContinuousOn (fun η ↦ B (x,η)) (annulus n (refinedRadius j)) := by
  intro j
  apply hB.comp (continuous_const.prodMk continuous_id).continuousOn
  intro η hη
  exact ⟨hx,hceil (closedBall_subset_closedBall (refinedRadius_le_ceiling j) hη.1)⟩

/-- Keep the actual matrix topology and kernel opaque at the metadata boundary. -/
private theorem original_smooth_annular_sections {n N J : ℕ}
    {X : Set (Euclidean n)} {V : Set (Euclidean (n-1))}
    {K : Euclidean n × Euclidean (n-1) → Matrix (Fin N) (Fin n) ℂ}
    (hK : ContDiffOn ℝ ∞ K (X ×ˢ V)) (hceil : closedBall 0 ((2 : ℝ)^J) ⊆ V)
    {x : Euclidean n} (hx : x ∈ X) :
    ∀ j : RefinedIndex J, ContinuousOn (fun η ↦ K (x,η)) (annulus n (refinedRadius j)) :=
  original_annular_sections hK.continuousOn hceil hx

/-- The source density of the SAME existing wide/refined isometry gives the
literal finite annular integral. This is equality, not a bandwise estimate.
In particular it adds no cardinality factor and changes no Fourier scalar. -/
private theorem raw_integral_refined_annuli {n N J : ℕ}
    (S : Euclidean n → Euclidean (n-1) → ℝ)
    (A : Euclidean n → Euclidean (n-1) → Matrix (Fin N) (Fin n) ℂ)
    (ζ : Euclidean (n-1)) (τ : ℝ) {d : Euclidean (n-1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    (v : RefinedInput n J) (x : Euclidean n)
    (hA : ∀ j : RefinedIndex J, ContinuousOn
      (fun η ↦ Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
        A x (ζ + τ • η)) (annulus n (refinedRadius j))) :
    rawPrimaryDemodulatedIntegral S A ζ τ volume
        (weightedWideDensity d ((wideRefinement n J).symm v)) x =
      ∑ j : RefinedIndex J, ∫ η,
        ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j.1.val η * v j η) •
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
            A x (ζ + τ • η)) ∂annularMeasure n (refinedRadius j) := by
  let B := fun η ↦ Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℝ)) •
    A x (ζ + τ • η)
  let β := fun j : RefinedIndex J ↦ weightedRadialBand d j.1.val
  have he := weightedWideDensity_eq_refined hd hM hb ((wideRefinement n J).symm v)
  simp only [LinearIsometryEquiv.apply_symm_apply] at he
  calc
    _ = ∫ η, density β v η • B η := by
      apply integral_congr_ae
      filter_upwards [he] with η hη
      rw [hη]
      exact smul_comm _ _ _
    _ = ∑ j : RefinedIndex J, ∫ η, channelDensity (β j) (v j) η • B η := by
      simp only [density, Finset.sum_smul]
      exact integral_finsetSum _ (fun j _ ↦ integrable_native_annular_channel
        (measurable_weightedRadialBand hd j.1.val) (norm_weightedRadialBand_le hb j.1.val)
        (v j) B (hA j))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact RawInputDilation.integral_channelDensity_smul (β j) B (v j)

private theorem tensor_bounds_on_original_chart {n N : ℕ}
    (e : (ℝ × (Fin (n-1) → ℝ)) ≃L[ℝ] Euclidean n) (S X : Set (Euclidean n))
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (h : ∀ i j : Fin n, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' S), ∀ y : Euclidean n,
        ‖tensorComponentResponse e S B i j u y‖ ≤ C * ‖ofTest s volume u.val‖) :
    ∀ i j : Fin n, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' S), ∀ y ∈ X,
        ‖tensorComponentResponse e S B i j u y‖ ≤ C * ‖ofTest s volume u.val‖ := by
  intro i j
  obtain ⟨s,C,hC,h⟩ := h i j
  exact ⟨s,C,hC,fun u y _ ↦ h u y⟩

end JanetCartan.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles
private def selected := `JanetCartan.PhysicalSeed.SelectedBoundary
private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args

/-- Read the coefficient cutoff from the actual scalar tester's support theorem.
No reference, cap, chart or cutoff is selected again. -/
elab "construct_original_mean_quadratic_geometry" : command => liftTermElabM do
  let producer := `JanetCartan.PhysicalSampling.OriginalCoefficientTester.one_on_coefficient_support
  forallBoundedTelescope (← getConstInfo producer).type (some 22) fun fixed _ => do
    unless fixed.size == 22 do throwError "mean quadratic: changed original scalar22 prefix"
    let cutoff ← forallBoundedTelescope (← inferType (app producer fixed)) (some 3) fun p _ => do
      unless p.size == 3 do throwError "mean quadratic: missing row/point/support certificate"
      let some χ := (← inferType p[2]!).find? (·.isAppOfArity (selected ++ `χcoeff) 21)
        | throwError "mean quadratic: scalar tester lost the original coefficient cutoff"
      return χ
    let original := cutoff.getAppArgs
    let n := original[0]!
    let sel (name : Name) := app (selected ++ name) original
    let μ := sel `rMeasure
    let hμ := sel `hrMeasure
    let χ ← store (ns ++ `Geometry.χ) fixed cutoff true
    discard <| store (ns ++ `Geometry.χ_smooth) fixed (sel `fact62)
    discard <| store (ns ++ `Geometry.χ_compact) fixed (sel `fact64)
    discard <| store (ns ++ `Geometry.χ_range) fixed (sel `fact63)
    discard <| store (ns ++ `Geometry.χ_cell) fixed
      (app ``coefficient_test_support_cell #[n,μ,χ,hμ,sel `fact59,sel `fact65])
    let radius := (← inferType (sel `hMeasureCell)).getAppArgs[(← inferType (sel `hMeasureCell)).getAppArgs.size-2]!
    let radius ← store (ns ++ `Geometry.Rbox) fixed radius true
    discard <| store (ns ++ `Geometry.Rbox_pos) fixed (app ``source_box_pos #[μ,hμ])
    discard <| store (ns ++ `Geometry.Rbox_lt_half) fixed (sel `hMeasureCell)
    let E := mkApp (mkConst `JanetCartan.Euclidean) n
    let zero ← mkNumeral E 0
    let K ← store (ns ++ `Geometry.K) fixed (← mkAppM `Metric.closedBall #[zero,radius]) true
    discard <| store (ns ++ `Geometry.K_compact) fixed
      (← mkAppM `ProperSpace.isCompact_closedBall #[zero,radius])
    discard <| store (ns ++ `Geometry.χ_one_on_K) fixed
      (app ``coefficient_test_plateau #[n,χ,K,sel `fact66])
    discard <| store (ns ++ `Geometry.K_box) fixed (app ``source_box_coordinates #[n,μ])
    for (name,index) in #[(`observation_support,2),(`measurement_support,1)] do
      let i ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 3)) index
      discard <| store (ns ++ `Geometry ++ name) fixed
        (app `JanetCartan.ContinuumRow.FixedCutoffs.physical_tsupport_four #[n,μ,hμ,i])
  logInfo "original scalar22 mean quadratic geometry: same chiCoeff, original four-mu compact and strict half-cell box; whole observation and measurement supports retained"

private def nativeArguments (name : Name) (value : Expr) : MetaM (Array (Name × Expr)) := do
  let value := value.headBeta
  unless value.isAppOf name do
    throwError "mean quadratic: expected original producer {name}, found {value.getAppFn}"
  let mut type := (← getConstInfo name).type
  let mut result := #[]
  for value in value.getAppArgs do
    let .forallE key _ rest _ := type | throwError "mean quadratic: changed native producer spine"
    result := result.push (key,value)
    type := rest.instantiate1 value
  return result

private def actual (values : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  let some (_,value) := values.find? (·.1 == key)
    | throwError "mean quadratic: original producer did not retain {key}"
  return value

private def applyNative (name : Name) (values : Array (Name × Expr)) (through : Name) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  let mut proof := mkConst name
  while let .forallE key _ rest _ := type do
    let value ← actual values key
    proof := mkApp proof value
    if key == through then return proof
    type := rest.instantiate1 value
  throwError "mean quadratic: producer ended before its final input {through}"

/-- Close the continuity premise of the whole-source integral theorem using
only the actual native ordinary response producer. The original weak-current
admissions are copied, not supplied as any norm or response-success premise. -/
elab "construct_original_mean_response_integral_continuity" : command => liftTermElabM do
  let joint := `JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity
  let info ← getConstInfo (joint ++ `joint_family)
  forallBoundedTelescope info.type (some 57) fun fixed _ => do
    unless fixed.size == 57 do throwError "mean quadratic: expected source53 and four original weak admissions"
    let some value := info.value? (allowOpaque := true)
      | throwError "mean quadratic: original ordinary response proof is unavailable"
    let values ← nativeArguments (joint ++ `joint_of_classical_and_admitted_support) (value.beta fixed)
    let Qraw ← actual values `Q
    let Q := Expr.proj ``Subtype 0 Qraw
    let hQ := Expr.proj ``And 0 (Expr.proj ``Subtype 1 Qraw)
    let d ← actual values `d
    let n := mkApp (mkConst ``Nat.succ) d
    let U ← actual values `U
    let hQ := app `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation.raw_components #[n,U,Q,hQ]
    let χ ← actual values `χ
    let S ← mkAppM `tsupport #[χ]
    let B ← store (ns ++ `Response.B) fixed (← actual values `B) true
    let values := #[(`Q,Q),(`hQ,hQ),(`S,S),(`hS,← actual values `hc),(`B,B)] ++ values
    let proof ← applyNative ``same_response_tensor_bounds values `hKR
    discard <| store (ns ++ `Response.tensor_component_bounds) fixed proof
  logInfo "original source53/weak4 tensor continuity: same full uncut B, original admitted chi2 tensor source, native output support and original inverse/paired-solver classical bounds; no response-success premise"

private def nativeBody (name : Name) (args : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "mean quadratic: missing actual producer body {name}"
  return (value.beta args).headBeta

private def declaredInputs : Expr → Nat
  | .forallE _ _ body _ => 1 + declaredInputs body
  | _ => 0

private def restrictCurrentCertificate (proof domain : Expr) : MetaM Expr := do
  forallBoundedTelescope (← inferType proof) (some 1) fun w _ => do
    withLocalDeclD `hw (← mkAppM ``Membership.mem #[domain,w[0]!]) fun hw => do
      mkLambdaFVars (w.push hw) (mkAppN proof #[w[0]!,.proj ``And 0 hw])

/-- The native whole-source response is interchanged with its original Fourier
integral, using the SAME uncut B. All analytic and shifted-domain certificates
come from the actual native constructors, not from a successful integral premise. -/
elab "construct_original_mean_whole_derivative_integral" : command => liftTermElabM do
  let wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
  let geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
  let masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
  let joint := `JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity
  let whole := `JanetCartan.CanonicalAtomRealization
  let rawName := wave ++ `Whole.raw_on_selected_cell
  let rawType := (← getConstInfo rawName).type
  let arity := declaredInputs rawType
  unless arity == 67 do throwError "mean quadratic: original whole-wave input telescope changed from67 to {arity}"
  forallBoundedTelescope rawType (some arity) fun all result => do
    unless result.getAppFn.isConstOf ``ContDiffOn do
      throwError "mean quadratic: original smoothness conclusion was unfolded into input binders"
    let params := all.pop
    let field ← nativeBody (wave ++ `Whole.corrected) all
    let fieldArgs ← nativeArguments (whole ++ `wholeSourceCorrectedWave) field
    let rawArgs ← nativeArguments `JanetCartan.RawPrimary.contDiffOn_fullPrimaryWave
      (← nativeBody rawName all)
    let known := fieldArgs ++ rawArgs
    let T ← actual known `T
    unless T.isAppOfArity (wave ++ `T) 53 do
      throwError "mean quadratic: whole corrected derivative changed the original53 current"
    let source := T.getAppArgs
    let B ← actual known `B
    let full := `JanetCartan.PhysicalPrimary.OriginalFullResponse.B
    let rawB ← if B.isAppOfArity full 38 then pure B else nativeBody B.getAppFn.constName! B.getAppArgs
    unless rawB.isAppOfArity full 38 do
      throwError "mean quadratic: Graph42 did not retain the actual globally uncut weak38 response"
    let weak := rawB.getAppArgs
    let ordinary := source ++ #[weak[24]!,weak[29]!,weak[30]!,weak[33]!]
    let retainedB ← nativeBody (ns ++ `Response.B) ordinary
    unless retainedB == app (joint ++ `B) ordinary do
      throwError "mean quadratic: component continuity changed its original ordinary response alias"
    let ordinaryB ← nativeBody (joint ++ `B) ordinary
    unless ordinaryB.isAppOfArity full 38 do
      throwError "mean quadratic: ordinary source57 changed its weak38 response"
    let ordinaryArgs := ordinaryB.getAppArgs
    let cb := ordinaryArgs[20]!
    unless cb.isAppOfArity (wave ++ `source_extra_on_graph) 22 do
      throwError "mean quadratic: missing original source callback alias"
    let cb ← nativeBody (wave ++ `source_extra_on_graph) cb.getAppArgs
    unless rawB == app full (ordinaryArgs.set! 20 cb) do
      throwError "mean quadratic: Graph42 and ordinary source57 changed their literal weak38 arguments"
    let window ← nativeBody (geo ++ `parameter_window) source
    unless window.isAppOfArity (masks ++ `V) 25 do
      throwError "mean quadratic: changed original doubled parameter window"
    let cell := window.getAppArgs
    let hsrc ← mkAppM `Set.Subset.trans
      #[app (masks ++ `χ₂_support_chart) source[:23].toArray,app (masks ++ `chart_in_cell) cell]
    let hresponse := app (joint ++ `full_response_smooth) ordinary
    let responseType ← inferType hresponse
    unless responseType.getAppFn.isConstOf ``ContDiffOn do
      throwError "mean quadratic: ordinary response lost its original smoothness conclusion"
    let responseDomain := responseType.appArg!
    let E := app `JanetCartan.Euclidean #[← actual known `n]
    let huniv ← mkAppOptM ``isOpen_univ #[some E,none]
    let hwindow := app (geo ++ `parameter_window_open) source
    let hopen ← mkAppM `IsOpen.inter
      #[← actual known `hΩ,← mkAppM `IsOpen.prod #[huniv,hwindow]]
    let domain := (← inferType hopen).appArg!
    let originalDomain ← actual known `Ω
    let domainType := (← inferType originalDomain).appArg!
    let left ← mkAppOptM `Set.inter_subset_left #[some domainType,some originalDomain,some responseDomain]
    let right ← mkAppOptM `Set.inter_subset_right #[some domainType,some originalDomain,some responseDomain]
    let hresponse ← mkAppM `ContDiffOn.mono #[hresponse,right]
    let hα ← mkAppM `ContDiffOn.mono #[← actual known `hα,left]
    let hspace ← restrictCurrentCertificate (← actual known `hspace) domain
    let hphase ← restrictCurrentCertificate (← actual known `hphase) domain
    let hnonzero ← restrictCurrentCertificate (← actual known `hnonzero) domain
    let originalShift ← actual known `hshift
    let hparameter := app (wave ++ `Whole.shifted_parameter_in_closed_cell) params
    let hwindowContains := app (masks ++ `V_contains_original_closed_cell) cell
    let hshift ← forallBoundedTelescope (← inferType originalShift) (some 2) fun p _ => do
      let x ← mkAppM ``Prod.fst #[p[0]!]
      let η ← mkAppM ``Prod.snd #[p[0]!]
      let hp := mkAppN hparameter #[η,.proj ``And 1 p[1]!]
      let hpType ← inferType hp
      unless hpType.isAppOfArity ``Membership.mem 5 do
        throwError "mean quadratic: original shifted parameter membership changed"
      let inWindow := mkAppN hwindowContains #[hpType.getAppArgs[4]!,hp]
      let inProduct ← mkAppM ``And.intro #[← mkAppM `Set.mem_univ #[x],inWindow]
      mkLambdaFVars p (← mkAppM ``And.intro #[mkAppN originalShift p,inProduct])
    let n ← actual known `n
    let N ← actual known `N
    let χ ← actual known `χ
    let S ← mkAppM `tsupport #[χ]
    let X ← actual known `X
    let e := app `JanetCartan.ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates.Jcoord #[source[0]!]
    let hB := app ``tensor_bounds_on_original_chart
      #[n,N,e,S,X,B,app (ns ++ `Response.tensor_component_bounds) ordinary]
    let data := #[(`Ω,domain),(`hΩ,hopen),(`hspace,hspace),(`hphase,hphase),(`hα,hα),
      (`hnonzero,hnonzero),(`hshift,hshift),(`hsrc,hsrc),(`d₀,source[0]!),(`e,e),(`hB,hB),(`hresponse,hresponse),
      (`hceil,← actual known `hVceil),
      (`hχ,app (masks ++ `χ₂_smooth) source[:23].toArray),
      (`hc,app (masks ++ `χ₂_compact) source[:23].toArray),
      (`hτ,← mkAppM `ne_of_gt #[source[48]!])] ++ known
    withLocalDeclD `x E fun x => do
      withLocalDeclD `hx (← mkAppM ``Membership.mem #[X,x]) fun hx => do
        let proof ← applyNative (whole ++ `wholeSourceCorrectedDerivative_eq_integral)
          (#[(`x,x),(`hx,hx)] ++ data) `hx
        discard <| store (ns ++ `Whole.derivative_integral) (all ++ #[x,hx]) proof
  logInfo "original source53/Graph42 whole derivative integral: SAME uncut B and literal source, native doubled-window shift and original Fourier density; no response/integral success premise"

/-- Reuse the already checked actual integral producer. No original selection,
response bound, or shifted-domain proof is recreated for the annular consequence. -/
elab "construct_original_mean_whole_refined_integral" : command =>
    liftTermElabM <| withTransparency .reducible do
  let whole := `JanetCartan.CanonicalAtomRealization
  let original := ns ++ `Whole.derivative_integral
  let type := (← getConstInfo original).type
  unless declaredInputs type == 69 do throwError "mean quadratic: changed original67 plus x/hx integral spine"
  forallBoundedTelescope type (some 69) fun all result => do
    unless result.isAppOfArity ``Eq 3 do throwError "mean quadratic: native integral conclusion changed"
    let params := all[:66].toArray
    let data ← nativeArguments (whole ++ `wholeSourceCorrectedDerivative_eq_integral)
      (← nativeBody original all)
    let integralArgs ← nativeArguments ``rawPrimaryDemodulatedIntegral result.getAppArgs[2]!
    let n ← actual data `n
    let J ← actual data `J
    let X ← actual data `X
    let V ← actual data `V
    let x ← actual data `x
    let hx ← actual data `hx
    let ζ ← actual integralArgs `ζ
    let hceil ← actual data `hceil
    let ceilingName := `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Whole.ceiling_buffer
    unless hceil.isAppOfArity ceilingName 64 do
      throwError "mean quadratic: lost the actual whole64 frequency ceiling"
    let .proj ``And 0 buffer ← nativeBody ceilingName hceil.getAppArgs
      | throwError "mean quadratic: original ceiling lost its retained dyadic-rate proof"
    let bounds ← nativeArguments
      `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.original_finite_band_open_buffer buffer
    let quarter ← applyNative ``original_refined_shift_quarter
      (#[(`n,n),(`J,J)] ++ bounds) `hmargin
    discard <| store (ns ++ `Whole.refined_shift_le_quarter) params[:64].toArray quarter
    let hzero := app ``original_ceiling_contains_zero #[n,J,V,hceil]
    let kernelProof ← applyNative (whole ++ `contDiffOn_correctedWideKernel)
      (#[(`O,X),(`ζ,ζ),(`hzero,hzero)] ++ data) `hzero
    let kernel ← store (ns ++ `Whole.kernel_smooth) params kernelProof
    logInfo "retained actual full corrected kernel smoothness on the SAME whole frequency window"
    let kernelType ← inferType kernel
    let kernelFn := kernelType.getAppArgs[kernelType.getAppArgs.size-2]!
    let hAnnular ← applyNative ``original_smooth_annular_sections
      (#[(`K,kernelFn),(`hK,kernel)] ++ data) `hx
    logInfo "retained actual matrix kernel on every unchanged refined annulus"
    let refinedType := app `JanetCartan.RawInputPartition.RefinedInput #[n,J]
    -- A Hilbert vector is data, not a typeclass; do not normalize its entire Lp type.
    withLocalDeclNoLocalInstanceUpdate `wRefined .default refinedType fun w => do
      let wide ← nativeBody ``original_refined_input #[n,J,w]
      let native := app original (params ++ #[wide,x,hx])
      let annular ← applyNative ``raw_integral_refined_annuli
        (#[(`v,w),(`x,x),(`hA,hAnnular)] ++ integralArgs ++ data) `hA
      let leftType ← inferType native
      let rightType ← inferType annular
      unless leftType.isAppOfArity ``Eq 3 && rightType.isAppOfArity ``Eq 3 do
        throwError "mean quadratic: the two actual integral equalities changed their heads"
      let left := leftType.getAppArgs
      let right := rightType.getAppArgs
      let proof := mkAppN (mkConst ``Eq.trans [.succ .zero])
        #[left[0]!,left[1]!,left[2]!,right[2]!,native,annular]
      discard <| store (ns ++ `Whole.derivative_refined_annuli) (params ++ #[w,x,hx]) proof
  logInfo "actual whole derivative refined annular sum: original wideRefinement inverse and full dyadic window, no Fourier rescaling, band-cardinality estimate or new integral success premise"

private def transActualMatrixEq (p q : Expr) : MetaM Expr := do
  let pt ← inferType p
  let qt ← inferType q
  unless pt.isAppOfArity ``Eq 3 && qt.isAppOfArity ``Eq 3 do
    throwError "mean quadratic: expected actual matrix equalities"
  let a := pt.getAppArgs
  let b := qt.getAppArgs
  return mkAppN (mkConst ``Eq.trans [.succ .zero]) #[a[0]!,a[1]!,a[2]!,b[2]!,p,q]

/-- Observe the actual native derivative only on the same original physical
support. The native G and all local integral hypotheses are already proved. -/
elab "construct_original_mean_inner_annular" : command =>
    liftTermElabM <| withTransparency .reducible do
  let source := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.Whole.G_native
  let constructor := `JanetCartan.PhysicalMean.OriginalCanonicalDerivativeTemplate.nativePeriodicDerivative_apply
  let info ← getConstInfo source
  unless declaredInputs info.type == 68 do
    throwError "mean quadratic: changed native inner66 plus wide input/torus point"
  forallBoundedTelescope info.type (some 68) fun all result => do
    unless result.isAppOfArity ``Eq 3 do throwError "mean quadratic: native G result changed"
    let params := all[:66].toArray
    let z := all[67]!
    let data ← nativeArguments constructor (← nativeBody source all)
    let n ← actual data `n
    let J ← actual data `J
    let input := app `JanetCartan.RawInputPartition.RefinedInput #[n,J]
    withLocalDeclNoLocalInstanceUpdate `wRefined .default input fun w => do
      let wide ← nativeBody ``original_refined_input #[n,J,w]
      let native := app source (params ++ #[wide,z])
      let nativeType ← inferType native
      let rhs := nativeType.getAppArgs[2]!
      unless rhs.isAppOfArity ``HSMul.hSMul 6 do
        throwError "mean quadratic: actual native G lost its original observation"
      let derivative := rhs.getAppArgs[5]!
      let derived ← nativeArguments
        `JanetCartan.CanonicalAtomRealization.wholeSourceCorrectedDerivative derivative
      let x ← actual derived `x
      let annular := app (ns ++ `Whole.derivative_refined_annuli) (params ++ #[w,x])
      let .forallE _ hxType _ _ ← inferType annular
        | throwError "mean quadratic: actual annular producer lost its physical-cell input"
      let (eq,hlocal) ← withLocalDeclNoLocalInstanceUpdate `hx .default hxType fun hx => do
        let proof := mkApp annular hx
        return (← inferType proof, ← mkLambdaFVars #[hx] proof)
      unless eq.isAppOfArity ``Eq 3 do throwError "mean quadratic: actual annular result changed"
      let observed ← applyNative ``original_observed_matrix_eq
        (#[(`x,x),(`A,eq.getAppArgs[1]!),(`B,eq.getAppArgs[2]!),(`h,hlocal)] ++ data) `h
      let proof ← transActualMatrixEq native observed
      discard <| store (ns ++ `Kernel.inner_refined_annuli) (params ++ #[w,z]) proof
  logInfo "SAME native inner G observed annular identity: original psi2, complete corrected derivative, exact wideRefinement and no physical-cell or integral-success premise"

/-- Restore the actual angular factor on all nodes, including its zero branch.
The active annular identity and full-wave factor come from the same native G. -/
elab "construct_original_mean_full_annular" : command =>
    liftTermElabM <| withTransparency .reducible do
  let source := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G_native
  let innerSource := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.Whole.G_native
  let info ← getConstInfo source
  unless declaredInputs info.type == 67 do
    throwError "mean quadratic: changed native full65 plus wide input/torus point"
  forallBoundedTelescope info.type (some 67) fun all result => do
    unless result.isAppOfArity ``Eq 3 do throwError "mean quadratic: full native G result changed"
    let body ← nativeBody source all
    let .const constructor _ := body.getAppFn
      | throwError "mean quadratic: native full realization lost its actual constructor"
    let .str _ "full_derivative_apply" := constructor
      | throwError "mean quadratic: native full realization no longer retains the zero-safe factor"
    unless body.getAppNumArgs == 12 do throwError "mean quadratic: changed full derivative constructor"
    let data ← nativeArguments constructor body
    let params := all[:65].toArray
    let z := all[66]!
    let n ← actual data `n
    let J ← actual data `J
    let input := app `JanetCartan.RawInputPartition.RefinedInput #[n,J]
    withLocalDeclNoLocalInstanceUpdate `wRefined .default input fun w => do
      let wide ← nativeBody ``original_refined_input #[n,J,w]
      let native := app source (params ++ #[wide,z])
      let nativeType ← inferType native
      let rhs := nativeType.getAppArgs[2]!
      unless rhs.isAppOfArity ``HSMul.hSMul 6 do
        throwError "mean quadratic: native full G lost its unchanged observation"
      let derivative := rhs.getAppArgs[5]!
      let derived ← nativeArguments
        `JanetCartan.CanonicalAtomRealization.wholeSourceCorrectedDerivative derivative
      let x ← actual derived `x
      let hfactor := (mkAppN (← actual data `hfactor) #[wide,x]).headBeta
      let factorType ← inferType hfactor
      unless factorType.isAppOfArity ``Eq 3 &&
          factorType.getAppArgs[2]!.isAppOfArity ``HSMul.hSMul 6 do
        throwError "mean quadratic: missing literal full angular derivative factor"
      let bare := factorType.getAppArgs[2]!.getAppArgs[5]!
      let hG ← actual data `hG
      let .forallE _ nonzero _ _ ← inferType hG
        | throwError "mean quadratic: native active-branch realization changed"
      let (observed,hactive) ←
          withLocalDeclNoLocalInstanceUpdate `ha .default nonzero fun ha => do
        let inner := (mkAppN hG #[ha,wide,z]).headBeta
        unless inner.isAppOfArity innerSource 68 do
          throwError "mean quadratic: full G did not retain the same actual inner G"
        let innerArgs := inner.getAppArgs
        let annular := app (ns ++ `Kernel.inner_refined_annuli)
          (innerArgs[:66].toArray ++ #[w,z])
        let innerType ← inferType inner
        let e := innerType.getAppArgs
        let reverse := mkAppN (mkConst ``Eq.symm [.succ .zero]) #[e[0]!,e[1]!,e[2]!,inner]
        let proof ← transActualMatrixEq reverse annular
        let conclusion ← inferType proof
        let observed := conclusion.getAppArgs[2]!
        if (observed.find? (· == ha)).isSome then
          throwError "mean quadratic: actual annular data unexpectedly depends on a nonzero proof"
        return (observed, ← mkLambdaFVars #[ha] proof)
      let restored ← applyNative ``original_restore_angular_observation
        (#[(`ψ,rhs.getAppArgs[4]!),(`full,factorType.getAppArgs[1]!),(`bare,bare),
          (`result,observed),(`hfull,hfactor),(`hactive,hactive)] ++ data) `hactive
      let proof ← transActualMatrixEq native restored
      discard <| store (ns ++ `Kernel.full_refined_annuli) (params ++ #[w,z]) proof
  logInfo "SAME full native G annular identity: angular factor once, actual a=0 zero branch, original psi2/full corrected derivative and unchanged refined input; no weight division or G rescaling"

/-- Project the SAME saved native53 event into task90's AtPoint chart and
source profiles. The two appended hypotheses are exactly the numerical
interfaces that the parent common-history construction must discharge:
`γ ≤ tolerance` and `Native.S ≤ R₀`. No chart, current, source, sample or
history is selected here. -/
elab "construct_original_mean_actual_moment_profiles" : command =>
    liftTermElabM <| withTransparency .reducible do
  let withActualG := JanetCartan.PhysicalMean.OriginalCanonicalActualTemplate.withActualG
  let fields := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry.AtPoint.fields
  let profiles := `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry.AtPoint.profiles
  withActualG (fun p _native _input _torus => do
    let tolerance := app `JanetCartan.PhysicalMean.OriginalSampledMomentGeometry.tolerance
      #[p[0]!,p[1]!]
    let hγMomentType ← mkAppM ``LE.le #[p[24]!,tolerance]
    let hExtraFrameType ← mkAppM ``LE.le #[p[3]!,tolerance]
    withLocalDeclNoLocalInstanceUpdate `hExtraFrame .default hExtraFrameType fun hExtraFrame => do
      let gammaExtra := app `JanetCartan.PhysicalSampling.OriginalBareScale.γ_le_extra p[:24].toArray
      let hγMoment ← mkAppM ``le_trans #[gammaExtra,hExtraFrame]
      discard <| store (ns ++ `AtPoint.actual_gamma_moment) (p ++ #[hExtraFrame]) hγMoment
      withLocalDeclNoLocalInstanceUpdate `hγMoment .default hγMomentType fun hγMomentVar => do
        let pref := #[p[0]!,p[1]!,p[2]!,p[3]!,p[4]!,p[5]!,p[6]!,p[7]!,p[8]!,p[9]!,
          p[10]!,p[11]!,p[12]!,p[13]!,p[14]!,p[15]!,p[16]!,p[17]!,p[18]!,p[19]!,
          p[20]!,p[21]!,p[22]!,p[23]!,p[24]!,p[25]!,p[26]!,hγMomentVar,p[27]!,p[28]!,
          p[29]!,p[30]!,p[31]!,p[32]!,p[33]!,p[34]!,p[35]!,p[39]!]
        let prefType ← inferType (app fields pref)
        let .forallE _ _ afterR _ := prefType
          | throwError "mean quadratic: task90 fields lost R₀ binder"
        let hRType := (← whnf afterR).bindingDomain!
        withLocalDeclNoLocalInstanceUpdate `hR90 .default hRType fun hR90 => do
          let all := pref ++ #[p[44]!,hR90,p[46]!,p[47]!,p[48]!,p[49]!,p[50]!,p[51]!,p[52]!]
          let fieldsValue := app fields all
          discard <| store (ns ++ `AtPoint.actual_fields) (p ++ #[hγMomentVar,hR90]) fieldsValue true
          let profilesValue := app profiles all
          discard <| store (ns ++ `AtPoint.actual_profiles) (p ++ #[hγMomentVar,hR90]) profilesValue true)
  logInfo "same native53 task90 AtPoint fields/profiles projected; only gamma-tolerance and common-R premises remain"

end JanetCartan.PhysicalMean.OriginalMeanQuadraticProfilesTemplate
end
