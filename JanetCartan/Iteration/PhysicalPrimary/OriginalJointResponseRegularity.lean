module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalObservedSolver
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveRaw
public import JanetCartan.Iteration.PhysicalPrimary.OriginalComparisonResponseBase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullResponseSupported
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalObservation
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverJointRegularity
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CoefficientNorms
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.MeanCorrectedSource.ObservedCore.Coordinates
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate

/-!
# Ordinary joint regularity of the actual uncut primary response

Unlike the graded small-parameter inverse envelopes, ordinary regularity uses
only the local inverse's and the paired solver's positive Sobolev estimates.
The original chi3 localizes the inverse *source* of the full solver. No chi2 is
inserted ahead of that inverse and no output multiplier is introduced. The
classical constants may depend on the current, but precede every source.
Consumers: the actual original corrected atom and its two modulated amplitudes
on the doubled parameter window (`app:ch_response:cor:current-atoms`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 12000
set_option Elab.async false

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
  JanetCartan.RegularSector.Realization
namespace JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity
open FixedDomainInverse LocalSobolev SmallSupport Pseudodifferential RegularSector.Realization
  RegularSector.Characteristic.RetardedLocalization RegularSector.FiniteAssembly.CoefficientNorms
  ArbitraryAccuracy.ResidualLocalization ResponseTransfer.Complement

variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "CF" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp CF 2 (volume : Measure E)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Only the original chi3 *source* bump intervenes in the real-to-complex
Sobolev comparison. This identity, not a support assertion for a fresh mask,
identifies the input to the same full paired solver. -/
private theorem inclusion_bumped_extension {W : Set E} (hW : MeasurableSet W)
    {x : E} (χ₃ : ContDiffBump x) (u : LocalL2 W E) :
    l2ComplexInclusion volume (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ u)) =
      zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (l2ComplexInclusion (volume.restrict W) u)) := by
  have h₁ := bumpL2_complex_quadratures χ₃ u 0
  have h₂ := zeroExtend_complex_quadratures hW (bumpL2 (p := 2) le_rfl χ₃ u) 0
  simp only [map_zero, smul_zero, add_zero] at h₁ h₂
  rw [h₁, h₂]

/-- Ordinary classical continuity for the SAME uncut real smooth realization.
Apply the actual inverse estimate to the real smooth source itself, the
interior zero-extension bound only *after* its inverse, and the original
paired-solver estimate at the same order. The fixed Sobolev embedding costs
exactly `d+2` derivatives. This supplies the classical-bound premise of
`CorrectedAtoms.contDiffOn_fullPrimaryResponse_fixedSmoothSolver_of_classical_bound`.
No quantitative history profile is claimed (`app:ch_response:cor:current-atoms`). -/
theorem classical_costs_of_uncut_solver {W : Set E} (hW : MeasurableSet W)
    {x₀ : E} (χ₃ : ContDiffBump x₀) (hχ₃ : tsupport (χ₃ : E → ℝ) ⊆ W)
    (I : LocalL2 W E →L[ℝ] LocalL2 W E) (S : H →L[ℂ] H)
    (solver : smoothSource W E →ₗ[ℝ] (E → E)) (hsolver : ∀ h, ContDiff ℝ ∞ (solver h))
    (hae : ∀ h : smoothSource W E, solver h =ᵐ[volume]
      realCompression S (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (I h))))
    (CI aI CS aS : ℕ → ℝ) (hCI : ∀ s, 0 ≤ CI s) (haI : ∀ s, 0 ≤ aI s)
    (hCS : ∀ s, 0 ≤ CS s) (haS : ∀ s, 0 ≤ aS s)
    (hI : ∀ s u, MemRestrictionSobolev W s u → MemRestrictionSobolev W s (I u) ∧
      restrictionSobolevNorm W s (I u) ≤ CI s * (restrictionSobolevNorm W s u + aI s * ‖u‖))
    (hS : ∀ (s : ℕ) u, MemVectorFourierSobolev (s : ℝ) u → MemVectorFourierSobolev (s : ℝ) (S u) ∧
      vectorFourierSobolevNorm (s : ℝ) (S u) ≤ CS s * (vectorFourierSobolevNorm (s : ℝ) u + aS s * ‖u‖)) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (x : E) (R : ℝ), 0 < R → ∀ (h : smoothSource W E) (m : ℕ),
      cNorm (closedBall x R) m (solver h) ≤ D m *
        (restrictionSobolevNorm W (m + (d+2)) (h : LocalL2 W E) + ‖(h : LocalL2 W E)‖) := by
  choose Co hCo hcut using fun s ↦ exists_bump_zeroExtension_fourier_constant (r := d+1) χ₃ s
  choose Cq hCq hquad using fun s ↦ SignedProductEstimates.exists_source_quadrature_restriction_comparison (d := d) s
  choose Ce hCe hemb using fun m ↦ exists_cNorm_le_restrictionSobolevNorm (F := E) (d+1) m
  let A (s : ℕ) := (CS s * (1+aS s)) * (Co s * (2 * (CI s * (1+aI s))))
  have hA s : 0 ≤ A s := by dsimp only [A]; positivity [hCS s, haS s, hCo s, hCI s, haI s]
  refine ⟨fun m ↦ Ce m * (Cq (m+(d+2)) * A (m+(d+2))), fun m ↦
    mul_nonneg (zero_le_one.trans (hCe m)) (mul_nonneg (hCq _) (hA _)), ?_⟩
  intro x R hR h m
  let s := m + (d+2)
  let v := (h : LocalL2 W E)
  let u := I v
  let vi := l2ComplexInclusion (volume.restrict W) u
  let z : H := zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ vi)
  let U' := ball x (R+1)
  let out := l2RealPart (volume.restrict U') (restrictL2 U' (S z))
  obtain ⟨hu, hub⟩ := hI s v (h.property s)
  have hub' : restrictionSobolevNorm W s u ≤ (CI s * (1+aI s)) * (restrictionSobolevNorm W s v + ‖v‖) := by
    apply hub.trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hCI s)
    nlinarith only [mul_nonneg (haI s) (restrictionSobolevNorm_nonneg (U := W) (s := s) (u := v)), norm_nonneg v]
  obtain ⟨hvi, hvib⟩ := compLp_restrictionSobolev_bound (euclideanComplexInclusion (ι := Fin (d+1))) hu
  have hvi' : restrictionSobolevNorm W s vi ≤ 2 * restrictionSobolevNorm W s u := hvib.trans
    (mul_le_mul_of_nonneg_right (by linarith only [euclideanComplexInclusion_norm_le (ι := Fin (d+1))]) restrictionSobolevNorm_nonneg)
  obtain ⟨hz, hzb⟩ := hcut s W hW hχ₃ vi hvi
  have hzlow : ‖z‖ ≤ vectorFourierSobolevNorm (s : ℝ) z := by
    simpa only [vectorFourierSobolevNorm_zero] using vectorFourierSobolevNorm_mono hz (show (0 : ℝ) ≤ s by positivity)
  obtain ⟨hy, hyb⟩ := hS s z hz
  have hy' : vectorFourierSobolevNorm (s : ℝ) (S z) ≤ A s * (restrictionSobolevNorm W s v + ‖v‖) := by
    refine hyb.trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hzlow (haS s))) (hCS s)).trans ?_)
    calc
      _ = (CS s * (1+aS s)) * vectorFourierSobolevNorm (s : ℝ) z := by ring
      _ ≤ (CS s * (1+aS s)) * (Co s * (2 * ((CI s * (1+aI s)) * (restrictionSobolevNorm W s v + ‖v‖)))) :=
        mul_le_mul_of_nonneg_left (hzb.trans (mul_le_mul_of_nonneg_left
          (hvi'.trans (mul_le_mul_of_nonneg_left hub' (by norm_num))) (hCo s).le)) (mul_nonneg (hCS s) (by linarith [haS s]))
      _ = _ := by simp only [A, mul_assoc]
  have hout := hquad s (S z) hy U' 1 (by simp)
  simp only [one_smul] at hout
  have heglobal : solver h =ᵐ[volume] l2RealPart volume (S z) := by
    have ha := hae h
    change solver h =ᵐ[volume] l2RealPart volume (S (l2ComplexInclusion volume (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ u)))) at ha
    rwa [inclusion_bumped_extension] at ha
  have heq : solver h =ᵐ[volume.restrict U'] out := by
    filter_upwards [ae_restrict_of_ae heglobal, ae_restrict_of_ae (euclideanRealPart.coeFn_compLpL (S z)),
      euclideanRealPart.coeFn_compLpL (restrictL2 U' (S z)), restrictL2_coeFn U' (S z)] with y h₁ h₂ h₃ h₄
    exact (h₁.trans h₂).trans ((congrArg euclideanRealPart h₄.symm).trans h₃.symm)
  have hc := hemb m x R (R+1) hR (by linarith) (solver h) (hsolver h).contDiffOn out heq hout.1
  apply hc.trans
  exact (mul_le_mul_of_nonneg_left (hout.2.trans (mul_le_mul_of_nonneg_left hy' (hCq s)))
    (zero_le_one.trans (hCe m))).trans_eq (by simp only [s, v, mul_assoc])

/-- The proof-only completion chart is strictly inside the ordinary original
raw-current geometry, before every source and response order. -/
theorem weak_chart_in_raw {n : ℕ} (hn : 5 ≤ n) :
    ball (0 : Euclidean n) (PhysicalSeed.OriginalBoundary.b hn) ⊆
      ball 0 (PhysicalSeed.OriginalBoundary.R hn) := ball_subset_ball (PhysicalSeed.OriginalBoundary.b_lt_R hn).le

/-- The native source chart uses the minimum of these very two original
radii; no observation domain is shrunk in the parameter variable. -/
theorem source_chart_in_ball {n : ℕ} (x : Euclidean n) (r R : ℝ) : ball x (min r R) ⊆ ball x R :=
  ball_subset_ball (min_le_right _ _)

open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
  CorrectedAtoms PrimarySourceAdmission ResponseSourceExtension
  ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates

/-- Outside the original closed output the actual field is zero *for all
parameters in the window*. Inside, the classical fixed-solver estimate is
available. These two open germs cover the ambient space without a re-cut. -/
private theorem joint_window_of_native_output {n p q : ℕ}
    {V : Set (Euclidean 3 × Euclidean p)} (hV : IsOpen V)
    {K X : Set (Euclidean n)} (hK : IsClosed K) (hX : IsOpen X) (hKX : K ⊆ X)
    (f : Euclidean n × (Euclidean 3 × Euclidean p) → EuclideanSpace ℂ (Fin q))
    (h : ContDiffOn ℝ ∞ f (X ×ˢ V)) (hz : ∀ c ∈ V, ∀ x ∉ K, f (x,c) = 0) :
    ContDiffOn ℝ ∞ f (univ ×ˢ V) := by
  intro w hw
  by_cases hx : w.1 ∈ K
  · exact (h.contDiffAt ((hX.prod hV).mem_nhds ⟨hKX hx,hw.2⟩)).contDiffWithinAt
  · have h₀ : f =ᶠ[𝓝 w] (fun _ ↦ 0) := by
      filter_upwards [(hK.isOpen_compl.prod hV).mem_nhds (show w ∈ Kᶜ ×ˢ V from ⟨hx,hw.2⟩)] with y hy
      exact hz y.2 hy.2 y.1 hy.1
    exact (contDiffAt_const.congr_of_eventuallyEq h₀).contDiffWithinAt

variable {N : ℕ} {P : Patch (d+1)} {U : Set (Euclidean (d+1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : (Euclidean (d+1)) → Fin (d+1) → MetricTensor (d+1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : (Euclidean (d+1))) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d+1)) < T.family.threshold})
    (F : (Euclidean (d+1)) → Euclidean N) (row col : Fin (d+1))
    (Φ Y : ℝ × (Euclidean ((d+1)-1) × (Euclidean 3 × Euclidean ((d+1)-1))) →
      Euclidean ((d+1)-1) × (Euclidean 3 × Euclidean ((d+1)-1)))
    (χ η : (Euclidean (d+1)) → ℝ) (hη : ContDiff ℝ ∞ η) (hχU : tsupport χ ⊆ U)
    {W core chart : Set (Euclidean (d+1))} (solver : smoothSource W (Euclidean (d+1)) →ₗ[ℝ] ((Euclidean (d+1)) → (Euclidean (d+1))))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (x : (Euclidean (d+1))) (R : ℝ) (hcore : closedBall x R ⊆ core) (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hbound : ∀ (v : smoothSource W (Euclidean (d+1))) (m : ℕ), cNorm (closedBall x R) m (solver v) ≤
      D m * (restrictionSobolevNorm W (m+(d+2)) (v : LocalL2 W (Euclidean (d+1))) + ‖(v : LocalL2 W (Euclidean (d+1)))‖))
    {Ω : Set ((Euclidean (d+1)) × (Euclidean 3 × Euclidean ((d+1)-1)))} (hΩ : IsOpen Ω)
    (hspace : ∀ w ∈ Ω, w.1 ∈ U) (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    {X K : Set (Euclidean (d+1))} {V : Set (Euclidean 3 × Euclidean ((d+1)-1))}
    (hX : IsOpen X) (hV : IsOpen V) (hXV : X ×ˢ V ⊆ Ω)
    (hXR : X ⊆ ball x R) (hK : IsClosed K) (hKR : K ⊆ ball x R)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hχX : tsupport χ ⊆ X)
    (B : MetricField (d+1) →ₗ[ℝ] ((Euclidean (d+1)) → Euclidean N))
    (τ : ℝ) (hτ : τ ≠ 0) (r : Euclidean ((d+1)-1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)

set_option quotPrecheck false in
local notation "Bcore" => fixedSmoothSolverAmbientExtension F Q.1 η hU
  (fun j ↦ contDiffOn_pi.mp Q.property.1 j) hη hχU solver hsolver Ξ
set_option quotPrecheck false in
local notation "tensor" => fun c : Euclidean 3 × Euclidean ((d+1)-1) ↦
  complexAtomicSource F χ (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y,c.2))

include hchart hchartU hcore hD hbound hΩ hspace hphase hF hi hrank hnonzero hX hV hXV hXR hK hKR hχ hc hχX hτ hα

/-- Use the two existing fixed-solver joint regularity theorems on their
native domains. The true uncut map agrees with the proof-only localization on
admitted real tensors only, but that is enough for the *whole function* of x
in each original quadrature, hence also its physical derivative. The last
three clauses cover the entire current leading domain above the full doubled
window, not just the source chart. No parameter cutoff or summand estimate is
used (`app:ch_response:cor:current-atoms`, `app:ch_response:eq:current-atomic-amplitudes`). -/
theorem joint_of_classical_and_admitted_support
    (_heAgree : ∀ h : compactSmoothSources (tsupport χ), B h = Bcore h)
    (_hBK : ∀ h : compactSmoothSources (tsupport χ), tsupport (B h) ⊆ K)
    (_hquad : ∀ c ∈ V, tensorFieldRealPart (tensor c) ∈ compactSmoothSources (tsupport χ) ∧
      tensorFieldImagPart (tensor c) ∈ compactSmoothSources (tsupport χ)) :
    let O := Ω ∩ (univ ×ˢ V)
    ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) (univ ×ˢ V) ∧
    (ContDiffOn ℝ ∞ (fun w ↦ fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2 w.1) (X ×ˢ V) ∧
      ContDiffOn ℝ ∞ (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ) (X ×ˢ V) ∧
      ContDiffOn ℝ ∞ (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) (X ×ˢ V)) ∧
    ContDiffOn ℝ ∞ (fun w ↦ fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r w.2 w.1) O ∧
    ContDiffOn ℝ ∞ (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ) O ∧
    ContDiffOn ℝ ∞ (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ) O := by
  intro O
  let a := fun _ : ℕ ↦ (0 : ℝ)
  have ha (m : ℕ) : 0 ≤ a m := le_rfl
  have classicalBound (v : smoothSource W (Euclidean (d+1))) (m : ℕ) : cNorm (closedBall x R) m (solver v) ≤
      D m * (restrictionSobolevNorm W (m+(d+2)) (v : LocalL2 W (Euclidean (d+1))) +
        (1 + a (m+(d+2)+0)) * ‖(v : LocalL2 W (Euclidean (d+1)))‖) := by simpa only [a, add_zero, one_mul] using hbound v m
  have hsource (c) (hc : c ∈ V) (y) (hy : y ∈ tsupport χ) := hXV (show (y,c) ∈ X ×ˢ V from ⟨hχX hy,hc⟩)
  have hRin : ball x R ⊆ interior (closedBall x R) := interior_maximal ball_subset_closedBall isOpen_ball
  have hfixed := contDiffOn_fullPrimaryResponse_fixedSmoothSolver_of_classical_bound T Q F row col Φ Y χ η hη hχU
    solver hsolver Ξ hchart hchartU x R hcore D a hD ha 0 classicalBound (Jcoord d) (measurePreserving_Jcoord d)
    hΩ hspace hphase hF hi hrank hnonzero (isOpen_ball.prod hV) (fun _ hw ↦ hRin hw.1)
    (fun w hw ↦ hsource w.2 hw.2) hχ hc τ r hα
  have hlocal := contDiffOn_fullCorrectedPrimary_family_fixedSmoothSolver T Q F row col Φ Y χ η hη hχU
    solver hsolver Ξ hchart hchartU x R hcore D a hD ha 0 classicalBound (Jcoord d) (measurePreserving_Jcoord d)
    hΩ hspace hphase hF hi hrank hnonzero (hX.prod hV) (fun _ hw ↦ hRin (hXR hw.1))
    (fun w hw ↦ hsource w.2 hw.2) hχ hc hXV hτ r hα
  have agree (c) (hc : c ∈ V) : fullPrimaryResponse T Q F row col Φ Y χ B τ r c =
      fullPrimaryResponse T Q F row col Φ Y χ Bcore τ r c := by
    funext y
    unfold fullPrimaryResponse complexifyResponse
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [_heAgree ⟨_,(_hquad c hc).1⟩,_heAgree ⟨_,(_hquad c hc).2⟩]
  have hzero (c) (hc : c ∈ V) (y) (hy : y ∉ K) : fullPrimaryResponse T Q F row col Φ Y χ B τ r c y = 0 := by
    have hr := image_eq_zero_of_notMem_tsupport (fun hx ↦ hy (_hBK ⟨_,(_hquad c hc).1⟩ hx))
    have hi := image_eq_zero_of_notMem_tsupport (fun hx ↦ hy (_hBK ⟨_,(_hquad c hc).2⟩ hx))
    unfold fullPrimaryResponse complexifyResponse
    simp only [LinearMap.coe_mk, AddHom.coe_mk, hr, hi, map_zero, smul_zero, add_zero]
  have hglobal := joint_window_of_native_output hV hK isOpen_ball hKR
    (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1)
    (hfixed.congr (fun w hw ↦ congrFun (agree w.2 hw.2) w.1)) hzero
  have hO : IsOpen O := hΩ.inter (isOpen_univ.prod hV)
  have hred := hglobal.mono (show O ⊆ univ ×ˢ V from inter_subset_right)
  have hoΩ : O ⊆ Ω := inter_subset_left
  have hsp := fun w (hw : w ∈ O) ↦ hspace w (hoΩ hw)
  have hph := fun w (hw : w ∈ O) ↦ hphase w (hoΩ hw)
  have hn := fun w (hw : w ∈ O) ↦ hnonzero w (hoΩ hw)
  refine ⟨hglobal, ⟨hlocal.1.congr ?_,hlocal.2.1.congr ?_, hlocal.2.2.congr ?_⟩,
    contDiffOn_fullCorrectedPrimaryAtom_joint T Q F row col Φ Y χ B r hO hsp hph hF hi hrank (hα.mono hoΩ) hn τ hred,
    contDiffOn_fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r hO hsp hph hF hi hrank (hα.mono hoΩ) hn hτ hred,
    contDiffOn_fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r hO hsp hph hF hi hrank (hα.mono hoΩ) hn hτ hred⟩
  · intro w hw
    change fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (w.1,w.2.2) - fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1 =
      _ - fullPrimaryResponse T Q F row col Φ Y χ Bcore τ r w.2 w.1
    rw [agree w.2 hw.2]
  · intro w hw
    simp only [fullCorrectedDisplacementAmplitude, fullPrimaryResponseDisplacementAmplitude, agree w.2 hw.2]
  · intro w hw
    simp only [fullCorrectedDerivativeAmplitude, fullPrimaryResponseDerivativeAmplitude, agree w.2 hw.2]

end JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity

derive_original_uncut_classical_bound
retain_original_joint_solver_spine
identify_original_joint_tensor_frame
apply_original_joint_window_regularities
