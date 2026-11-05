module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ResidualSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverAtoms
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PreparationTransportPrimitives.OneHigh.Matrix
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds

/-!
# Both full residual quadratures and the literal corrected-atom strain

The original Frobenius matrix complexification transfers the two real residual
seminorms with no derivative loss. Each real source uses the identical supplied
solver, corrected-source map and angular operator. Source symmetry and the
all-order strain-seminorm identity are proved for the complete atomic source.

Consumers: the same-field arbitrary-precision estimate of
`app:ch_response:cor:current-atoms`, `PreparedHistory`, `Current`, and the actual
`UniformHistoryCorrection` producer. Quantitative angular decay and selection
of the inverse on the initialized source family remain analytic obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms
open PrimarySourceAdmission ResponseSourceExtension FixedDomainInverse LocalSobolev
open CharacteristicTransport.CompleteResidual

/-- Both quadratures of the full residual are the real residuals of the SAME
response on the original two sources. This is the complexification step of
`app:ch_response:eq:response-full-identity`. -/
theorem complexAtomicResidual_eq_quadratures {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ) {x : Euclidean n}
    (hR : DifferentiableAt ℝ (B (tensorFieldRealPart H)) x)
    (hI : DifferentiableAt ℝ (B (tensorFieldImagPart H)) x) :
    complexAtomicResidual F B H x =
      (linearizedMetric F (B (tensorFieldRealPart H)) x - tensorFieldRealPart H x).map Complex.ofReal +
        Complex.I •
          (linearizedMetric F (B (tensorFieldImagPart H)) x - tensorFieldImagPart H x).map Complex.ofReal := by
  have hd := (euclideanComplexInclusion.hasFDerivAt.comp x hR.hasFDerivAt).add
    ((euclideanComplexInclusion.hasFDerivAt.comp x hI.hasFDerivAt).const_smul Complex.I)
  have hp (a : Fin n) : partialDeriv (complexifyResponse B H) x a =
      euclideanComplexInclusion (partialDeriv (B (tensorFieldRealPart H)) x a) +
        Complex.I • euclideanComplexInclusion (partialDeriv (B (tensorFieldImagPart H)) x a) := by
    exact congrArg (fun L : Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin N) ↦
      L (EuclideanSpace.single a 1)) hd.fderiv
  ext i j
  apply Complex.ext <;>
    simp [complexAtomicResidual, WKB.complexLinearizedMetric, hp, linearizedMetric,
      tensorFieldRealPart, tensorFieldImagPart, PiLp.inner_apply,
      RCLike.inner_apply, Finset.sum_add_distrib, mul_comm]

/-- Finite full-residual seminorms are bounded by the sum of the two literal
real residual seminorms, with no norm or derivative loss. The Frobenius tensor
norm and the SAME response are preserved
(`app:ch_response:cor:current-atoms`). -/
theorem cNorm_complexAtomicResidual_le_quadrature_strains {n N : ℕ}
    (F : Euclidean n → Euclidean N)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    {K O : Set (Euclidean n)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hF : ContDiffOn ℝ ∞ F O)
    (hBR : ContDiffOn ℝ ∞ (B (tensorFieldRealPart H)) O)
    (hBI : ContDiffOn ℝ ∞ (B (tensorFieldImagPart H)) O)
    (hHR : ContDiffOn ℝ ∞ (tensorFieldRealPart H) O)
    (hHI : ContDiffOn ℝ ∞ (tensorFieldImagPart H) O) (s : ℕ) :
    cNorm K s (complexAtomicResidual F B H) ≤
      cNorm K s (linearizedMetric F (B (tensorFieldRealPart H)) - tensorFieldRealPart H) +
        cNorm K s (linearizedMetric F (B (tensorFieldImagPart H)) - tensorFieldImagPart H) := by
  let R := linearizedMetric F (B (tensorFieldRealPart H)) - tensorFieldRealPart H
  let I := linearizedMetric F (B (tensorFieldImagPart H)) - tensorFieldImagPart H
  let J := CurrentMean.PreparationTransportPrimitives.preparationMatrixComplexification (n := n) (N := n)
  let JI : MetricTensor n →L[ℝ] Matrix (Fin n) (Fin n) ℂ := Complex.I • J
  have hJ : ‖J‖ ≤ 1 := by
    apply J.opNorm_le_bound zero_le_one
    intro A
    change ‖A.map Complex.ofReal‖ ≤ 1 * ‖A‖
    rw [Matrix.frobenius_norm_map_eq A Complex.ofReal Complex.norm_real, one_mul]
  have hJI : ‖JI‖ ≤ 1 := by
    simpa only [JI, norm_smul, Complex.norm_I, one_mul] using hJ
  have hR : ContDiffOn ℝ ∞ R O :=
    (AmbientResponse.contDiffOn_linearizedMetric hO hF hBR).sub hHR
  have hI : ContDiffOn ℝ ∞ I O :=
    (AmbientResponse.contDiffOn_linearizedMetric hO hF hBI).sub hHI
  have hRAt (x) (hx : x ∈ K) : ContDiffAt ℝ s R x :=
    (hR.contDiffAt (hO.mem_nhds (hKO hx))).of_le (by simp)
  have hIAt (x) (hx : x ∈ K) : ContDiffAt ℝ s I x :=
    (hI.contDiffAt (hO.mem_nhds (hKO hx))).of_le (by simp)
  have he : cNorm K s (complexAtomicResidual F B H) =
      cNorm K s (fun x ↦ J (R x) + JI (I x)) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro x hx
    filter_upwards [hO.mem_nhds (hKO hx)] with y hy
    exact complexAtomicResidual_eq_quadratures F B H
      ((hBR.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
      ((hBI.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
  rw [he]
  apply (cNorm_add_le_of_contDiffAt hK
    (fun x hx ↦ J.contDiff.contDiffAt.comp x (hRAt x hx))
    (fun x hx ↦ JI.contDiff.contDiffAt.comp x (hIAt x hx))).trans
  apply add_le_add
  · exact (FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on hK s J hRAt).trans
      (by simpa using mul_le_mul_of_nonneg_right hJ (cNorm_nonneg K s R))
  · exact (FullPhaseCharts.InverseEstimates.cNorm_postLinear_le_on hK s JI hIAt).trans
      (by simpa using mul_le_mul_of_nonneg_right hJI (cNorm_nonneg K s I))

/-- Both complete source quadratures of the fixed ambient response obey the
full-strain bound with the original local Sobolev norms. The same constant,
solver, correction and angular operator are used for both sources; neither
quadrature is discarded. Their actual angular decay remains the input from
`both-response-transfer` (`app:ch_response:eq:response-full-identity`,
`app:ch_response:cor:current-atoms`). -/
theorem exists_fixedSmoothSolver_fullComplexStrain_cNorm_bound (n s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (F : Euclidean n → Euclidean N)
      (Q : Euclidean n → Fin n → MetricTensor n) (η : Euclidean n → ℝ)
      (S U W O core chart : Set (Euclidean n)) (hU : IsOpen U)
      (hQ : ∀ i, ContDiffOn ℝ ∞ (fun x ↦ Q x i) U)
      (hη : ContDiff ℝ ∞ η) (hSU : S ⊆ U)
      (solver right : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
      (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)),
      (∀ v, ContDiff ℝ ∞ (right v)) →
      ∀ Ξ : OutputCutoff core chart, IsOpen chart → ContDiffOn ℝ ∞ F chart →
      IsImmersionOn F chart → HasFullNormalRankOn F chart →
      ∀ (Corr : LocalL2 W (Euclidean n) →L[ℝ] LocalL2 W (Euclidean n))
        (A : Lp (Euclidean n) 2 (volume : Measure (Euclidean n)) →L[ℝ]
          Lp (Euclidean n) 2 (volume : Measure (Euclidean n)))
        (hW : MeasurableSet W), S ⊆ W → S ⊆ {x | η x = 1} →
      (∀ v, EqOn (physicalWeakApply
        (fun y a ↦ ActualCarriers.pencil (Q y) (EuclideanSpace.single a 1))
        (fun y ↦ GeometricProfile.reducedZerothCoefficient F (Q y) y)
        (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)
        (fderiv ℝ (fun y ↦ (euclideanComplexInclusion (solver v y)).ofLp)))
        (fun y ↦ (euclideanComplexInclusion (right v y)).ofLp) O) →
      (∀ v : smoothSource W (Euclidean n), right v =ᵐ[volume.restrict O]
        (SmallSupport.zeroExtend hW (v : LocalL2 W (Euclidean n)) +
          A (SmallSupport.zeroExtend hW (Corr v)) - SmallSupport.zeroExtend hW (Corr v))) →
      ∀ (x : Euclidean n) (r R : ℝ), 0 < r → r < R →
      ball x R ⊆ O → ball x R ⊆ core → ball x R ⊆ U →
      (∀ y ∈ ball x R, ∀ i, (Q y i).IsSymm) →
      (∀ y ∈ ball x R, LinearIndependent ℝ (Q y)) →
      (∀ y ∈ ball x R,
        (Submodule.span ℝ (range (Q y)) : Set (MetricTensor n)) = stressSpace F y) →
      ∀ (H : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
        (hR : tensorFieldRealPart H ∈ compactSmoothSources S)
        (hI : tensorFieldImagPart H ∈ compactSmoothSources S),
      (∀ y ∈ ball x R, (H y).IsSymm) →
      let B := fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
      let residualNorm := fun h : compactSmoothSources S ↦
        let z := SmallSupport.zeroExtend hW
          (Corr (cutoffStressSmoothSource (W := W) Q η hU hQ hη hSU h))
        let e := A z - z
        restrictionSobolevNorm (ball x R) (s+n+1)
          (((Lp.memLp e).restrict (ball x R)).toLp e)
      cNorm (closedBall x r) s (complexAtomicResidual F B H) ≤
        ((s+1 : ℝ) * (2 : ℝ)^s) *
          cNorm (closedBall x r) s (fun y ↦ fullStressResidualReconstruction (Q y)) *
          (C * (residualNorm ⟨_, hR⟩ + residualNorm ⟨_, hI⟩)) := by
  obtain ⟨C, hC, hbound⟩ := exists_fixedSmoothSolver_fullStrain_cNorm_bound n s
  refine ⟨C, hC, ?_⟩
  intro N F Q η S U W O core chart hU hQ hη hSU solver right hsolver hsmooth Ξ
    hchart hF hi hrank Corr A hW hSW hplateau hphysical hright x r R hr hrR hVO hVcore hVU
    hQsymm hQlin hspan H hR hI hsymm
  dsimp only
  let B := fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU solver hsolver Ξ
  have hBR := contDiff_fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU
    solver hsolver Ξ hchart hF hi hrank ⟨_, hR⟩
  have hBI := contDiff_fixedSmoothSolverAmbientExtension F Q η hU hQ hη hSU
    solver hsolver Ξ hchart hF hi hrank ⟨_, hI⟩
  have hcorechart : core ⊆ chart := by
    intro y hy
    have heq : Ξ.toFun y = 1 := interior_subset (s := {z | Ξ.toFun z = 1}) (Ξ.plateau hy)
    exact Ξ.support_chart (subset_tsupport _ (by change Ξ.toFun y ≠ 0; rw [heq]; exact one_ne_zero))
  have hcomplex := cNorm_complexAtomicResidual_le_quadrature_strains F B H
    (isCompact_closedBall x r) hchart ((closedBall_subset_ball hrR).trans (hVcore.trans hcorechart))
    hF hBR.contDiffOn hBI.contDiffOn hR.1.contDiffOn hI.1.contDiffOn s
  have hreal := hbound N F Q η S U W O core chart hU hQ hη hSU solver right hsolver hsmooth Ξ
    hchart hF hi hrank Corr A hW hSW hplateau hphysical hright x r R hr hrR hVO hVcore hVU
    hQsymm hQlin hspan ⟨_, hR⟩ (fun y hy ↦ (hsymm y hy).map Complex.re)
  have himag := hbound N F Q η S U W O core chart hU hQ hη hSU solver right hsolver hsmooth Ξ
    hchart hF hi hrank Corr A hW hSW hplateau hphysical hright x r R hr hrR hVO hVcore hVU
    hQsymm hQlin hspan ⟨_, hI⟩ (fun y hy ↦ (hsymm y hy).map Complex.im)
  exact hcomplex.trans ((add_le_add hreal himag).trans_eq (by ring))

/-- The complete cutoff strain is symmetric at every point, including both
quadratures and every lower-order term. This discharges source symmetry in
`exists_fixedSmoothSolver_fullComplexStrain_cNorm_bound` for the literal
primary source (`app:ch_response:cor:current-atoms`). -/
theorem complexAtomicSource_isSymm {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) (x : Euclidean n) :
    (complexAtomicSource F χ W x).IsSymm := by
  change (complexAtomicSource F χ W x).transpose = complexAtomicSource F χ W x
  ext i j
  simp only [complexAtomicSource, Matrix.transpose_apply, Matrix.smul_apply,
    WKB.complexLinearizedMetric]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

section Retained

open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ η : Euclidean n → ℝ) (hη : ContDiff ℝ ∞ η) (hχU : tsupport χ ⊆ U)
    {W core chart : Set (Euclidean n)}
    (solver : smoothSource W (Euclidean n) →ₗ[ℝ] (Euclidean n → Euclidean n))
    (hsolver : ∀ v, ContDiff ℝ ∞ (solver v)) (Ξ : OutputCutoff core chart)

set_option quotPrecheck false in
local notation "Bfixed" => fixedSmoothSolverAmbientExtension F Q.1 η hU
  (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη hχU solver hsolver Ξ

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (hchart : IsOpen chart) (hchartU : chart ⊆ U)
    (τ : ℝ) (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (c : Euclidean 3 × Euclidean (n - 1))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : ∀ x ∈ tsupport χ, (x, c) ∈ Ω)

include hΩ hspace hphase hF hi hrank hnonzero hchart hchartU hα hχ hc hs

/-- Every physical strain seminorm of the SAME literal corrected primary is
exactly that of its original complex response residual. Source admission and
response smoothness are supplied by the retained raw construction and the
accepted smooth solver. Both quadratures can therefore use the preceding
full-residual estimate without an extra analytic assumption
(`app:ch_response:cor:current-atoms`). -/
theorem cNorm_fullCorrectedPrimaryAtom_strain_fixedSmoothSolver
    {K V : Set (Euclidean n)} (hV : IsOpen V) (hKV : K ⊆ V)
    (hVΩ : ∀ x ∈ V, (x, c) ∈ Ω) (hplateau : ∀ x ∈ V, χ x = 1) (s : ℕ) :
    cNorm K s (WKB.complexLinearizedMetric F
      (fullCorrectedPrimaryAtom T Q F row col Φ Y χ Bfixed τ r c)) =
      cNorm K s (complexAtomicResidual F Bfixed (complexAtomicSource F χ
        (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y, c.2)))) := by
  have hraw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero
  have hresponse := contDiff_fullPrimaryResponse_fixedSmoothSolver T Q F row col Φ Y χ η hη hχU
    solver hsolver Ξ hΩ hspace hphase hF hi hrank hnonzero hchart hchartU
    τ r hα c hχ hc hs
  apply cNorm_complexCorrectedAtom_strain_eq F χ Bfixed _ hV hKV hplateau
  · intro x hx
    exact (((hraw.contDiffAt (hΩ.mem_nhds (hVΩ x hx))).comp x
      (f := fun y : Euclidean n ↦ (y, c))
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  · intro x _
    exact hresponse.differentiable (by simp) x

end Retained

end JanetCartan.CorrectedAtoms
