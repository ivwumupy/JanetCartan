module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalizedFamily.SourceCoefficients
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedLeading.NormalProfiles
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.FiberBounds

/-!
# Global amplitude-component profiles of the retained source family

The actual normal and detector profiles feed the existing fixed-cutoff
polynomial estimate. The full normal contains the original source scalar;
the scalar and flow factors in the raw endpoint can therefore both be one.
The fixed bump keeps the literal kernel on its entire original mask support.

Consumer: `hc` and `hgeom` of the uniform scalar-transport raw adjoint
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormal.FrozenModel
open PositiveReference PositiveReference.FlowConstruction
open ContinuumNormalReduction.TransportSymbol FullPhaseCharts.InverseEstimates
open DerivativeKernels AmplitudeProfiles

/-- The compactly supported polynomial in the original normal and detector
has a global component budget. This private step is instantiated below with
both actual coefficient families from `exists_retained_source_coefficient_profiles`
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-adjoint`). -/
private theorem exists_supported_normal_components {n N : ℕ}
    {R : ℝ} {V : Set CarrierParameter} (hV : IsOpen V)
    (z : Euclidean 3) {u a : ℝ} (hu : 0 < u) (ha : 0 < a)
    (hau : 12 * a ≤ u)
    (hchart : closedBall (chartCenter z) u ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (A : ℕ → ℝ) (hA : ∀ m, 0 < A m) :
    ∃ C₀ : Fin n → ℕ → ℝ, (∀ j i, 0 ≤ C₀ j i) ∧
      ∀ d : CarrierData n N,
      let ac := TransportKernel.coefficientsOfCarrier d (FixedCutoffs.physical ha 1)
      ContDiffOn ℝ ∞ ac.normal (ball (0 : Euclidean n) R ×ˢ V) →
      ContDiffOn ℝ ∞ ac.reduced (ball (0 : Euclidean n) R ×ˢ V) →
      (∀ m, cNorm (closedBall (chartCenter z) u) m ac.normal +
        cNorm (closedBall (chartCenter z) u) m ac.reduced ≤ A m) →
      let ν := fun p : AdjointJetPoint n ↦ chartBump z ha (p.2, p.1) • d.normalField p.2 p.1
      ContDiff ℝ ∞ ν ∧
      (∀ j, ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j)) ∧
      ∀ j p i,
        ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j) p‖ ≤
          C₀ j i := by
  let L := closedBall (chartCenter (n := n) z) u
  let O := ball (0 : Euclidean n) R ×ˢ V
  have hL : IsCompact L := isCompact_closedBall _ _
  have hO : IsOpen O := isOpen_ball.prod hV
  have hsupp : tsupport (chartBump (n := n) z ha) ⊆ L := by
    rw [(chartBump z ha).tsupport_eq]
    exact closedBall_subset_closedBall hau
  let Lq := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap
  choose D hD hd using fun j ↦ exists_cNorm_geometricPolynomial_le
    (N := N) z ha hu (A 0) (‖Lq‖ * A 0) j
  let C₀ := fun j i ↦ D j i * (1 + A i + ‖Lq‖ * A i)
  have hC₀ j i : 0 ≤ C₀ j i := by
    have := hD j i
    have := hA i
    dsimp [C₀]
    positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro d ac hg hred hcoeff
  let g := ac.normal
  let q := Lq ∘ ac.reduced
  let f := fun (j : Fin n) (p : Euclidean n × CarrierParameter) ↦
    ((FixedCutoffs.physical ha 1) p.1 * ‖chartBump z ha p • g p‖ ^ 2 * q p j : ℝ)
  have hg' : ContDiffOn ℝ ∞ g O := hg
  have hq : ContDiffOn ℝ ∞ q O := Lq.contDiff.comp_contDiffOn hred
  have hgB i : cNorm L i g ≤ A i :=
    (le_add_of_nonneg_right (cNorm_nonneg _ _ _)).trans (hcoeff i)
  have hqB i : cNorm L i q ≤ ‖Lq‖ * A i :=
    (cNorm_postLinear_le_on hL i Lq
      (fun p hp ↦ (hred.contDiffAt (hO.mem_nhds (hchart hp))).of_le (by simp))).trans
      (mul_le_mul_of_nonneg_left
        ((le_add_of_nonneg_left (cNorm_nonneg _ _ _)).trans (hcoeff i)) (norm_nonneg _))
  have hext : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      chartBump z ha p • g p) :=
    Localization.contDiff_of_contDiffOn_support_neighborhood hO
      ((chartBump z ha).contDiff.contDiffOn.smul hg')
      ((tsupport_smul_subset_left _ _).trans (hsupp.trans hchart))
  have hfsupp j : tsupport (fun p ↦ (f j p : ℂ)) ⊆ tsupport (chartBump z ha) := by
    apply (isClosed_tsupport _).closure_subset_iff.mpr
    intro p hp
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    exact hp (by simp [f, hz])
  have hf j : ContDiff ℝ ∞ (fun p ↦ (f j p : ℂ)) := by
    apply Localization.contDiff_of_contDiffOn_support_neighborhood hO
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((((FixedCutoffs.physical ha 1).contDiff.comp contDiff_fst).contDiffOn.mul
          (hext.norm_sq ℝ).contDiffOn).mul
          (contDiffOn_pi.mp (PiLp.contDiff_ofLp.comp_contDiffOn hq) j))
    · exact (hfsupp j).trans (hsupp.trans hchart)
  have hfB j i : cNorm L i (fun p ↦ (f j p : ℂ)) ≤ C₀ j i := by
    apply (hd j O hO hchart g q hg' hq (hgB 0) (hqB 0) i).trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl 1) (hgB i)) (hqB i)) (hD j i).le
  let ν := fun p : AdjointJetPoint n ↦ chartBump z ha (p.2, p.1) • d.normalField p.2 p.1
  have he j : carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j =
      fun p ↦ (f j (p.2, p.1) : ℂ) := by
    rfl
  refine ⟨hext.comp (contDiff_snd.prodMk contDiff_fst),
    fun j ↦ by rw [he]; exact (hf j).comp (contDiff_snd.prodMk contDiff_fst), ?_⟩
  intro j p i
  rw [he]
  apply ((LinearIsometryEquiv.prodComm ℝ CarrierParameter (Euclidean n)).norm_iteratedFDeriv_comp_right
    (fun p ↦ (f j p : ℂ)) p i).trans_le
  change ‖iteratedFDeriv ℝ i (fun p ↦ (f j p : ℂ)) (p.2, p.1)‖ ≤ C₀ j i
  by_cases hp : (p.2, p.1) ∈ L
  · exact (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
      (fun _ _ ↦ (hf j).contDiffAt.of_le (by simp)) hp (le_refl i)).trans (hfB j i)
  · have hz : iteratedFDeriv ℝ i (fun p ↦ (f j p : ℂ)) (p.2, p.1) = 0 := by
      by_contra hn
      exact hp (hsupp (hfsupp j (support_iteratedFDeriv_subset i hn)))
    rw [hz, norm_zero]
    exact hC₀ j i

/-- The SAME retained source scalar, normal and detector have global smooth
component extensions and all-order mixed derivative bounds before `σ`.
`exists_retained_source_coefficient_profiles` discharges the varying normal
and detector estimates from the actual seed ODE; the polynomial estimate is
applied on the prescribed fixed chart. The incidence center may differ from
the ODE center. The complete scalar is kept inside `extendedRetainedNormal`,
so `carrierKernel_extendedRetainedNormal_eq` preserves the literal adjoint
and its original measures (`app:ch_background:prop:bg-adjoint`, `bg-T`,
`bg-normalized`). -/
theorem exists_retained_source_component_profiles {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc M τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc M τ row col H.map)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {R : ℝ} {V : Set CarrierParameter} (hR : 0 < R)
    (hRphysical : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (z : Euclidean 3) {u a : ℝ} (hu : 0 < u) (ha : 0 < a)
    (hau : 12 * a ≤ u)
    (hchart : closedBall (chartCenter z) u ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hcell : 4 * a < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    ∃ C₀ : Fin n → ℕ → ℝ, (∀ j i, 0 ≤ C₀ j i) ∧
      ∀ σ ∈ Ioc (0 : ℝ) 1,
      ∀ cσ : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
        ((0 : Euclidean (n - 1)), zCell) Rc M τ row col (sourceDilation H.map σ),
      let d := data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
        (fun _ ↦ σ) ha hcell angular high
      let ν := RetainedLeading.extendedRetainedNormal T cσ.Q (sourceDilation H.map σ)
        row col cσ.forward cσ.inverse (fun _ ↦ σ) z ha
      ContDiff ℝ ∞ ν ∧
      (∀ j, ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j)) ∧
      ∀ j p i,
        ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j) p‖ ≤
          C₀ j i := by
  obtain ⟨A, hA, _hnormalized, hcurrent⟩ := exists_retained_source_coefficient_profiles H hP T hUH hΩ
    hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans hR hRphysical hRU hV hVP hflow
    (isCompact_closedBall (chartCenter (n := n) z) u) hchart ha hcell angular high
  obtain ⟨C₀, hC₀, hcomponents⟩ := exists_supported_normal_components (N := embeddingDimension n)
    hV z hu ha hau hchart A hA
  refine ⟨C₀, hC₀, ?_⟩
  intro σ hσ cσ
  obtain ⟨hnormal, hdetector, hbounds⟩ := hcurrent σ hσ cσ
  exact hcomponents (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse
    (fun _ ↦ σ) ha hcell angular high) hnormal hdetector hbounds

/-- Global component estimates for the literal normalized seed data, including
source scale zero. The seed ODE and contraction on the fixed compact coefficient
domain prove all normal and detector budgets. No contracted null-flow chart is
required to construct these amplitudes; the existing source matching theorem
identifies them with a supplied current chart when available. Consumer:
`exists_normalized_seed_rawAdjoint_for_submasks`
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_normalized_source_component_profiles {n : ℕ} (H : FlatReference n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    (hUH : U ⊆ H.domain.chart n)
    {Ω : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    {zCell : Euclidean 3} {ρ Rc M τ : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ω)
    (hpatch : Ω ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius))
    (hRc : 0 < Rc) (hτ : 0 < τ) (hτR : τ ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (c₀ : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc M τ row col H.map)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU c₀.Q.1 c₀.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    {R : ℝ} {V : Set CarrierParameter} (hR : 0 < R)
    (hRphysical : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hV : IsOpen V) (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (z : Euclidean 3) {u a : ℝ} (hu : 0 < u) (ha : 0 < a)
    (hau : 12 * a ≤ u)
    (hchart : closedBall (chartCenter z) u ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hcell : 4 * a < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    ∃ C₀ : Fin n → ℕ → ℝ, (∀ j i, 0 ≤ C₀ j i) ∧
      ∀ σ ∈ Icc (0 : ℝ) 1,
      let d := normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
        (fun _ ↦ 1) ha hcell angular high σ
      let ν := fun p : AdjointJetPoint n ↦ chartBump z ha (p.2, p.1) • d.normalField p.2 p.1
      ContDiff ℝ ∞ ν ∧
      (∀ j, ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j)) ∧
      ∀ j p i,
        ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j) p‖ ≤
          C₀ j i := by
  obtain ⟨A, hA, hnormalized, _hcurrent⟩ := exists_retained_source_coefficient_profiles H hP T hUH hΩ
    hKΩ hpatch hRc hτ hτR hbuffer hphysical c₀ htrans hR hRphysical hRU hV hVP hflow
    (isCompact_closedBall (chartCenter (n := n) z) u) hchart ha hcell angular high
  obtain ⟨C₀, hC₀, hcomponents⟩ := exists_supported_normal_components (N := embeddingDimension n)
    hV z hu ha hau hchart A hA
  refine ⟨C₀, hC₀, ?_⟩
  intro σ hσ
  obtain ⟨hnormal, hdetector, hbounds⟩ := hnormalized σ hσ
  exact hcomponents (normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse
    (fun _ ↦ 1) ha hcell angular high σ) hnormal hdetector hbounds

end JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
