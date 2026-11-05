module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.SourceCoefficients
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# All-order coefficients of the same retained source carriers

The supplied seed chart proves smoothness of its literal unit-initial scalar
by its ODE equations. Source contraction keeps one compact coefficient range
for every scale in `[0, 1]`. ODE uniqueness then transfers all derivative
bounds to any supplied source chart with the same minor and buffers. The
normal, detector, masks and source initial value are the original ones.

Consumer: the full-normal component profiles in the normalized raw-adjoint
construction (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:prop:bg-normalized`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier ContinuumNormal.FrozenModel
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction
open NormalizedBackground NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol FullPhaseCharts.InverseEstimates
open LeadingWave AmbientResponse ProjectedStressFrame

/-- Uniform all-order normal and detector bounds for the literal carriers of
one supplied flat-reference chart. Smoothness of the seed amplitude follows
from `Chart.scalar_spec`, and `retained_charts_source_dilation` identifies the
actual positive-scale fields by ODE uniqueness. The fixed compact range and
the whole profile precede `σ` and the supplied current chart. In particular,
the source interval does not shrink as the derivative order increases.

The coefficient product may have an incidence center different from the ODE
cell center. Its inclusion in the ORIGINAL output cylinder is retained, so no
detector mask is replaced. This is the amplitude input to
`UniformEndpoint.exists_uniform_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:prop:bg-adjoint`, `bg-Nsigma`, `bg-normalized`). -/
theorem exists_retained_source_coefficient_profiles {n : ℕ} (H : FlatReference n)
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
    {K : Set (Euclidean n × CarrierParameter)} (hK : IsCompact K)
    (hKO : K ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {rm : ℝ} (hrm : 0 < rm) (hcell : 4 * rm < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      (∀ σ ∈ Icc (0 : ℝ) 1,
        let aσ := TransportKernel.coefficientsOfCarrier
          (normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse (fun _ ↦ 1)
            hrm hcell angular high σ) (FixedCutoffs.physical hrm 1)
        ContDiffOn ℝ ∞ aσ.normal (ball (0 : Euclidean n) R ×ˢ V) ∧
        ContDiffOn ℝ ∞ aσ.reduced (ball (0 : Euclidean n) R ×ˢ V) ∧
        ∀ m, cNorm K m aσ.normal + cNorm K m aσ.reduced ≤ A m) ∧
      ∀ σ ∈ Ioc (0 : ℝ) 1,
      ∀ cσ : Chart T Ω (closedBall ((0 : Euclidean n), zCell) ρ)
        ((0 : Euclidean (n - 1)), zCell) Rc M τ row col (sourceDilation H.map σ),
      let aσ := TransportKernel.coefficientsOfCarrier
        (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse (fun _ ↦ σ)
          hrm hcell angular high) (FixedCutoffs.physical hrm 1)
      ContDiffOn ℝ ∞ aσ.normal (ball (0 : Euclidean n) R ×ˢ V) ∧
      ContDiffOn ℝ ∞ aσ.reduced (ball (0 : Euclidean n) R ×ˢ V) ∧
      ∀ m, cNorm K m aσ.normal + cNorm K m aσ.reduced ≤ A m := by
  have hi : IsImmersionOn H.map U :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ H.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn H.map U := fun x hx ↦ H.fullNormalRank x (hUH hx)
  let O := ball (0 : Euclidean n) R ×ˢ V
  have hO : IsOpen O := isOpen_ball.prod hV
  have hmapsW := hflow.mono_right (outputCylinder_spec hRc hτ).2
  have hmaps := fun p hp ↦ c₀.small_subset (hmapsW (x := p) hp)
  obtain ⟨_, hb, _, _, _, _, _, _⟩ :=
    c₀.scalar_spec hτ (fun _ ↦ 1) contDiffOn_const (fun _ _ ↦ zero_lt_one)
  have harg : ContDiff ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      (p.1, parameter p.2)) := contDiff_fst.prodMk (parameter.contDiff.comp contDiff_snd)
  have hb' : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T c₀.Q H.map row col c₀.forward c₀.inverse (fun _ ↦ 1)
        (p.1, parameter p.2) • carrierNullvector T c₀.Q col (p.1, parameter p.2)) O :=
    hb.comp harg.contDiffOn hmaps
  let ξ := fun p : Euclidean n × CarrierParameter ↦ T.carrierGradient c₀.Q p.1 (parameter p.2)
  let ν := fun p : Euclidean n × CarrierParameter ↦
    normalField T c₀.Q H.map row col c₀.forward c₀.inverse (fun _ ↦ 1) p.1 p.2
  let q := fun p : Euclidean n × CarrierParameter ↦
    (quadratic (c₀.Q.1 p.1) (ξ p)).ofLp
  have hVP' : ∀ z ∈ V, parameter z ∈ parameterInterior (2 * P.radius) :=
    fun z hz i ↦ (hVP hz i).trans (by linarith [hP.1])
  have hξ : ContDiffOn ℝ ∞ ξ O := by
    simpa only [Function.comp_def] using (T.carrierGradient_smooth hP c₀.Q).comp
      (f := fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      (s := O) harg.contDiffOn
      (fun p hp ↦ ⟨ball_subset_ball hRphysical hp.1, hVP' p.2 hp.2⟩)
  have hν : ContDiffOn ℝ ∞ ν O :=
    contDiffOn_canonicalPrincipalNormal hU H.contDiff.contDiffOn hi hrank (U := O)
      (fun _ hp ↦ hRU hp.1) hξ hb'
  have hQreg : ContDiffOn ℝ ∞ (fun p : Euclidean n × CarrierParameter ↦ c₀.Q.1 p.1) O :=
    c₀.Q.2.1.comp (f := Prod.fst) (s := O) contDiffOn_fst (fun _ hp ↦ hRU hp.1)
  have hq₀ := contDiff_quadratic.comp_contDiffOn (hQreg.prodMk hξ)
  have hq₁ := PiLp.contDiff_ofLp.comp_contDiffOn hq₀
  have hq : ContDiffOn ℝ ∞ q O := hq₁
  let S := (fun p : ℝ × (Euclidean n × CarrierParameter) ↦ (p.1 • p.2.1, p.2.2)) ''
    (Icc (0 : ℝ) 1 ×ˢ K)
  have hS : IsCompact S := (isCompact_Icc.prod hK).image
    ((continuous_fst.smul continuous_snd.fst).prodMk continuous_snd.snd)
  have hcontract (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
      MapsTo (fun p : Euclidean n × CarrierParameter ↦ (σ • p.1, p.2)) O O :=
    fun p hp ↦ ⟨(convex_ball (0 : Euclidean n) R).smul_mem_of_zero_mem
      (mem_ball_self hR) hp.1 hσ, hp.2⟩
  have hSO : S ⊆ O := by
    rintro p ⟨⟨σ, x⟩, ⟨hσ, hx⟩, rfl⟩
    exact hcontract σ hσ (hKO hx)
  let A := fun m : ℕ ↦ (m + 1 : ℝ) * (cNorm S m ν + cNorm S m q) + 1
  have hA m : 0 < A m := by
    have := cNorm_nonneg S m ν
    have := cNorm_nonneg S m q
    dsimp [A]
    positivity
  let an := fun σ ↦ TransportKernel.coefficientsOfCarrier
    (normalizedCarrierData T c₀.Q H.map row col c₀.forward c₀.inverse (fun _ ↦ 1)
      hrm hcell angular high σ) (FixedCutoffs.physical hrm 1)
  have hnorm (σ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
      ContDiffOn ℝ ∞ (an σ).normal O ∧ ContDiffOn ℝ ∞ (an σ).reduced O ∧
        ∀ m, cNorm K m (an σ).normal + cNorm K m (an σ).reduced ≤ A m := by
    let Lσ : (Euclidean n × CarrierParameter) →L[ℝ] (Euclidean n × CarrierParameter) :=
      (σ • ContinuousLinearMap.fst ℝ (Euclidean n) CarrierParameter).prod
        (ContinuousLinearMap.snd ℝ (Euclidean n) CarrierParameter)
    have hLσ : ‖Lσ‖ ≤ 1 := by
      apply Lσ.opNorm_le_bound zero_le_one
      intro p
      change ‖(σ • p.1, p.2)‖ ≤ 1 * ‖p‖
      rw [one_mul, Prod.norm_def, Prod.norm_def, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hσ.1]
      exact max_le ((mul_le_of_le_one_left (norm_nonneg _) hσ.2).trans
        (le_max_left _ _)) (le_max_right _ _)
    have hmap : MapsTo Lσ K S := fun p hp ↦ ⟨(σ, p), ⟨hσ, hp⟩, rfl⟩
    have he (p) (hp : p ∈ O) :
        (an σ).normal p = (ν ∘ Lσ) p ∧ (an σ).reduced p = (q ∘ Lσ) p := by
      have h := coefficientsOfCarrier_normalizedCarrierData_eq_source T c₀.Q H.map row col
        c₀.forward c₀.inverse (fun _ ↦ 1) hrm hcell angular high (FixedCutoffs.physical hrm 1)
        hP c₀.frame_eq (ball_subset_ball hRphysical (hcontract σ hσ hp).1) (hVP' p.2 hp.2)
      refine ⟨rfl, ?_⟩
      simpa only [normalizedSourceCoefficients, ← c₀.frame_eq, an, q, ξ, Lσ,
        Function.comp_apply, ContinuousLinearMap.prod_apply, smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using h.2
    refine ⟨(hν.comp Lσ.contDiff.contDiffOn (hcontract σ hσ)).congr
      (fun p hp ↦ (he p hp).1),
      (hq.comp Lσ.contDiff.contDiffOn (hcontract σ hσ)).congr
      (fun p hp ↦ (he p hp).2), ?_⟩
    intro m
    have hnEq : cNorm K m (an σ).normal = cNorm K m (ν ∘ Lσ) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq
      intro p hp
      filter_upwards [hO.mem_nhds (hKO hp)] with x hx
      exact (he x hx).1
    have hqEq : cNorm K m (an σ).reduced = cNorm K m (q ∘ Lσ) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq
      intro p hp
      filter_upwards [hO.mem_nhds (hKO hp)] with x hx
      exact (he x hx).2
    rw [hnEq, hqEq]
    have hnB := cNorm_comp_contraction_le_on Lσ hLσ hS hO hSO hν hmap m
    have hqB := cNorm_comp_contraction_le_on Lσ hLσ hS hO hSO hq hmap m
    dsimp [A]
    linarith
  refine ⟨A, hA, hnorm, ?_⟩
  intro σ hσ cσ
  let ac := TransportKernel.coefficientsOfCarrier
    (data T cσ.Q (sourceDilation H.map σ) row col cσ.forward cσ.inverse (fun _ ↦ σ)
      hrm hcell angular high) (FixedCutoffs.physical hrm 1)
  obtain ⟨_, _, _, hnull, _⟩ := RetainedLeading.retained_charts_source_dilation
    T hΩ hKΩ hpatch hRc hτ hτR hbuffer H.contDiff hrank hphysical c₀ htrans
    (fun x _ ↦ H.inducedMetric_eq_one x) hσ.1 hσ.2 cσ
  have hfields (p) (hp : p ∈ O) : ac.normal p = (an σ).normal p ∧
      ac.reduced p = (an σ).reduced p :=
    coefficientsOfCarrier_current_eq_normalized hP T c₀.Q cσ.Q H.contDiff hrank hphysical
      c₀.frame_eq htrans hσ.1 hσ.2 cσ.frame_eq row col c₀.forward c₀.inverse
      cσ.forward cσ.inverse hrm hcell angular high (ball_subset_ball hRphysical hp.1)
      (hVP' p.2 hp.2) (hnull (cσ.small_subset (hmapsW (x := p) hp)))
  obtain ⟨hnreg, hqreg, hbnd⟩ := hnorm σ ⟨hσ.1.le, hσ.2⟩
  refine ⟨hnreg.congr (fun p hp ↦ (hfields p hp).1),
    hqreg.congr (fun p hp ↦ (hfields p hp).2), ?_⟩
  intro m
  have hnEq : cNorm K m ac.normal = cNorm K m (an σ).normal := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro p hp
    filter_upwards [hO.mem_nhds (hKO hp)] with x hx
    exact (hfields x hx).1
  have hqEq : cNorm K m ac.reduced = cNorm K m (an σ).reduced := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro p hp
    filter_upwards [hO.mem_nhds (hKO hp)] with x hx
    exact (hfields x hx).2
  change cNorm K m ac.normal + cNorm K m ac.reduced ≤ A m
  rw [hnEq, hqEq]
  exact hbnd m

end JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
