module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourcePrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.NonnegativePrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FullAmplitude

/-!
# Small full amplitudes for the supplied normalized source

The source coefficient, inverse, Jacobian and original-domain ODE producers
are applied before the full-amplitude difference estimate. A single cap is
chosen before the source scale and the permitted density. The supplied
conic domains and the complete fixed mask support are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity AmplitudeBound

/-- Bound a current primitive by its reference and one unit of its proved
finite-norm difference. Consumer: the actual source full-amplitude bound,
`app:ch_background:prop:bg-normalized`. -/
private theorem source_norm_le_reference_add_one
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} (hK : IsCompact K) {f f₀ : E → G} (s : ℕ)
    (hf : ∀ p ∈ K, ContDiffAt ℝ ∞ f p) (hf₀ : ∀ p ∈ K, ContDiffAt ℝ ∞ f₀ p)
    (hsmall : cNorm K s (f - f₀) ≤ 1) :
    cNorm K s f ≤ cNorm K s f₀ + 1 := by
  have h := cNorm_add_le_of_contDiffAt (r := s) hK
    (fun p hp ↦ ((hf p hp).sub (hf₀ p hp)).of_le (by simp))
    (fun p hp ↦ (hf₀ p hp).of_le (by simp))
  simp only [Pi.add_def, sub_add_cancel] at h
  change cNorm K s f ≤ cNorm K s (f - f₀) + cNorm K s f₀ at h
  linarith

/-- Apply the existing full-amplitude difference estimate to primitive
limits on fixed domains. This private proof step is instantiated below by
the concrete source producers; it introduces no public family interface.
Source: `app:ch_background:prop:bg-normalized`. -/
private theorem source_amplitude_tolerance_from_primitive_limits
    {n N : ℕ} (D : CoefficientNormCharts n)
    (a : ℝ → Coefficients n N) (J : ℝ → InputVariables n → ℝ)
    (u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Fwd : ℝ → InputVariables n → Variables n × Euclidean 2)
    (foot : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1) × Euclidean 3)
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (hzero : ∀ t, t ≤ 1 → h t = 0) (hone : ∀ t, 2 ≤ t → h t = 1)
    (hhigh : ∀ t, (a t).high = h)
    (hmeas : ∀ t, (a t).measurement = (a 0).measurement)
    (hang : ∀ t, (a t).angular = (a 0).angular)
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hL : IsCompact L) (hconv : Convex ℝ L)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖) (hrange : ∀ p ∈ K, D.Contains p)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (Zmask : Set (InputVariables n))
    {sourceCap upperCap M₀ : ℝ} (hcap : 0 < sourceCap)
    (hupperCap : sourceCap ≤ upperCap) (hM₀ : 0 < M₀)
    (hbase : D.Controls (2 * (n + 1) + 1) M₀ (M₀ + 1) 1 (a 0))
    (hcoeff : ∀ σ ∈ Icc (0 : ℝ) sourceCap, D.Controls (2 * (n + 1)) M₀ (M₀ + 1) 1 (a σ))
    (hreg : ∀ σ ∈ Icc (0 : ℝ) sourceCap, PrimitiveRegularity (a σ) (J σ) W)
    (hgeom : ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (∀ q ∈ Ω, Fwd σ (inverseCoordinates (u σ) q) = q) ∧
      (∀ p ∈ K, δ ≤ |J σ p|) ∧
      (closure (Fwd σ '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u σ (scaleFrequency t p.1, p.2) = ((u σ p).1, t • (u σ p).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) p)) = t * J σ (inverseCoordinates (u σ) p)) ∧
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (Fwd σ '' Zmask) ∪ closure (Fwd 0 '' Zmask) → (p, v) ∈ Q))
    (hmask : ∀ σ ∈ Icc (0 : ℝ) sourceCap, ∀ p ∈ W,
      (a σ).measurement p.1.1 ≠ 0 → (a σ).measurement p.1.2 ≠ 0 →
      (a σ).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hlabel : ∀ σ ∈ Icc (0 : ℝ) sourceCap, ∀ side,
      ContDiffOn ℝ ∞ (foot σ ∘ densityEndpoint side) W ∧
      MapsTo (foot σ ∘ densityEndpoint side) W L)
    (error : ℝ → ℝ) (hlim : Tendsto error (𝓝[≥] (0 : ℝ)) (𝓝 0)) (herror0 : error 0 = 0)
    (hparts : ∀ σ,
      0 ≤ error σ ∧
      cNorm D.field.carrier (2 * (n + 1)) ((a σ).normal - (a 0).normal) ≤ error σ ∧
      cNorm D.field.carrier (2 * (n + 1)) ((a σ).reduced - (a 0).reduced) ≤ error σ ∧
      cNorm K (2 * (n + 1)) (J σ - J 0) ≤ error σ ∧
      cNorm Q (2 * (n + 1)) (inverseCoordinates (u σ) - inverseCoordinates (u 0)) ≤ error σ ∧
      ∀ side, cNorm Q (2 * (n + 1))
        (foot σ ∘ densityEndpoint side ∘ inverseCoordinates (u σ) -
          foot 0 ∘ densityEndpoint side ∘ inverseCoordinates (u 0)) ≤ error σ) :
    ∀ tol > 0, ∃ cap > 0, cap ≤ upperCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ d₀ : ℕ, 2 * (n + 1) + 1 ≤ d₀ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ L, ContDiffAt ℝ ∞ v y) → cNorm L d₀ v ≤ 1 →
      (∀ y ∈ L, (1 / 2 : ℝ) ≤ 1 + v y) →
      let av := fun t ↦ {(a t) with normal := fun p ↦ Real.sqrt (1 + v (foot t p)) • (a t).normal p}
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude (av σ) (J σ) (u σ) Ω S ξ z i j -
          fullComplexMatrixAmplitude (av 0) (J 0) (u 0) Ω S ξ z i j) (2 * (n + 1)) tol ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude (av σ) (J σ) (u σ) Ω S ξ z i j -
          fullReflectedMatrixAmplitude (av 0) (J 0) (u 0) Ω S ξ z i j) (2 * (n + 1)) tol := by
  let μ := 2 * (n + 1)
  let g := fun σ side ↦ foot σ ∘ densityEndpoint side ∘ inverseCoordinates (u σ)
  let M := M₀ + (cNorm K μ (J 0) + 1) +
    (cNorm Q μ (inverseCoordinates (u 0)) + 1) +
    (cNorm Q μ (g 0 false) + 1) + (cNorm Q μ (g 0 true) + 1)
  have hMparts : M₀ ≤ M ∧ cNorm K μ (J 0) + 1 ≤ M ∧
      cNorm Q μ (inverseCoordinates (u 0)) + 1 ≤ M ∧
      ∀ side, cNorm Q μ (g 0 side) + 1 ≤ M := by
    have h₁ := cNorm_nonneg K μ (J 0)
    have h₂ := cNorm_nonneg Q μ (inverseCoordinates (u 0))
    have h₃ := cNorm_nonneg Q μ (g 0 false)
    have h₄ := cNorm_nonneg Q μ (g 0 true)
    dsimp only [M]
    refine ⟨by linarith only [h₁, h₂, h₃, h₄],
      by linarith only [hM₀, h₂, h₃, h₄], by linarith only [hM₀, h₁, h₃, h₄], ?_⟩
    intro side
    cases side <;> linarith only [hM₀, h₁, h₂, h₃, h₄]
  have hM : 0 ≤ M := hM₀.le.trans hMparts.1
  have upgrade {k : ℕ} {b : Coefficients n N} (hc : D.Controls k M₀ (M₀ + 1) 1 b) :
      D.Controls k M (M + 1) 1 b := by
    have up {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [NormedAddCommGroup G] [NormedSpace ℝ G]
        {Echart : PrimitiveNormChart E} {f : E → G}
        (hf : Echart.Controls k M₀ (M₀ + 1) 1 f) :
        Echart.Controls k M (M + 1) 1 f :=
      ⟨hf.smooth, hf.low.trans hMparts.1, hf.high.trans
        (mul_le_mul_of_nonneg_right (add_le_add hMparts.1 (le_refl (1 : ℝ))) zero_le_one)⟩
    exact ⟨up hc.measurement, up hc.angular, up hc.high, up hc.normal, up hc.reduced⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) sourceCap := ⟨le_rfl, hcap.le⟩
  have hJ₀M : cNorm K μ (J 0) ≤ M := by linarith only [hMparts.2.1]
  obtain ⟨Cfull, hCfull, hfull⟩ := exists_fullAmplitude_sqrtFootpoints_sub_bounds
    (N := N) D hh hzero hone hK hW hKW hQ hΩ hQΩ hL hconv hS hη hδ hfreq hrange
      (hreg 0 h0).jacobian (hgeom 0 h0).2.2.2.2.1 μ le_rfl hM hJ₀M hCupper hℓ hlow
  intro tol htol
  obtain ⟨t, ht, htSmall⟩ := Metric.mem_nhdsWithin_iff.mp
    (hlim.eventually (gt_mem_nhds (lt_min zero_lt_one (div_pos htol (by positivity : 0 < 4 * Cfull)))))
  let cap := min sourceCap (min 1 (t / 2))
  have hcapSource : cap ≤ sourceCap := min_le_left _ _
  refine ⟨cap, lt_min hcap (lt_min zero_lt_one (half_pos ht)), hcapSource.trans hupperCap,
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro σ hσ d₀ horder v hv hvm hpos
  have hsmall : error σ < min 1 (tol / (4 * Cfull)) := by
    apply htSmall
    refine ⟨?_, hσ.1.le⟩
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
    exact (hσ.2.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (half_lt_self ht)
  let scale : Fin 2 → ℝ := ![σ, 0]
  have hscale (i : Fin 2) : scale i ∈ Icc (0 : ℝ) sourceCap := by
    fin_cases i
    · exact ⟨hσ.1.le, hσ.2.trans hcapSource⟩
    · exact h0
  have heSmall (i : Fin 2) : error (scale i) ≤ 1 := by
    fin_cases i
    · exact hsmall.le.trans (min_le_left _ _)
    · exact herror0.trans_le zero_le_one
  have huAt (i : Fin 2) (p) (hp : p ∈ Q) :
      ContDiffAt ℝ ∞ (inverseCoordinates (u (scale i))) p :=
    (inverseCoordinates_contDiffOn (hgeom _ (hscale i)).1).contDiffAt (hΩ.mem_nhds (hQΩ hp))
  have hgAt (i : Fin 2) (side : Bool) (p) (hp : p ∈ Q) :
      ContDiffAt ℝ ∞ (g (scale i) side) p :=
    ((hlabel _ (hscale i) side).1.comp
      (inverseCoordinates_contDiffOn (hgeom _ (hscale i)).1)
      (hgeom _ (hscale i)).2.2.1).contDiffAt (hΩ.mem_nhds (hQΩ hp))
  have hJM (i : Fin 2) : cNorm K μ (J (scale i)) ≤ M :=
    (source_norm_le_reference_add_one hK μ
      (fun p hp ↦ (hreg _ (hscale i)).jacobian.contDiffAt (hW.mem_nhds (hKW hp)))
      (fun p hp ↦ (hreg 0 h0).jacobian.contDiffAt (hW.mem_nhds (hKW hp)))
      ((hparts _).2.2.2.1.trans (heSmall i))).trans hMparts.2.1
  have huM (i : Fin 2) : cNorm Q μ (inverseCoordinates (u (scale i))) ≤ M :=
    (source_norm_le_reference_add_one hQ μ (huAt i) (huAt 1)
      ((hparts _).2.2.2.2.1.trans (heSmall i))).trans hMparts.2.2.1
  have hgM (i : Fin 2) (side : Bool) : cNorm Q μ (g (scale i) side) ≤ M :=
    (source_norm_le_reference_add_one hQ μ (hgAt i side) (hgAt 1 side)
      (((hparts _).2.2.2.2.2 side).trans (heSmall i))).trans (hMparts.2.2.2 side)
  have hbnd := hfull (fun i ↦ a (scale i)) (fun i ↦ J (scale i))
    (fun i ↦ u (scale i)) (fun i ↦ Fwd (scale i)) (fun _ ↦ Zmask)
    (fun i ↦ foot (scale i)) (error σ) (hparts σ).1 rfl
    (fun i ↦ hhigh (scale i)) (hmeas σ) (hang σ)
    (upgrade (hcoeff σ (hscale 0))) (upgrade hbase) (fun i ↦ hreg _ (hscale i))
    (hgeom σ (hscale 0)).2.2.2.2.1 (hJM 0)
    (fun i ↦ (hgeom _ (hscale i)).1) (fun i ↦ (hgeom _ (hscale i)).2.1) huM
    (fun i ↦ (hgeom _ (hscale i)).2.2.1) (fun i ↦ (hgeom _ (hscale i)).2.2.2.1)
    (fun i ↦ hmask _ (hscale i)) (fun i ↦ (hgeom _ (hscale i)).2.2.2.2.2.1)
    (fun i ↦ (hgeom _ (hscale i)).2.2.2.2.2.2.1) hcone
    (fun i ↦ (hgeom _ (hscale i)).2.2.2.2.2.2.2.1)
    (fun i ↦ (hgeom _ (hscale i)).2.2.2.2.2.2.2.2.1)
    (hgeom σ (hscale 0)).2.2.2.2.2.2.2.2.2
    (fun i side ↦ (hlabel _ (hscale i) side).1)
    (fun i side ↦ (hlabel _ (hscale i) side).2) hgM
    (hparts σ).2.1 (hparts σ).2.2.1 (hparts σ).2.2.2.1 (hparts σ).2.2.2.2.1
    (hparts σ).2.2.2.2.2 d₀ horder v hv hvm hpos
  have hReflected : (4 * Cfull) * error σ ≤ tol := by
    exact ((mul_lt_mul_of_pos_left (hsmall.trans_le (min_le_right _ _))
      (by positivity : 0 < 4 * Cfull)).trans_eq (mul_div_cancel₀ tol (by positivity))).le
  have hComplex : Cfull * error σ ≤ tol := by
    have hd := (hparts σ).1
    nlinarith only [hCfull, hd, hReflected]
  intro av i j
  exact ⟨fun ξ is his z ↦ ((hbnd i j).1 ξ is his z).trans hComplex,
    fun ξ is his z ↦ ((hbnd i j).2 ξ is his z).trans hReflected⟩

/-- Nonnegative primitive differences are bounded by their common sum
(`app:ch_background:prop:bg-normalized`). -/
private theorem source_error_sum_bounds {a b c d e f g h : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g) (hh : 0 ≤ h) :
    let E := a + b + (c + d + e + f) + g + h
    0 ≤ E ∧ a ≤ E ∧ b ≤ E ∧ e ≤ E ∧ d ≤ E ∧ g ≤ E ∧ h ≤ E := by
  dsimp only
  repeat' constructor
  all_goals linarith only [ha, hb, hc, hd, he, hf, hg, hh]

/-- Primitive field controls and fixed-mask smoothness give the regularity
used by the source comparison (`app:ch_background:eq:bg-full-complex-amplitude`). -/
private theorem source_primitiveRegularity_of_controls
    {n N : ℕ} (D : CoefficientNormCharts n) {a : Coefficients n N}
    {s : ℕ} {M B H : ℝ} (hc : D.Controls s M B H a)
    (hm : ContDiff ℝ ∞ a.measurement) (ha : ContDiff ℝ ∞ a.angular)
    (hh : ContDiff ℝ ∞ a.high) {W : Set (InputVariables n)}
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    {J : InputVariables n → ℝ} (hJ : ContDiffOn ℝ ∞ J W)
    (hne : ∀ p ∈ W, J p ≠ 0) (hfreq : ∀ p ∈ W, p.2.2 ≠ 0) :
    PrimitiveRegularity a J W where
  leftMeasurement := hm.comp_contDiffOn contDiffOn_fst.fst
  rightMeasurement := hm.comp_contDiffOn contDiffOn_fst.snd
  angular := ha
  high := hh
  leftNormal := hc.normal.smooth.comp (densityEndpoint_contDiff false).contDiffOn (hend false)
  rightNormal := hc.normal.smooth.comp (densityEndpoint_contDiff true).contDiffOn (hend true)
  leftReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
    (densityEndpoint_contDiff false).contDiffOn (hend false)
  rightReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
    (densityEndpoint_contDiff true).contDiffOn (hend true)
  jacobian := hJ
  jacobian_ne_zero := hne
  covector_ne_zero := hfreq

/-- Apply the concrete normalized source primitive limits to the literal
full complex and reflected amplitudes through `μ = 2 * (n + 1)`. The only
comparison inputs are the supplied geometric inverse equations and gaps;
no coefficient, footpoint, amplitude or operator convergence is assumed.
The original `L/8` density ball, both ODE labels and all fixed masks are
unchanged. One positive source cap precedes every admitted scale and density.
Only nonnegative-scale inverse geometry is used, matching the actual selected
carrier family; the original through-zero interface is retained below.

The conic geometry is supplied by `both-normal-variation` on the same row;
its full-mask support clauses are not replaced by a smaller chart. Consumer:
normalized carrier-normal comparison and `SourceInverse` uniform coercivity.
Sources: `app:ch_background:prop:bg-normalized`, `bg-Nsigma`,
`bg-full-complex-amplitude`, `bg-real-symbol`, and
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_source_fullAmplitude_sqrtFootpoints_tolerance_nonneg
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2))
    (hh : ContDiff ℝ ∞ high)
    (hhighZero : ∀ r, r ≤ 1 → high r = 0) (hhighOne : ∀ r, 2 ≤ r → high r = 1)
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hrange : ∀ p ∈ K, D.Contains p)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ico (0 : ℝ) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T Q₀ σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p))
    {sourceCap : ℝ} (hsourceCap : 0 < sourceCap)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    (hfreqW : ∀ p ∈ W, p.2.2 ≠ 0)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, FixedCutoffs.physical hr 1 p.1.1 ≠ 0 →
      FixedCutoffs.physical hr 1 p.1.2 ≠ 0 →
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hglobal : ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      let Z := normalizedTransportPosition T Q₀
      let J := fun t ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) (Z t)
      ContDiffOn ℝ ∞ (J σ) W ∧ (∀ p ∈ W, J σ p ≠ 0) ∧
      MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (closure (augmentedTransportGradient (Z σ) '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u σ (scaleFrequency t p.1, p.2) = ((u σ p).1, t • (u σ p).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) p)) = t * J σ (inverseCoordinates (u σ) p)) ∧
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (augmentedTransportGradient (Z σ) '' Zmask) ∪
          closure (augmentedTransportGradient (Z 0) '' Zmask) → (p, v) ∈ Q)) :
    let μ := 2 * (n + 1)
    let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q₀ σ)
    let foot := fun σ p ↦ sourceDensityFootpointExtension T Y (σ, p)
    ∀ tol > 0, ∃ cap > 0, cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ d₀ : ℕ, μ + 1 ≤ d₀ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) d₀ v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let av := fun t ↦ {(a t) with normal := fun p ↦ Real.sqrt (1 + v (foot t p)) • (a t).normal p}
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude (av σ) (J σ) (u σ) Ω S ξ z i j -
          fullComplexMatrixAmplitude (av 0) (J 0) (u 0) Ω S ξ z i j) μ tol ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude (av σ) (J σ) (u σ) Ω S ξ z i j -
          fullReflectedMatrixAmplitude (av 0) (J 0) (u 0) Ω S ξ z i j) μ tol := by
  intro μ a J foot
  let Z := normalizedTransportPosition T Q₀
  let g := fun σ side ↦ foot σ ∘ densityEndpoint side ∘ inverseCoordinates (u σ)
  let error := fun σ ↦
    cNorm D.field.carrier μ ((a σ).normal - (a 0).normal) +
    cNorm D.field.carrier μ ((a σ).reduced - (a 0).reduced) +
    (cNorm K μ (augmentedTransportGradient (Z σ) - augmentedTransportGradient (Z 0)) +
      cNorm Q μ (inverseCoordinates (u σ) - inverseCoordinates (u 0)) +
      cNorm K μ (J σ - J 0) +
      cNorm K μ ((fun p ↦ (J σ p)⁻¹) - (fun p ↦ (J 0 p)⁻¹))) +
    cNorm Q μ (g σ false - g 0 false) + cNorm Q μ (g σ true - g 0 true)
  obtain ⟨M₀, hM₀, sc, hsc, _, hbase, hprimitive⟩ :=
    exists_normalizedCarrierData_coefficient_controls T Q₀ F row col Φ Y (fun _ ↦ 1)
      hr hcell angular high (FixedCutoffs.physical hr 1) hP hseed hF hi hrank
      hR hRT hRU hV hVP hb D hD (FixedCutoffs.physical hr 1).contDiff.contDiffOn
      ha.contDiffOn hh.contDiffOn μ
  obtain ⟨hn, hq⟩ := tendsto_normalizedCarrierData_coefficients_sub_cNorm
    T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high (FixedCutoffs.physical hr 1)
      hP hseed hF hi hrank hR hRT hRU hV hVP hb D
        (fun p hp ↦ (hD (D.field.ball_subset hp)).2) μ
  have hendK (side : Bool) : MapsTo (densityEndpoint side) K (ball 0 R ×ˢ V) :=
    fun p hp ↦ hD (hend side (hKW hp))
  have hj := tendsto_source_conic_primitives_nonneg
    T Q₀ hK hconv hW hKW hQ hΩ hQΩ A he hδ hjoint hfamily μ
  have hg := fun side ↦ tendsto_source_conic_footpoints_nonneg T Q₀ hV hY
    hK hconv hW hKW hQ hΩ hQΩ hendK A he hδ hjoint hfamily μ side
  have hlim : Tendsto error (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
    simpa only [error, a, J, Z, g, foot, Function.comp_def, add_zero] using
      ((((hn.add hq).mono_left nhdsWithin_le_nhds).add hj).add (hg false)).add (hg true)
  let sp := min sc (e / 2)
  have hsp : 0 < sp := lt_min hsc (half_pos he)
  have hspe : sp < e := (min_le_right _ _).trans_lt (half_lt_self he)
  change D.Controls (μ + 1) M₀ (M₀ + 1) 1 (a 0) at hbase

  have hparts (σ : ℝ) : 0 ≤ error σ ∧
      cNorm D.field.carrier μ ((a σ).normal - (a 0).normal) ≤ error σ ∧
      cNorm D.field.carrier μ ((a σ).reduced - (a 0).reduced) ≤ error σ ∧
      cNorm K μ (J σ - J 0) ≤ error σ ∧
      cNorm Q μ (inverseCoordinates (u σ) - inverseCoordinates (u 0)) ≤ error σ ∧
      ∀ side, cNorm Q μ (g σ side - g 0 side) ≤ error σ := by
    have h := source_error_sum_bounds
      (cNorm_nonneg D.field.carrier μ ((a σ).normal - (a 0).normal))
      (cNorm_nonneg D.field.carrier μ ((a σ).reduced - (a 0).reduced))
      (cNorm_nonneg K μ (augmentedTransportGradient (Z σ) - augmentedTransportGradient (Z 0)))
      (cNorm_nonneg Q μ (inverseCoordinates (u σ) - inverseCoordinates (u 0)))
      (cNorm_nonneg K μ (J σ - J 0))
      (cNorm_nonneg K μ ((fun p ↦ (J σ p)⁻¹) - (fun p ↦ (J 0 p)⁻¹)))
      (cNorm_nonneg Q μ (g σ false - g 0 false))
      (cNorm_nonneg Q μ (g σ true - g 0 true))
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
    intro side
    cases side
    · exact h.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2
  have herror0 : error 0 = 0 := by
    simp only [error, sub_self, cNorm_zero, add_zero]
  let cap₀ := min sp (min sourceCap (min s₀ (1 / 8)))
  have hcap₀ : 0 < cap₀ := lt_min hsp (lt_min hsourceCap (lt_min hs₀ (by norm_num)))
  have hcapSp : cap₀ ≤ sp := min_le_left _ _
  have hcapSource : cap₀ ≤ sourceCap := (min_le_right _ _).trans (min_le_left _ _)
  have hcapLabel : cap₀ ≤ min s₀ (1 / 8) := (min_le_right _ _).trans (min_le_right _ _)
  have hspOf (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) cap₀) : σ ∈ Icc (0 : ℝ) sp :=
    ⟨hσ.1, hσ.2.trans hcapSp⟩
  have heOf (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) cap₀) : σ ∈ Ico (0 : ℝ) e :=
    ⟨hσ.1, (hσ.2.trans hcapSp).trans_lt hspe⟩
  have hcoeff (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) cap₀) :=
    hprimitive σ ⟨hσ.1, (hspOf σ hσ).2.trans (min_le_left _ _)⟩
  have hgeom (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) cap₀) :=
    hglobal σ ⟨hσ.1, hσ.2.trans hcapSource⟩
  have hreg (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) cap₀) : PrimitiveRegularity (a σ) (J σ) W :=
    source_primitiveRegularity_of_controls D (hcoeff σ hσ)
      (FixedCutoffs.physical hr 1).contDiff ha hh hend (hgeom σ hσ).1 (hgeom σ hσ).2.1 hfreqW
  have hlabel (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) cap₀) (side : Bool) :
      ContDiffOn ℝ ∞ (foot σ ∘ densityEndpoint side) W ∧
      MapsTo (foot σ ∘ densityEndpoint side) W (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) := by
    have hl := source_footpoint_original_domain_regular T hR hV hY hzero hparam hs₀ hsource
      σ ⟨hσ.1, hσ.2.trans hcapLabel⟩
    exact ⟨hl.1.comp (densityEndpoint_contDiff side).contDiffOn (fun p hp ↦ hD (hend side hp)),
      (hl.2.comp (fun p hp ↦ hD (hend side hp))).mono_right
        (closedBall_subset_closedBall (by linarith only [hL] : L / 16 ≤ L / 8))⟩
  have hgeo : ∀ σ ∈ Icc (0 : ℝ) cap₀,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (∀ q ∈ Ω, augmentedTransportGradient (Z σ) (inverseCoordinates (u σ) q) = q) ∧
      (∀ p ∈ K, δ ≤ |J σ p|) ∧
      (closure (augmentedTransportGradient (Z σ) '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u σ (scaleFrequency t p.1, p.2) = ((u σ p).1, t • (u σ p).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) p)) = t * J σ (inverseCoordinates (u σ) p)) ∧
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (augmentedTransportGradient (Z σ) '' Zmask) ∪
          closure (augmentedTransportGradient (Z 0) '' Zmask) → (p, v) ∈ Q) := by
    dsimp only [J, Z]
    as_aux_lemma =>
      exact (fun σ hσ ↦ ⟨(hfamily σ (heOf σ hσ)).1, (hfamily σ (heOf σ hσ)).2.1,
        (hgeom σ hσ).2.2.1,
        augmentedTransportGradient_inverseCoordinates (Z σ) (u σ) (hfamily σ (heOf σ hσ)).2.2.1,
        fun p hp ↦ ((hfamily σ (heOf σ hσ)).2.2.2.2 p hp).trans (le_abs_self _),
        (hgeom σ hσ).2.2.2.1, (hgeom σ hσ).2.2.2.2.1,
        (hgeom σ hσ).2.2.2.2.2.1, (hgeom σ hσ).2.2.2.2.2.2.1, (hgeom σ hσ).2.2.2.2.2.2.2⟩)
  have hhighEq : ∀ σ, (a σ).high = high := by
    dsimp only [a]
    as_aux_lemma => exact fun _ ↦ rfl
  have hmeasEq : ∀ σ, (a σ).measurement = (a 0).measurement := by
    dsimp only [a]
    as_aux_lemma => exact fun _ ↦ rfl
  have hangEq : ∀ σ, (a σ).angular = (a 0).angular := by
    dsimp only [a]
    as_aux_lemma => exact fun _ ↦ rfl
  have hmaskAll : ∀ σ ∈ Icc (0 : ℝ) cap₀, ∀ p ∈ W,
      (a σ).measurement p.1.1 ≠ 0 → (a σ).measurement p.1.2 ≠ 0 →
      (a σ).angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask := by
    dsimp only [a]
    as_aux_lemma => exact fun _ _ ↦ hmask
  exact source_amplitude_tolerance_from_primitive_limits D a J u
    (fun σ ↦ augmentedTransportGradient (Z σ)) foot high hh hhighZero hhighOne
    hhighEq hmeasEq hangEq hK hW hKW hQ hΩ hQΩ
    (isCompact_closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (convex_closedBall _ _)
    hS hη hδ hfreq hrange hCupper hℓ hlow Zmask hcap₀ hcapSource hM₀ hbase hcoeff hreg
    hgeo
    hmaskAll hcone hlabel error hlim herror0 hparts

/-- The original through-zero interface for the full-amplitude comparison.
It specializes `exists_source_fullAmplitude_sqrtFootpoints_tolerance_nonneg`
without changing any supplied constant, inverse, mask or density domain.
Sources: `app:ch_background:prop:bg-normalized`, `bg-full-complex-amplitude`
and `bg-real-symbol`. -/
theorem exists_source_fullAmplitude_sqrtFootpoints_tolerance
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2))
    (hh : ContDiff ℝ ∞ high)
    (hhighZero : ∀ r, r ≤ 1 → high r = 0) (hhighOne : ∀ r, 2 ≤ r → high r = 1)
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hrange : ∀ p ∈ K, D.Contains p)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T Q₀ σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p))
    {sourceCap : ℝ} (hsourceCap : 0 < sourceCap)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    (hfreqW : ∀ p ∈ W, p.2.2 ≠ 0)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, FixedCutoffs.physical hr 1 p.1.1 ≠ 0 →
      FixedCutoffs.physical hr 1 p.1.2 ≠ 0 →
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hglobal : ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      let Z := normalizedTransportPosition T Q₀
      let J := fun t ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) (Z t)
      ContDiffOn ℝ ∞ (J σ) W ∧ (∀ p ∈ W, J σ p ≠ 0) ∧
      MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (closure (augmentedTransportGradient (Z σ) '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u σ (scaleFrequency t p.1, p.2) = ((u σ p).1, t • (u σ p).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) p)) = t * J σ (inverseCoordinates (u σ) p)) ∧
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (augmentedTransportGradient (Z σ) '' Zmask) ∪
          closure (augmentedTransportGradient (Z 0) '' Zmask) → (p, v) ∈ Q)) :
    let μ := 2 * (n + 1)
    let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q₀ σ)
    let foot := fun σ p ↦ sourceDensityFootpointExtension T Y (σ, p)
    ∀ tol > 0, ∃ cap > 0, cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ d₀ : ℕ, μ + 1 ≤ d₀ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) d₀ v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let av := fun t ↦ {(a t) with normal := fun p ↦ Real.sqrt (1 + v (foot t p)) • (a t).normal p}
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude (av σ) (J σ) (u σ) Ω S ξ z i j -
          fullComplexMatrixAmplitude (av 0) (J 0) (u 0) Ω S ξ z i j) μ tol ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude (av σ) (J σ) (u σ) Ω S ξ z i j -
          fullReflectedMatrixAmplitude (av 0) (J 0) (u 0) Ω S ξ z i j) μ tol := by
  exact exists_source_fullAmplitude_sqrtFootpoints_tolerance_nonneg
    T Q₀ F row col Φ Y hr hcell angular high hP hseed hF hi hrank
    hR hRT hRU hV hVP hb hY hzero hparam hL hs₀ hsource D hD ha hh hhighZero hhighOne
    hK hconv hW hKW hQ hΩ hQΩ hrange A he hδ hjoint
    (fun σ hσ ↦ hfamily σ ⟨(neg_neg_of_pos he).trans_le hσ.1, hσ.2⟩)
    hsourceCap hend hfreqW hη hfreq Zmask hmask hS hCupper hℓ hlow hcone hglobal

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
