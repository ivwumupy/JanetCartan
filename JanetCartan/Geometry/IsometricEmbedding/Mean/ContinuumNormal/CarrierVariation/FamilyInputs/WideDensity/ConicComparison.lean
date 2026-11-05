module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity.SourceComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.ConicConvergence

/-!
# Both ODE density labels after the actual conic inverse

The common conic geometry supplies inverse convergence, while the integral
extension supplies the ODE labels. Their composition retains both physical
positions and the original fixed-low density class. The density domain,
constants and thresholds precede the density. Consumer: `SeedAssembly` and
the full-amplitude construction in `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow
open ContinuumRow CanonicalCarrier PositiveReference NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol AmplitudeDifference.PrimitiveDensity

private theorem tendsto_composed_footpoint_sub
    {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set F} {Q : Set E} (hK : IsCompact K) (hQ : IsCompact Q)
    (f : ℝ → F → G) (g : ℝ → E → F) (m : ℕ)
    (hf₀ : ∀ p ∈ K, ContDiffAt ℝ ∞ (f 0) p)
    (hg₀ : ∀ p ∈ Q, ContDiffAt ℝ ∞ (g 0) p) (hr₀ : MapsTo (g 0) Q K)
    (hs : ∀ᶠ σ in 𝓝 (0 : ℝ), (∀ p ∈ K, ContDiffAt ℝ ∞ (f σ) p) ∧
      (∀ p ∈ Q, ContDiffAt ℝ ∞ (g σ) p) ∧ MapsTo (g σ) Q K)
    (hf : Tendsto (fun σ ↦ cNorm K m (f σ - f 0)) (𝓝 0) (𝓝 0))
    (hg : Tendsto (fun σ ↦ cNorm Q m (g σ - g 0)) (𝓝 0) (𝓝 0)) :
    Tendsto (fun σ ↦ cNorm Q m (f σ ∘ g σ - f 0 ∘ g 0)) (𝓝 0) (𝓝 0) := by
  let B := cNorm Q m (g 0) + 1
  have hB : 0 ≤ B := add_nonneg (cNorm_nonneg ..) zero_le_one
  obtain ⟨C, _hC, hb⟩ := exists_cNorm_comp_sub_le_fixed_reference hQ hK hf₀ m hB
  have hgb₀ : cNorm Q m (g 0) ≤ B := by dsimp [B]; linarith
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ cNorm_nonneg ..)
  · filter_upwards [hs, hg.eventually (gt_mem_nhds zero_lt_one)] with σ hσ hsmall
    have hgb : cNorm Q m (g σ) ≤ B := by
      have hh := cNorm_add_le_of_contDiffAt (r := m) hQ
        (fun p hp ↦ ((hσ.2.1 p hp).sub (hg₀ p hp)).of_le (by simp))
        (fun p hp ↦ (hg₀ p hp).of_le (by simp))
      simp only [Pi.add_def, sub_add_cancel] at hh
      change cNorm Q m (g σ) ≤ cNorm Q m (g σ - g 0) + cNorm Q m (g 0) at hh
      exact hh.trans (by dsimp [B]; linarith only [hsmall])
    exact hb (f σ) (g σ) (g 0) _ (add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..))
      hσ.1 hσ.2.1 hg₀ hσ.2.2 hr₀ hgb hgb₀
      (le_add_of_nonneg_right (cNorm_nonneg ..)) (le_add_of_nonneg_left (cNorm_nonneg ..))
  · simpa using (hf.add hg).const_mul C

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Both divided seed ODE labels after the genuine conic inverse have a
fixed compact range and converge in every primitive finite norm. These are
the actual primitive inputs to the weighted matrix comparison, prior to
choosing any density. The inverse limit follows from its equations and
augmented gap. Consumer: `SeedAssembly`, `WideDensity.CanonicalComparison`;
source: `app:ch_background:prop:bg-normalized`, `app:ch_background:eq:bg-Nsigma`. -/
theorem exists_source_conic_footpoint_primitives
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    {Z : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hend : ∀ side, MapsTo (densityEndpoint side) K (ball 0 R ×ˢ V))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) {e : ℝ} (he : 0 < e)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Z q.1) q.2) (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (Z σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Z σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)) :
    let g := fun t side p ↦ sourceDensityFootpointExtension T Y
      (t, densityEndpoint side (inverseCoordinates (u t) p))
    ∃ Rv > (0 : ℝ),
      (∀ m side, Tendsto (fun t ↦ cNorm Q m (g t side - g 0 side)) (𝓝 0) (𝓝 0)) ∧
      ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Icc (0 : ℝ) s, ∀ side,
        (∀ p ∈ Q, ContDiffAt ℝ ∞ (g σ side) p) ∧
        MapsTo (g σ side) Q (closedBall 0 Rv) := by
  let O := {p : InputVariables n | ∀ b, densityEndpoint b p ∈ ball (0 : Euclidean n) R ×ˢ V}
  have hO : IsOpen O := by
    have hh : O = ⋂ b : Bool, densityEndpoint b ⁻¹' (ball (0 : Euclidean n) R ×ˢ V) := by
      ext p; simp only [O, mem_ofPred_eq, mem_iInter, mem_preimage]
    rw [hh]
    exact isOpen_iInter_of_finite fun b ↦
      (isOpen_ball.prod hV).preimage (densityEndpoint_contDiff b).continuous
  have hKO : K ⊆ O := fun p hp b ↦ hend b hp
  let f := fun b (t : ℝ) (p : InputVariables n) ↦
    sourceDensityFootpointExtension T Y (t, densityEndpoint b p)
  have hf (b : Bool) : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦ f b q.1 q.2)
      (Ioo (-(1 / 4) : ℝ) (1 / 4) ×ˢ O) :=
    (sourceDensityFootpointExtension_contDiffOn T hV hY).comp
      (contDiffOn_fst.prodMk ((densityEndpoint_contDiff b).comp_contDiffOn contDiffOn_snd))
      (fun q hq ↦ ⟨hq.1, hq.2 b⟩)
  have hI : Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-(1 / 4) : ℝ) (1 / 4) := by
    intro t ht; constructor <;> linarith [ht.1, ht.2]
  have h0I : (0 : ℝ) ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) := by constructor <;> norm_num
  have h0e : (0 : ℝ) ∈ Ioo (-e) e := ⟨neg_neg_of_pos he, he⟩
  have hbound (b : Bool) := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    ((hf b).continuousOn.mono (prod_mono hI hKO))
  choose B hB using hbound
  let Rv := |B false| + |B true| + 1
  have hRv : 0 < Rv := by dsimp [Rv]; positivity
  have hrange (b) (t) (ht : t ∈ Icc (0 : ℝ) (1 / 8)) :
      MapsTo (f b t) K (closedBall 0 Rv) := by
    intro p hp
    rw [mem_closedBall, dist_zero_right]
    apply (hB b (t, p) ⟨ht, hp⟩).trans
    cases b <;> dsimp [Rv] <;> linarith [le_abs_self (B false), le_abs_self (B true),
      abs_nonneg (B false), abs_nonneg (B true)]
  let g := fun t b ↦ f b t ∘ inverseCoordinates (u t)
  have hsm (b) (t) (ht : t ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) :
      ∀ p ∈ K, ContDiffAt ℝ ∞ (f b t) p := by
    intro p hp
    exact ((hf b).comp (f := fun p : InputVariables n ↦ (t, p))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨ht, hp⟩)).contDiffAt
        (hO.mem_nhds (hKO hp))
  have husm (t) (ht : t ∈ Ioo (-e) e) :
      ∀ p ∈ Q, ContDiffAt ℝ ∞ (inverseCoordinates (u t)) p :=
    fun p hp ↦ (inverseCoordinates_contDiffOn (hfamily t ht).1).contDiffAt (hΩ.mem_nhds (hQΩ hp))
  have hgsm (b) (t) (ht : t ∈ Ioo (-(1 / 4) : ℝ) (1 / 4)) (hte : t ∈ Ioo (-e) e) :
      ∀ p ∈ Q, ContDiffAt ℝ ∞ (g t b) p :=
    fun p hp ↦ (hsm b t ht _ ((hfamily t hte).2.1 hp)).comp p (husm t hte p hp)
  have hlim (m : ℕ) (b) : Tendsto (fun t ↦ cNorm Q m (g t b - g 0 b)) (𝓝 0) (𝓝 0) := by
    apply tendsto_composed_footpoint_sub hK hQ (f b) (fun t ↦ inverseCoordinates (u t)) m
      (hsm b 0 h0I) (husm 0 h0e) (hfamily 0 h0e).2.1
    · filter_upwards [isOpen_Ioo.mem_nhds h0I, isOpen_Ioo.mem_nhds h0e] with t ht hte
      exact ⟨hsm b t ht, husm t hte, (hfamily t hte).2.1⟩
    · exact tendsto_cNorm_slice_sub isOpen_Ioo hO (hf b) hK hKO h0I m
    · exact tendsto_conic_inverse_sub_cNorm hK hconv hW hKW hQ hΩ hQΩ A he hjoint hfamily m
  let s := min (e / 2) (1 / 8)
  have hs : 0 < s := lt_min (half_pos he) (by norm_num)
  refine ⟨Rv, hRv, hlim, s, hs, (min_le_right _ _).trans (by norm_num), ?_⟩
  intro σ hσ side
  have hσe : σ ∈ Ioo (-e) e := ⟨by linarith [hσ.1],
    (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self he)⟩
  have hσI : σ ∈ Icc (0 : ℝ) (1 / 8) := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  exact ⟨hgsm side σ (hI hσI) hσe, (hrange side σ hσI).comp (hfamily σ hσe).2.1⟩

/-- The original two density factors converge uniformly over the fixed-low
class AFTER substitution of the genuine conic inverse. The inverse limit is
derived here from the original augmented map and its identities and gap;
the ODE footpoint is the separate integral extension of the seed scalar flow.
`NormDomains` and `MatchedSeedCoefficients` supply these premises on the same
objects. Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:prop:bg-normalized`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_source_conic_densityPair_comparison
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    {Z : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hend : ∀ side, MapsTo (densityEndpoint side) K (ball 0 R ×ˢ V))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) {e : ℝ} (he : 0 < e)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Z q.1) q.2) (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (Z σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Z σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)) :
    ∃ Rv > (0 : ℝ), ∀ m : ℕ, ∃ C > (0 : ℝ), ∀ ε > (0 : ℝ),
      ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ (d₀ : ℕ), m + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ q ∈ closedBall 0 Rv, ContDiffAt ℝ ∞ v q) → cNorm (closedBall 0 Rv) d₀ v ≤ 1 →
      let g := fun t side p ↦ sourceDensityFootpointExtension T Y
        (t, densityEndpoint side (inverseCoordinates (u t) p))
      cNorm Q m (densityPair v (g σ)) ≤ C ∧
      cNorm Q m (sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)) ≤ C ∧
      cNorm Q m (densityPair v (g σ) -
        sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)) < ε := by
  obtain ⟨Rv, hRv, hlim, s₀, hs₀, hs₀1, hregular⟩ :=
    exists_source_conic_footpoint_primitives T hV hY hK hconv hW hKW hQ hΩ hQΩ
      hend A he hjoint hfamily
  let g := fun t side p ↦ sourceDensityFootpointExtension T Y
    (t, densityEndpoint side (inverseCoordinates (u t) p))
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) s₀ := ⟨le_rfl, hs₀.le⟩
  refine ⟨Rv, hRv, ?_⟩
  intro m
  let M := cNorm Q m (g 0 false) + cNorm Q m (g 0 true) + 1
  have hM : 0 ≤ M := add_nonneg (add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)) zero_le_one
  have hnorm₀ (b) : cNorm Q m (g 0 b) + 1 ≤ M := by
    cases b <;> dsimp [M] <;> linarith [cNorm_nonneg Q m (g 0 false), cNorm_nonneg Q m (g 0 true)]
  obtain ⟨C, hC, hpair⟩ := exists_densityPair_sub_bound hQ
    (isCompact_closedBall (0 : Euclidean (n - 1) × Euclidean 3) Rv) (convex_closedBall _ _) m hM
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have htol : 0 < min 1 (ε / C) := lt_min zero_lt_one (div_pos hε hC)
  have hsmall := (hlim m false).add (hlim m true)
  obtain ⟨a, ha, hasmall⟩ := Metric.mem_nhds_iff.mp
    (hsmall.eventually (gt_mem_nhds (show (0 : ℝ) + 0 < min 1 (ε / C) by simpa only [add_zero] using htol)))
  let s := min (a / 2) s₀
  have hs : 0 < s := lt_min (half_pos ha) hs₀
  refine ⟨s, hs, (min_le_right _ _).trans hs₀1, ?_⟩
  intro σ hσ d₀ horder v hv hvm
  have hσs : σ ∈ Icc (0 : ℝ) s₀ := ⟨hσ.1.le, hσ.2.trans (min_le_right _ _)⟩
  let d := cNorm Q m (g σ false - g 0 false) + cNorm Q m (g σ true - g 0 true)
  have hd : 0 ≤ d := add_nonneg (cNorm_nonneg ..) (cNorm_nonneg ..)
  have hdiff : d < min 1 (ε / C) := by
    apply hasmall
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ.1]
    exact (hσ.2.trans (min_le_left _ _)).trans_lt (half_lt_self ha)
  have hbd (b) : cNorm Q m (g σ b - g 0 b) ≤ d := by
    cases b <;> dsimp [d] <;> linarith [cNorm_nonneg Q m (g σ false - g 0 false),
      cNorm_nonneg Q m (g σ true - g 0 true)]
  have hnorm (b) : cNorm Q m (g σ b) ≤ M := by
    have hh := cNorm_add_le_of_contDiffAt (r := m) hQ
      (fun p hp ↦ (((hregular σ hσs b).1 p hp).sub ((hregular 0 hzero b).1 p hp)).of_le (by simp))
      (fun p hp ↦ ((hregular 0 hzero b).1 p hp).of_le (by simp))
    simp only [Pi.add_def, sub_add_cancel] at hh
    change cNorm Q m (g σ b) ≤ cNorm Q m (g σ b - g 0 b) + cNorm Q m (g 0 b) at hh
    exact hh.trans (by linarith only [hbd b, hnorm₀ b, hdiff.trans_le (min_le_left _ _)])
  have hp := hpair v (g σ) (g 0) d hd hv ((cNorm_mono_order horder).trans hvm)
    (fun b ↦ (hregular σ hσs b).1) (fun b ↦ (hregular 0 hzero b).1)
    (fun b ↦ (hregular σ hσs b).2)
    (fun b ↦ (hregular 0 hzero b).2)
    hnorm (fun b ↦ (le_add_of_nonneg_right zero_le_one).trans (hnorm₀ b)) hbd
  refine ⟨hp.2.1, hp.2.2.1, hp.2.2.2.trans_lt ?_⟩
  exact (mul_lt_mul_of_pos_left (hdiff.trans_le (min_le_right _ _)) hC).trans_eq
    (mul_div_cancel₀ ε (ne_of_gt hC))

/-- Replace the divided extension by the literal positive-scale scalar ODE
inverse before comparing both density factors. Matching is the exact output
of `MatchedSeedCoefficients` for the same seed; it does not identify the ODE
footpoint with Hamilton transport. Consumer: `SeedAssembly` on its actual
conic domains (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_actual_source_conic_densityPair_comparison
    {Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3}
    {R : ℝ} (hR : 0 < R) {V : Set CarrierParameter} (hV : IsOpen V)
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {Z : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hend : ∀ side, MapsTo (densityEndpoint side) K (ball 0 R ×ˢ V))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) {e : ℝ} (he : 0 < e)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Z q.1) q.2) (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (Z σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient (Z σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)) :
    ∃ Rv > (0 : ℝ), ∀ m : ℕ, ∃ C > (0 : ℝ), ∀ ε > (0 : ℝ),
      ∃ s > (0 : ℝ), s ≤ 1 ∧ ∀ σ ∈ Ioc (0 : ℝ) s,
      ∀ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
      EqOn (densityFootpoint T Yσ) (densityFootpoint T (sourceTransportFlow Y σ))
        (ball 0 R ×ˢ V) →
      ∀ (d₀ : ℕ), m + 1 ≤ d₀ →
      ∀ (v : Euclidean (n - 1) × Euclidean 3 → ℝ),
      (∀ q ∈ closedBall 0 Rv, ContDiffAt ℝ ∞ v q) → cNorm (closedBall 0 Rv) d₀ v ≤ 1 →
      cNorm Q m (canonicalDensityPair T v Yσ ∘ inverseCoordinates (u σ)) ≤ C ∧
      cNorm Q m (sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)) ≤ C ∧
      cNorm Q m (canonicalDensityPair T v Yσ ∘ inverseCoordinates (u σ) -
        sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)) < ε := by
  obtain ⟨Rv, hRv, hcompare⟩ := exists_source_conic_densityPair_comparison T hV hY
    hK hconv hW hKW hQ hΩ hQΩ hend A he hjoint hfamily
  refine ⟨Rv, hRv, ?_⟩
  intro m
  obtain ⟨C, hC, htol⟩ := hcompare m
  refine ⟨C, hC, ?_⟩
  intro ε hε
  obtain ⟨s₀, hs₀, hs₀1, hs₀bound⟩ := htol ε hε
  refine ⟨min s₀ (e / 2), lt_min hs₀ (half_pos he), (min_le_left _ _).trans hs₀1, ?_⟩
  intro σ hσ Yσ hmatch d₀ horder v hv hvm
  have hσs : σ ∈ Ioc (0 : ℝ) s₀ := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hσ1 : σ ≤ 1 := hσs.2.trans hs₀1
  have hσe : σ ∈ Ioo (-e) e := ⟨by linarith [hσ.1],
    (hσ.2.trans (min_le_right _ _)).trans_lt (half_lt_self he)⟩
  have hp := hs₀bound σ hσs d₀ horder v hv hvm
  let O := {p : InputVariables n | ∀ b, densityEndpoint b p ∈ ball (0 : Euclidean n) R ×ˢ V}
  have hO : IsOpen O := by
    have hh : O = ⋂ b : Bool, densityEndpoint b ⁻¹' (ball (0 : Euclidean n) R ×ˢ V) := by
      ext p; simp only [O, mem_ofPred_eq, mem_iInter, mem_preimage]
    rw [hh]
    exact isOpen_iInter_of_finite fun b ↦
      (isOpen_ball.prod hV).preimage (densityEndpoint_contDiff b).continuous
  have heq (p : Euclidean n × CarrierParameter) (hpp : p ∈ ball (0 : Euclidean n) R ×ˢ V) :
      densityFootpoint T Yσ p = sourceDensityFootpointExtension T Y (σ, p) := by
    rw [hmatch hpp]
    apply (sourceDensityFootpointExtension_eq T hR hY hzero hparam hσ.1.ne' ?_).symm
    refine ⟨?_, hpp.2⟩
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hσ.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hσ1).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using hpp.1)
  have hevent (p) (hpp : p ∈ Q) :
      canonicalDensityPair T v Yσ ∘ inverseCoordinates (u σ) =ᶠ[𝓝 p]
        densityPair v (fun b q ↦ sourceDensityFootpointExtension T Y
          (σ, densityEndpoint b (inverseCoordinates (u σ) q))) := by
    have hu := (inverseCoordinates_contDiffOn (hfamily σ hσe).1).contDiffAt
      (hΩ.mem_nhds (hQΩ hpp))
    have hm : inverseCoordinates (u σ) p ∈ O := fun b ↦ hend b ((hfamily σ hσe).2.1 hpp)
    filter_upwards [hu.continuousAt.eventually (hO.mem_nhds hm)] with q hq
    change (1 + v (densityFootpoint T Yσ (densityEndpoint false (inverseCoordinates (u σ) q)))) *
      (1 + v (densityFootpoint T Yσ (densityEndpoint true (inverseCoordinates (u σ) q)))) = _
    rw [heq _ (hq false), heq _ (hq true)]
    rfl
  have hn := GeometricProfile.cNorm_eq_of_eventuallyEq hevent m
  have hd := GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun p hpp ↦ (hevent p hpp).sub (Filter.EventuallyEq.rfl
      (f := sourceDensityPairLimit T v Y ∘ inverseCoordinates (u 0)))) m
  exact ⟨hn.trans_le hp.1, hp.2.1, hd.trans_lt hp.2.2⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
