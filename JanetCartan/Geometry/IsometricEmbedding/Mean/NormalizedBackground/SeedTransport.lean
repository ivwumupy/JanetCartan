module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Adapted
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.UniformFlow

/-!
# Constructing the unit transport of a fixed flat seed

For `app:ch_background:prop:bg-normalized`, the primitive minor threshold is
chosen from the retained patch before the seed scale. Source dilation meets
that threshold. The actual smooth direction then supplies its own finite
compact low norm, and the existing adapted-flow and positive-transport
constructors produce the unit-initial scalar. No metric/normal gap or high
norm is assumed uniform before this seed is fixed.

This constructs local transports over every original carrier label. Finite
refinement, fixed carrier weights, source rescaling of these same scalars and
the continuum estimates remain with the normalized-background assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude

/-- Construct the actual unit-initial null scalars for a finite retained primary
patch family of an actual flat seed, with one source scale preceding all derivative
orders. All coefficient and ODE hypotheses are discharged. The output uses
the literal `carrierScalarAmplitude`, the retained adapted section and the
original Euclidean carrier labels (`app:ch_background:prop:bg-normalized`). -/
theorem exists_finite_flat_seed_unit_transports {n : ℕ} {A : Type} [Fintype A]
    (hn : 2 ≤ n) (G₀ : FlatReference n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (hUG : U ⊆ G₀.domain.chart n)
    {P : A → Patch n} {c₀ C₀ : A → ℝ} (hP : ∀ a, (P a).IsValid (c₀ a) (C₀ a))
    (T : (a : A) → PatchQuantitativeFamily (P a) U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ a, closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius ⊆ K)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ θ : ℝ, 0 < θ ∧ θ < cap ∧ θ ≤ 1 ∧
      ∃ G : FlatReference n, G.domain = G₀.domain ∧ G.map = sourceDilation G₀.map θ ∧
      ∃ hQ : ContDiffOn ℝ ∞ (projectedStress G.map) U,
      ∃ hlow : ∀ a, cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (projectedStress G.map - fun _ ↦ cubeStress n) < (T a).family.threshold,
      ∀ a : A,
      let T := T a
      let P := P a
      let Q := ⟨projectedStress G.map, hQ, hlow a⟩
      let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
      ∀ z ∈ parameterCube P.radius,
        ∃ row col : Fin n, ∃ τ R : ℝ, 0 < τ ∧ 0 < R ∧
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen D ∧
          Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
          C ⁻¹' D ⊆ U ×ˢ parameterInterior (3 * P.radius / 2) ∧
          D ⊆ Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4) ∧
          ContDiffOn ℝ ∞ Φ (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
          ContDiffOn ℝ ∞ Y D ∧
          MapsTo (fun q ↦ (q.1, Φ q))
            (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) D ∧
          MapsTo (fun q ↦ (q.1, Y q)) D
            (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), Φ (0, p) = p) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            Y (t, Φ (t, p)) = p) ∧
          (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            (Φ (t, p)).2 = p.2) ∧
          (∀ q ∈ D, (Y q).2 = q.2.2) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            HasDerivAt (fun s ↦ Φ (s, p))
              ((adaptedCoordinates T.data.adapted
                (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
          let α := carrierScalarAmplitude T Q G.map row col Φ Y (fun _ ↦ 1)
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8),
            α (T.data.adapted.embedding p.1, p.2) = 1) ∧
          (∀ w ∈ C ⁻¹' D, 0 < α w ∧ α w • carrierNullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
              carrierTransportPotential T Q G.map row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
              (fun j ↦ (α w • carrierNullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, carrierConullvector T Q row w ⬝ᵥ reducedOperator G.map Q.1
            (fun x ↦ α (x, w.2) • carrierNullvector T Q col (x, w.2)) w.1 = 0) ∧
          ContDiffOn ℝ ∞ (carrierNullvector T Q col) (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (carrierTransportPotential T Q G.map row col) (C ⁻¹' D) ∧
          (∀ w ∈ C ⁻¹' D, carrierAdaptedDenominator T Q row col w ≠ 0) := by
  classical
  choose δ μ κ hδ _hμ _hκ V hV hcover hcoeff using
    fun a ↦ exists_projected_null_coefficients (N := embeddingDimension n)
      hn (hP a) (T a) hK hKU (hball a)
  obtain ⟨d, hd, hdδ⟩ := (finite_range δ).isCompact.exists_forall_le' continuousOn_id
    (by rintro x ⟨a, rfl⟩; exact hδ a)
  obtain ⟨_, _, _, θ₀, hθ₀, hθ₀1, _, _, hbounds⟩ :=
    exists_projectedStress_dilation_bounds G₀ hK
  obtain ⟨L, hL, hbound⟩ := hbounds 6
  let θ := min θ₀ (min (cap / 2) (d / (28 * L)))
  have hθ : 0 < θ := lt_min hθ₀ (lt_min (half_pos hcap) (by positivity))
  have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
  have hθ1 : θ ≤ 1 := hθθ₀.trans hθ₀1
  have hθcap : θ < cap :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hcap)
  have hsmall : 7 * (L * θ) < d := by
    have hh : θ ≤ d / (28 * L) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (show 0 < 28 * L by positivity)).mp hh
    nlinarith
  let G := sourceDilationReference G₀ hθ hθ1
  have hF : ContDiffOn ℝ ∞ G.map U := G.contDiff.contDiffOn
  have hi : IsImmersionOn G.map U :=
    isImmersionOn_of_isIsometricOn (g := fun _ ↦ 1) (fun _ _ ↦ Matrix.PosDef.one)
      (fun x _ ↦ G.inducedMetric_eq_one x)
  have hrank : HasFullNormalRankOn G.map U := fun x hx ↦ G.fullNormalRank x (hUG hx)
  have hframe : ContDiffOn ℝ ∞ (projectedStress G.map) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hclose : cNorm K 6 (projectedStress G.map - fun _ ↦ cubeStress n) < d := by
    have hh := frame_cNorm_le_of_componentwise hK
      (fun x hx ↦ ((hframe.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le
        (show (6 : ℕ∞ω) ≤ ∞ by simp))
      (mul_nonneg hL.le hθ.le) (hbound θ ⟨hθ, hθθ₀⟩)
    exact hh.trans_lt (by convert hsmall using 1; norm_num)
  choose hlow hc using fun a ↦
    hcoeff a G.map hF hi hrank (hclose.trans_le (hdδ _ ⟨a, rfl⟩))
  refine ⟨θ, hθ, hθcap, hθ1, G, rfl, rfl, hframe, hlow, ?_⟩
  intro a
  let T := T a
  let P := P a
  have hP := hP a
  have hball := hball a
  have hV := hV a
  have hcover := hcover a
  have hc := hc a
  let V := V a
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress G.map, hframe, hlow a⟩
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  dsimp only
  intro z hz
  obtain ⟨row, hr⟩ := mem_iUnion.mp (hcover hz)
  obtain ⟨col, hzV⟩ := mem_iUnion.mp hr
  let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V row col)
  have hΩ : IsOpen Ω := (isOpen_ball.inter isOpen_interior).prod
    ((isOpen_parameterInterior _).inter (hV row col))
  have h0K : (0 : Euclidean n) ∈ interior K :=
    mem_interior.mpr ⟨ball 0 T.data.localReference.stateRadius,
      ball_subset_closedBall.trans hball, isOpen_ball,
      mem_ball_self T.data.localReference.stateRadius_pos⟩
  have hzΩ : ((0 : Euclidean n), z) ∈ Ω :=
    ⟨⟨mem_ball_self T.physicalRadius_pos, h0K⟩,
      ⟨fun i ↦ (hz i).trans_lt (by linarith [hP.1]), hzV⟩⟩
  obtain ⟨a, R, _, hR, hwork, _, hbuffer⟩ := exists_adapted_coefficient_ball T hΩ z hzΩ
  obtain ⟨hk, _, hd, hp, hnull⟩ := hc row col
  let M := cNorm (closedBall ((0 : Euclidean n), z) a) 1 (carrierTransportDirection T Q row col)
  have hM : 0 ≤ M := cNorm_nonneg _ _ _
  obtain ⟨_, _, hflow⟩ := exists_uniform_actual_flow_chart T hΩ
    (isCompact_closedBall _ _) hwork hM hR hbuffer
  obtain ⟨D, Φ, Y, hτ, hD, hsmallD, hbigD, _, hΦ, hY, hdomain, hΦD, hYU,
    hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity, _, _, _⟩ := hflow Q row col hd (le_refl M)
  let τ := existenceTime R (liftedLowBound T M) / 4
  have hphys : C ⁻¹' D ⊆ Ω := by
    intro w hw
    have hh := hdomain hw
    change C.symm (C w) ∈ Ω at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  have hsym (w) (hw : w ∈ C ⁻¹' D) (i) : (Q.1 w.1 i).IsSymm :=
    (projectedStress_mem_stressSpace (G.contDiff.contDiffAt.of_le (by simp))
      (hrank w.1 (hKU (interior_subset (hphys hw).1.2))) i).1
  obtain ⟨hα, hb, hinit, hpos, _, hscalar, hsymbol, hreduce⟩ :=
    carrierScalarAmplitude_spec T Q G.map row col isOpen_Ioo ordConnected_Ioo
      isOpen_ball hD ⟨neg_neg_of_pos hτ, hτ⟩ (hk.mono hphys) (hp.mono hphys) hsym
      (fun w hw ↦ (hnull w (hphys hw)).2.2.2.2.2.1)
      (fun w hw ↦ (hnull w (hphys hw)).2.2.1)
      (r := fun _ ↦ 1) contDiffOn_const (fun _ _ ↦ zero_lt_one)
      hΦ hΦD hΦ₀ (hY.mono hbigD) hYU hYΦ hΦY hvelocity
  refine ⟨row, col, τ, R, hτ, hR, D, Φ, Y, hD, hsmallD, ?_, hbigD, hΦ,
    hY.mono hbigD, hΦD, hYU, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hα, hb, hinit, ?_, hscalar, hsymbol, hreduce, hk.mono hphys, hd.mono hphys,
    hp.mono hphys, fun w hw ↦ (hnull w (hphys hw)).2.2.2.2.2.1⟩
  · intro w hw
    exact ⟨hKU (interior_subset (hphys hw).1.2), (hphys hw).2.1⟩
  · intro w hw
    exact ⟨hpos w hw, smul_ne_zero (hpos w hw).ne' (hnull w (hphys hw)).1⟩

end JanetCartan.NormalizedBackground
