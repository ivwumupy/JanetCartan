module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedRefinement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry

/-!
# The normalized mean of the constructed finite seed family

This instantiates the principal-normal and compact-integral estimates using the
actual unit transports constructed from the retained Hamilton family. Carrier
weights and Lebesgue measure are unchanged under source dilation. The geometric
and transport inputs are conclusions of the seed construction, not additional
analytic assumptions (`app:ch_background:prop:bg-normalized`).

The continuum row, its coercivity, its inverse and density estimates remain
separate obligations. The phase here is the divided retained seed phase;
matching independently selected positive-scale charts remains with
`CarrierVariation.FamilyInputs.SourceMatching`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.NormalizedBackground
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude SourceGeometry

/-- Construct a finite seed family and prove its positive-scale principal mean
is the normalized pullback, has constant positive-semidefinite limit, and varies
by `O(ρ)` in every fixed `C^s` norm. Every seed geometry and amplitude hypothesis
of `exists_common_source_geometry_bounds` is discharged for these same actual
objects. All buffers precede derivative order, targets and histories
(`app:ch_background:eq:bg-Hsigma`). -/
theorem exists_flat_seed_normalized_mean {n : ℕ} {A : Type} [Fintype A]
    (hn : 5 ≤ n) (G₀ : FlatReference n)
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
      ∃ centers : (a : A) → Finset (parameterCube (P a).radius),
      ∃ radius : (a : A) → centers a → ℝ,
        (∀ a j, 0 < radius a j) ∧
        (∀ a, parameterCube (P a).radius ⊆ ⋃ j : centers a,
          ball j.1.1 (radius a j / 4)) ∧
        ∃ ε : ℝ, 0 < ε ∧ ball (0 : Euclidean n) (2 * ε) ⊆ G.domain.chart n ∧
        (∀ a, 2 * ε < (T a).physicalRadius) ∧
        let I := (a : A) × centers a
        let Q := fun a ↦ (⟨projectedStress G.map, hQ, hlow a⟩ :
          {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
            cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
              (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
        let S := fun (j : I) (p : Euclidean n × Euclidean 3) ↦ (T j.1).carrier (Q j.1) p.1 p.2
        let ξ := fun (j : I) (p : Euclidean n × Euclidean 3) ↦
          (T j.1).carrierGradient (Q j.1) p.1 p.2
        let V := fun j : I ↦ ball j.2.1.1 (radius j.1 j.2 / 2)
        let Kc := fun j : I ↦ closedBall j.2.1.1 (radius j.1 j.2 / 4)
        ∃ b : I → Euclidean n × Euclidean 3 → Euclidean n,
        (∀ j : I,
        let T := T j.1
        let P := P j.1
        let Q := Q j.1
        let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
        let z := j.2.1.1
        let r := radius j.1 j.2
        ∃ row col : Fin n, ∃ τ R : ℝ, 0 < τ ∧ 0 < R ∧
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          b j = (fun w ↦ carrierScalarAmplitude T Q G.map row col Φ Y (fun _ ↦ 1) w •
            carrierNullvector T Q col w) ∧
          (ball (0 : Euclidean n) (2 * ε) ×ˢ ball z (r / 2) ⊆ C ⁻¹' D) ∧
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
          (∀ w ∈ C ⁻¹' D, carrierAdaptedDenominator T Q row col w ≠ 0)) ∧
        ∀ (w : I → Euclidean 3 → ℝ),
          (∀ j, ContDiffOn ℝ ∞ (w j) (V j)) → (∀ j z, 0 ≤ w j z) →
          (∀ j z, z ∉ Kc j → w j z = 0) →
          ∀ (D : Set (Euclidean n)), IsCompact D →
          let μ := fun _ : I ↦ (volume : Measure (Euclidean 3))
          let ν := fun j p ↦ LeadingWave.principalNormal
            (AmbientResponse.canonicalNormalCompletion G.map p.1) (ξ j p) (b j p)
          let J := fun j q ↦ (normalizedPullback (b j) q,
            normalizedPullback (ξ j) q, normalizedPullback (ν j) q)
          ∃ B : Set (Euclidean n), IsOpen B ∧ D ⊆ B ∧ ∃ ρ₀ > 0, ρ₀ ≤ 1 ∧
            (∀ j, ContDiffOn ℝ ∞ (J j) (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V j) ∧
              ContDiffOn ℝ ∞ (sourcePhaseExtension (S j))
                (Ioo (-2 * ρ₀) (2 * ρ₀) ×ˢ B ×ˢ V j)) ∧
            (∃ c > 0, ∀ j, ∀ ρ ∈ Icc (0 : ℝ) ρ₀, ∀ x ∈ D, ∀ z ∈ Kc j,
              c ≤ ‖normalizedPullback (ν j) (ρ, (x, z))‖) ∧
            (carrierMean μ w ν ξ 0).PosSemidef ∧
            (∀ ρ ∈ Ioc (0 : ℝ) ρ₀, ∀ x ∈ B,
              sourcePrincipalMean G.map μ w S b ρ x = normalizedCarrierMean μ w ν ξ ρ x ∧
              PositiveBackground.referenceMeanResidual (sourceDilation G.map ρ)
                (carrierMean μ w ν ξ 0) (sourcePrincipalMean G.map μ w S b ρ) x =
                sourcePrincipalMean G.map μ w S b ρ x - carrierMean μ w ν ξ 0 ∧
              ∀ j z, z ∈ V j → sourcePhase (S j) ρ (x, z) =
                sourcePhaseExtension (S j) (ρ, (x, z))) ∧
            ∀ s : ℕ, ∃ C > 0, ∀ ρ ∈ Ioc (0 : ℝ) ρ₀,
              cNorm D s (fun x ↦ sourcePrincipalMean G.map μ w S b ρ x -
                carrierMean μ w ν ξ 0) ≤ C * ρ ∧
              ∀ j x, x ∈ D → ∀ z ∈ Kc j,
                ‖iteratedFDeriv ℝ s (J j) (ρ, (x, z))‖ ≤ C := by
  classical
  obtain ⟨θ, hθ, hθcap, hθ1, G, hdomain, hmap, hQ, hlow, centers, radius,
    hradius, hcover, ε, hε, hεG, hεT, hlocal⟩ :=
    exists_refined_flat_seed_unit_transports (by omega) G₀ hUG hP T hK hKU hball hcap
  let I := (a : A) × centers a
  let Q a := (⟨projectedStress G.map, hQ, hlow a⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T a).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T a).family.threshold})
  let S := fun (j : I) (p : Euclidean n × Euclidean 3) ↦ (T j.1).carrier (Q j.1) p.1 p.2
  let ξ := fun (j : I) (p : Euclidean n × Euclidean 3) ↦
    (T j.1).carrierGradient (Q j.1) p.1 p.2
  let V := fun j : I ↦ ball j.2.1.1 (radius j.1 j.2 / 2)
  let Kc := fun j : I ↦ closedBall j.2.1.1 (radius j.1 j.2 / 4)
  let Ω := ball (0 : Euclidean n) (2 * ε)
  have h0 : (0 : Euclidean n) ∈ Ω := mem_ball_self (by positivity)
  choose row col τ R hτ hR Dflow Φ Y hbuffer hspec using fun j : I ↦ hlocal j.1 j.2
  let α := fun (j : I) ↦ carrierScalarAmplitude (T j.1) (Q j.1) G.map (row j) (col j)
    (Φ j) (Y j) (fun _ ↦ 1)
  let b := fun (j : I) (p : Euclidean n × Euclidean 3) ↦
    α j p • carrierNullvector (T j.1) (Q j.1) (col j) p
  have hcarrier (j : I) : V j ⊆ parameterInterior (2 * (P j.1).radius) := by
    intro z hz
    have hh : ((0 : Euclidean n), z) ∈ U ×ˢ parameterInterior (3 * (P j.1).radius / 2) :=
      (hspec j).2.2.1 (hbuffer j ⟨h0, hz⟩)
    exact fun k ↦ (hh.2 k).trans (by linarith [(hP j.1).1])
  have hξ (j : I) : ContDiffOn ℝ ∞ (ξ j) (Ω ×ˢ V j) :=
    ((T j.1).carrierGradient_smooth (hP j.1) (Q j.1)).mono
      (fun p hp ↦ ⟨ball_subset_ball (hεT j.1).le hp.1, hcarrier j hp.2⟩)
  have hS (j : I) : ContDiffOn ℝ ∞ (S j) (Ω ×ˢ V j) :=
    ((T j.1).carrier_smooth (hP j.1) (Q j.1)).mono
      (fun p hp ↦ ⟨ball_subset_ball (hεT j.1).le hp.1, hcarrier j hp.2⟩)
  have hKc (j : I) : IsCompact (Kc j) := isCompact_closedBall _ _
  have hKV (j : I) : Kc j ⊆ V j := closedBall_subset_ball (by
    have := hradius j.1 j.2
    linarith)
  have hb (j : I) : ContDiffOn ℝ ∞ (b j) (Ω ×ˢ V j) := by
    rcases hspec j with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩
    exact hb.mono (hbuffer j)
  have hb0 (j : I) (z) (hz : z ∈ Kc j) : b j (0, z) ≠ 0 := by
    rcases hspec j with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩
    exact (hp (0, z) (hbuffer j ⟨h0, hKV j hz⟩)).2
  have hnull (j : I) (z) (hz : z ∈ Kc j) :
      pencil (projectedStress G.map 0) (ξ j (0, z)) *ᵥ (fun k ↦ b j (0, z) k) = 0 := by
    rcases hspec j with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _⟩
    exact hn (0, z) (hbuffer j ⟨h0, hKV j hz⟩)
  have hξ0 (j : I) (z) (hz : z ∈ Kc j) : ξ j (0, z) ≠ 0 :=
    retained_carrierGradient_ne_zero (T j.1) (Q j.1)
      (mem_ball_self (T j.1).physicalRadius_pos) (hcarrier j (hKV j hz))
  refine ⟨θ, hθ, hθcap, hθ1, G, hdomain, hmap, hQ, hlow, centers, radius,
    hradius, hcover, ε, hε, hεG, hεT, b, ?_, ?_⟩
  · intro j
    exact ⟨row j, col j, τ j, R j, hτ j, hR j, Dflow j, Φ j, Y j,
      rfl, hbuffer j, hspec j⟩
  intro w hw hwpos hsupp D hD
  let μ := fun _ : I ↦ (volume : Measure (Euclidean 3))
  let ν := fun (j : I) (p : Euclidean n × Euclidean 3) ↦ LeadingWave.principalNormal
    (AmbientResponse.canonicalNormalCompletion G.map p.1) (ξ j p) (b j p)
  let J := fun (j : I) q ↦ (normalizedPullback (b j) q,
    normalizedPullback (ξ j) q, normalizedPullback (ν j) q)
  have (j : I) : IsFiniteMeasure ((μ j).restrict (Kc j)) :=
    isFiniteMeasure_restrict.mpr (hKc j).measure_lt_top.ne
  have hrank : HasFullNormalRankOn G.map Ω := fun x hx ↦ G.fullNormalRank x (hεG hx)
  obtain ⟨B, hB, hDB, ρ₀, hρ₀, hρ₀1, hseg, hJ, hlo, hH0, hres, hbound⟩ :=
    exists_common_source_geometry_bounds isOpen_ball h0 hD G.contDiff
      (fun x _ ↦ G.inducedMetric_eq_one x) hrank (flatReference_projectedStress_basis hn G)
      μ Kc V (fun _ ↦ isOpen_ball) hKc hKV w ξ b hw hwpos hsupp hξ hb hnull hξ0 hb0
  have hphase (j : I) := sourcePhaseExtension_joint_bounds isOpen_ball hB isOpen_ball
    hρ₀ hD hDB (hKc j) (hKV j) (hS j) hseg
  have hmaps (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) ρ₀) {x : Euclidean n} (hx : x ∈ B) :
      ρ • x ∈ Ω := by
    simpa only [one_mul] using hseg ρ ⟨by linarith [hρ.1], by linarith [hρ.2]⟩ x hx 1
      ⟨by norm_num, by norm_num⟩
  have heq (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) ρ₀) {x : Euclidean n} (hx : x ∈ B) :
      sourcePrincipalMean G.map μ w S b ρ x = normalizedCarrierMean μ w ν ξ ρ x :=
    sourcePrincipalMean_eq_normalizedCarrierMean isOpen_ball G.contDiff hrank
      μ Kc V hKV w S b hsupp hS hρ.1 (hmaps ρ hρ hx)
  refine ⟨B, hB, hDB, ρ₀, hρ₀, hρ₀1, (fun j ↦ ⟨hJ j, (hphase j).1.fst⟩),
    hlo, hH0, ?_, ?_⟩
  · intro ρ hρ x hx
    refine ⟨heq ρ hρ hx, ?_, ?_⟩
    · change PositiveBackground.referenceMeanResidual (sourceDilation G.map ρ)
        (carrierMean μ w ν ξ 0) (sourcePrincipalMean G.map μ w S b ρ) x =
          sourcePrincipalMean G.map μ w S b ρ x - carrierMean μ w ν ξ 0
      simpa only [PositiveBackground.referenceMeanResidual, Pi.add_apply, heq ρ hρ hx,
        normalizedCarrierMean_zero] using hres ρ hρ x hx
    · intro j z hz
      have hs : ContDiffOn ℝ ∞ (fun y ↦ S j (y, z)) Ω :=
        (hS j).comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hz⟩)
      exact sourcePhase_eq_extension isOpen_ball (convex_ball _ _) (hs.of_le (by simp))
        (retained_carrier_phase_zero (T j.1) (Q j.1) (fun k ↦ (hcarrier j hz k).le))
        h0 (hmaps ρ hρ hx) hρ.1.ne'
  · intro s
    obtain ⟨C, hC, hbound⟩ := hbound s
    refine ⟨C, hC, ?_⟩
    intro ρ hρ
    have hn : cNorm D s (fun x ↦ sourcePrincipalMean G.map μ w S b ρ x - carrierMean μ w ν ξ 0) =
        cNorm D s (fun x ↦ normalizedCarrierMean μ w ν ξ ρ x - normalizedCarrierMean μ w ν ξ 0 x) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq
      intro x hx
      filter_upwards [hB.mem_nhds (hDB hx)] with y hy
      rw [heq ρ hρ hy, normalizedCarrierMean_zero]
    rw [hn]
    exact hbound ρ ⟨hρ.1.le, hρ.2⟩

end JanetCartan.NormalizedBackground
