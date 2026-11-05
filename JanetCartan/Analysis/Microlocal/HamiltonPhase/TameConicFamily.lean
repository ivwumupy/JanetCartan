module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameBufferedFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.ConicExtension

/-!
# Homogeneous extensions of the actual tame Hamilton family

For `app:lem:common-hamilton-phase`, extend the very charts constructed by
`exists_commonTameBufferedHamiltonPhases`. The local phase and its homogeneous
extension agree on a fixed open overlap. Thus the sharp scalar-symbol order
`m + 1` estimate holds for the homogeneous phase on a compact inner overlap,
without identifying independently chosen inverse charts by definitional equality.
The common mixed and averaged gaps and finite-order continuity still require
assembly with this same family.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

local instance tameConicFamilyNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance tameConicFamilyNormedSpaceU : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

set_option maxHeartbeats 800000 in
/-- Construct the homogeneous extension of the actual tame phase family
(`app:lem:common-hamilton-phase`). All constants and the compact overlap precede
the variable symbol. Root, ODE and inverse inputs are constructed, and the
same root/flow/chart has both the joint tame estimates and the homogeneous
eikonal phase. The final bound is explicitly at scalar-symbol order `m + 1`,
so the coefficient order is `m + 3` for symbols costing two derivatives.
Uniform mixed/averaged inverse gaps and finite-order continuity are not claimed
by this theorem. -/
theorem exists_commonTameConicHamiltonPhases
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0)
    (hξ : (transverseSectionState j ν (s₀, τ₀)).2 ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (ℓ : (ℝ × U) →L[ℝ] ℝ) (ε r b ρ δ r₀ a c T : ℝ) (V : Set (E × (ℝ × U))) (B : ℕ → ℝ)
      (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U))),
      let Ω := CharacteristicRoot.conicDomain ℓ (ball (j s₀.1) ρ ×ˢ ball s₀.2 ρ)
      ℓ s₀.2 = 1 ∧ 0 < ε ∧ IsOpen Ω ∧ Convex ℝ Ω ∧
      closedBall (j s₀.1, s₀.2) (2 * ε) ⊆
        (ball (j s₀.1) ρ ×ˢ ball s₀.2 ρ) ∩ Ω ∧
      0 < r ∧ 0 < b ∧ 0 < ρ ∧ 0 < δ ∧ 0 < r₀ ∧ 0 < a ∧ 0 < c ∧
      4 * r₀ ≤ T ∧ 2 * r < r₀ ∧ (∀ m, 0 < B m) ∧
      MapsTo (transverseSectionState j ν)
        (closedBall s₀ (2 * r₀) ×ˢ Icc (τ₀ - a) (τ₀ + a)) (closedBall z₀ R) ∧
      IsOpen V ∧ IsCompact (closure V) ∧
      closedBall (j s₀.1) ρ ×ˢ closedBall s₀.2 ρ ⊆ V ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D → H.ConicHomogeneous →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (g : InitialData U → ℝ) (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          Φ.sectionMap = j.toContinuousLinearMap ∧
          Φ.time = Ioo (-T) T ∧ Φ.parameters = ball s₀ (2 * r₀) ∧
          ContDiffOn ℝ ∞ g (ball s₀ (2 * r₀)) ∧
          (∀ s ∈ ball s₀ (2 * r₀), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1 ∧
            c ≤ |⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ|) ∧
          (∀ s ∈ ball s₀ (2 * r₀), ∀ τ ∈ Icc (τ₀ - a) (τ₀ + a),
            H.h (transverseSectionState j ν (s, τ)) = s.2.1 ↔ g s = τ) ∧
          (∀ s ∈ ball s₀ (2 * r₀),
            (Φ.position (0, s), Φ.momentum (0, s)) = transverseSectionState j ν (s, g s)) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          C.target = V ∧
          C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧ ContDiffOn ℝ ∞ (phase C.coordinates) V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
            ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
              (fderiv ℝ Φ.augmentedProjection q) -
              ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) ∧
          (∀ z ∈ V,
            HasFDerivAt (phase C.coordinates)
              (phaseDifferential (Φ.momentum (chartLift C.coordinates z)) (C.coordinates z)) z ∧
            H.h (z.1, gradient (fun x ↦ phase C.coordinates (x, z.2)) z.1) = z.2.1) ∧
          (∀ u η, (0, (u, η)) ∈ C.source → phase C.coordinates (j u, η) = ⟪u, η.2⟫_ℝ) ∧
          (∀ m : ℕ,
            cNorm (closedBall s₀ r ×ˢ Icc (-r) r) m
                (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) +
              cNorm (closedBall (j s₀.1) ρ ×ˢ closedBall s₀.2 ρ) m C.coordinates +
              cNorm (closedBall (j s₀.1) ρ ×ˢ closedBall s₀.2 ρ) m (phase C.coordinates) ≤
                B m * (1 + cNorm (closedBall z₀ R) (m + 1) H.h)) ∧
          (∀ s ∈ ball s₀ (3 * r), ∀ t ∈ Φ.time, ∀ scale : ℝ, 0 < scale →
            scaleSectionData scale s ∈ ball s₀ (3 * r) →
            (Φ.position (t, scaleSectionData scale s), Φ.momentum (t, scaleSectionData scale s)) =
              (Φ.position (t, s), scale • Φ.momentum (t, s))) ∧
          ContDiffOn ℝ ∞ (C.conicPhase ℓ) Ω ∧
          (∀ z, ∀ scale : ℝ, 0 < scale →
            C.conicPhase ℓ (z.1, scale • z.2) = scale * C.conicPhase ℓ z) ∧
          (∀ z ∈ closedBall (j s₀.1, s₀.2) (2 * ε),
            C.conicPhase ℓ z = phase C.coordinates z) ∧
          (∀ z ∈ Ω,
            (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) ∈ H.domain ∧
            H.h (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) = z.2.1 ∧
            HasFDerivAt (fun η ↦ C.conicPhase ℓ (z.1, η))
              (canonicalCovector (C.coordinates (CharacteristicRoot.normalize ℓ z))) z.2) ∧
          (∀ u η, 0 < ℓ η → (0, (u, (ℓ η)⁻¹ • η)) ∈ C.source →
            C.conicPhase ℓ (j u, η) = ⟪u, η.2⟫_ℝ) ∧
          (∀ m : ℕ,
            cNorm (closedBall (j s₀.1, s₀.2) ε) m (C.conicPhase ℓ) =
              cNorm (closedBall (j s₀.1, s₀.2) ε) m (phase C.coordinates)) ∧
          (∀ m : ℕ,
            cNorm (closedBall (j s₀.1, s₀.2) ε) m (C.conicPhase ℓ) ≤
              B m * (1 + cNorm (closedBall z₀ R) (m + 1) H.h)) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨ℓ, hℓ⟩ := exists_canonicalNormalization
    (sectionCanonical_ne_zero H₀ j ν (hDH₀ (hRD (mem_closedBall_self hR.le)))
      henergy htrans hξ)
  obtain ⟨r, b, ρ, δ, r₀, a, c, T, V, B, A, hr, hb, hρ, hδ, hr₀, ha, hc,
      hrT, hrr, hB, hmap, hV, hVc, hbox, hfamily⟩ :=
    exists_commonTameBufferedHamiltonPhases H₀ hD hDH₀ hH₀ j ν horth hspan
      hR hRD henergy htrans
  let P := ball (j s₀.1) ρ ×ˢ ball s₀.2 ρ
  let Ω := CharacteristicRoot.conicDomain ℓ P
  have hPV : P ⊆ V := (Set.prod_mono ball_subset_closedBall ball_subset_closedBall).trans hbox
  obtain ⟨e, he, hebox⟩ := exists_normalization_buffer ℓ isOpen_ball isOpen_ball
    (show (j s₀.1, s₀.2) ∈ P from ⟨mem_ball_self hρ, mem_ball_self hρ⟩) hℓ
  have hbuf : closedBall (j s₀.1, s₀.2) (2 * (e / 2)) ⊆ P ∩ Ω := by
    simpa only [show 2 * (e / 2) = e by ring] using hebox
  refine ⟨ℓ, e / 2, r, b, ρ, δ, r₀, a, c, T, V, B, A, hℓ, half_pos he,
    CharacteristicRoot.isOpen_conicDomain ℓ (isOpen_ball.prod isOpen_ball),
    convex_conicDomain_prod ℓ (convex_ball _ _) (convex_ball _ _), hbuf,
    hr, hb, hρ, hδ, hr₀, ha, hc, hrT, hrr, hB, hmap, hV, hVc, hbox, ?_⟩
  intro H hDH hH hhom hsmall
  obtain ⟨g, Φ, C, hj, ht, hp, hg, hroot, huniq, hstart, hrange, hx, hm, hCt,
      hCs, hsource, hC, hphase, hinner, houter, hpre, hgap, hid, hsection, hbound⟩ :=
    hfamily H hDH hH hsmall
  have hC' : ContDiffOn ℝ ∞ C.coordinates C.target := hCt.symm ▸ hC
  have hsub : P ⊆ C.target := hCt.symm ▸ hPV
  have hcone : Ω ⊆ CharacteristicRoot.conicDomain ℓ C.target :=
    fun _ hz ↦ ⟨hz.1, hsub hz.2⟩
  have hagree : ∀ z ∈ closedBall (j s₀.1, s₀.2) (2 * (e / 2)),
      C.conicPhase ℓ z = phase C.coordinates z := by
    intro z hz
    have hz' := hbuf hz
    exact C.conicPhase_eq_of_mem_convex ℓ isOpen_ball (convex_ball _ _)
      (fun η hη ↦ hsub ⟨hz'.1.1, hη⟩) hz'.1.2 hz'.2.1 hz'.2.2.2
  have hPsub : ball s₀ (3 * r) ⊆ Φ.parameters := by
    rw [hp]
    exact ball_subset_ball (by linarith)
  have hstate : ∀ t ∈ Φ.time, ∀ s ∈ Φ.parameters,
      (Φ.position (t, s), Φ.momentum (t, s)) ∈ D :=
    fun t ht s hs ↦ hRD (hrange (t, s) ⟨ht, hs⟩)
  have hν : ν ≠ 0 := by
    intro heq
    apply htrans
    rw [heq, inner_zero_right]
  have hnormeq (m : ℕ) :
      cNorm (closedBall (j s₀.1, s₀.2) (e / 2)) m (C.conicPhase ℓ) =
        cNorm (closedBall (j s₀.1, s₀.2) (e / 2)) m (phase C.coordinates) := by
    apply Finset.sum_congr rfl
    intro k _hk
    congr 1
    apply Set.image_congr
    intro z hz
    have hz' : z ∈ ball (j s₀.1, s₀.2) (2 * (e / 2)) :=
      closedBall_subset_ball (by linarith) hz
    have heq : C.conicPhase ℓ =ᶠ[𝓝 z] phase C.coordinates :=
      eventuallyEq_of_mem (isOpen_ball.mem_nhds hz')
        (fun w hw ↦ hagree w (ball_subset_closedBall hw))
    exact congrArg norm ((heq.iteratedFDeriv ℝ k).eq_of_nhds)
  refine ⟨g, Φ, C, hj, ht, hp, hg, hroot, huniq, hstart, hrange, hx, hm, hCt,
    hCs, hsource, hC, hphase, hinner, houter, hpre, hgap, hid, hsection, hbound,
    ?_, (C.contDiffOn_conicPhase ℓ hC').mono hcone,
    fun z scale hscale ↦ C.conicPhase_smul ℓ z hscale, hagree, ?_, ?_, hnormeq, ?_⟩
  · intro s hs t ht scale hscale hscales
    have hi := Φ.initial_momentum_smul_of_section hD hH (hstate 0 Φ.zero_mem_time)
      j ν hν hj horth hspan isOpen_ball (convex_ball _ _) hPsub hs hscale hscales
    exact Φ.state_smul_on_symbolPatch hhom hD hstate
      (H.contDiffOn_vectorField_of_subset hD hDH (hH.of_le (by simp)))
      hscale (hPsub hs) (hPsub hscales) hi ht
  · intro z hz
    obtain ⟨hmem, heik⟩ := C.conicPhase_eikonal ℓ hhom (hcone hz)
    exact ⟨hmem, heik, C.hasFDerivAt_conicPhase_canonical ℓ hC'
      isOpen_ball (convex_ball _ _) hsub hz⟩
  · intro u η hη hs
    simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using
      C.conicPhase_initial_value ℓ hη hs
  · intro m
    rw [hnormeq]
    have hKsub : closedBall (j s₀.1, s₀.2) (e / 2) ⊆
        closedBall (j s₀.1) ρ ×ˢ closedBall s₀.2 ρ := by
      intro z hz
      exact ⟨ball_subset_closedBall (hbuf
        (closedBall_subset_closedBall (by linarith) hz)).1.1,
        ball_subset_closedBall (hbuf
          (closedBall_subset_closedBall (by linarith) hz)).1.2⟩
    have hmono := cNorm_mono_set_of_contDiffAt hKsub
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
      (fun z hz ↦ (hphase.contDiffAt (hV.mem_nhds (hbox hz))).of_le
        (by simp : (m : ℕ∞ω) ≤ ∞))
    exact hmono.trans ((le_add_of_nonneg_left
      (add_nonneg (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _))).trans (hbound m))


/-- The sharp coefficient-order `m + 3` bound for the actual homogeneous phase
in `app:lem:common-hamilton-phase`. The only high-order input concerns the scalar
symbol at coefficient order `k + 2`, supplied for carrier symbols by their
normalized-symbol estimate. The phase itself is constructed before the
coefficient map and the derivative order. In particular, using `m = r + 3`
gives coefficient order `r + 6` for the primitive phase budget consumed by
`FullPhaseCharts.InverseEstimates.exists_carrierQuotient_inverse_epsilon_map_bound`.
This does not supply that consumer's separate carrier or parameter-jet bounds. -/
theorem exists_commonHomogeneousPhase_coefficient_order_three
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0)
    (hξ : (transverseSectionState j ν (s₀, τ₀)).2 ≠ 0)
    (KF : Set X) (M : ℕ → ℝ) (hM : ∀ k, 0 ≤ M k) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (ℓ : (ℝ × U) →L[ℝ] ℝ) (ε δ : ℝ) (Ω : Set (E × (ℝ × U))) (B : ℕ → ℝ),
      ℓ s₀.2 = 1 ∧ 0 < ε ∧ 0 < δ ∧ IsOpen Ω ∧ Convex ℝ Ω ∧
      closedBall (j s₀.1, s₀.2) (2 * ε) ⊆ Ω ∧ (∀ m, 0 < B m) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        H.ConicHomogeneous → cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ (C.conicPhase ℓ) Ω ∧
          (∀ z, ∀ scale : ℝ, 0 < scale →
            C.conicPhase ℓ (z.1, scale • z.2) = scale * C.conicPhase ℓ z) ∧
          (∀ z ∈ closedBall (j s₀.1, s₀.2) (2 * ε),
            C.conicPhase ℓ z = phase C.coordinates z) ∧
          (∀ z ∈ Ω,
            (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) ∈ H.domain ∧
            H.h (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) = z.2.1 ∧
            HasFDerivAt (fun η ↦ C.conicPhase ℓ (z.1, η))
              (canonicalCovector (C.coordinates (CharacteristicRoot.normalize ℓ z))) z.2) ∧
          (∀ u η, 0 < ℓ η → (0, (u, (ℓ η)⁻¹ • η)) ∈ C.source →
            C.conicPhase ℓ (j u, η) = ⟪u, η.2⟫_ℝ) ∧
          ∀ F : X → Y,
            (∀ k, cNorm (closedBall z₀ R) k H.h ≤ M k * (1 + cNorm KF (k + 2) F)) →
            ∀ m, cNorm (closedBall (j s₀.1, s₀.2) ε) m (C.conicPhase ℓ) ≤
              B m * (1 + cNorm KF (m + 3) F) := by
  obtain ⟨ℓ, ε, r, b, ρ, δ, r₀, a, c, T, V, B, A, hℓ, hε, hΩ, hΩc, hbuf,
      _hr, _hb, _hρ, hδ, _hr₀, _ha, _hc, _hrT, _hrr, hB,
      _hmap, _hV, _hVc, _hbox, hfamily⟩ :=
    exists_commonTameConicHamiltonPhases H₀ hD hDH₀ hH₀ j ν horth hspan
      hR hRD henergy htrans hξ
  refine ⟨ℓ, ε, δ, _, fun m ↦ B m * (1 + M (m + 1)), hℓ, hε, hδ, hΩ, hΩc,
    hbuf.trans inter_subset_right, fun m ↦ mul_pos (hB m) (by linarith [hM (m + 1)]), ?_⟩
  intro H hDH hH hhom hsmall
  obtain ⟨g, Φ, C, hj, _ht, _hp, _hg, _hroot, _huniq, _hstart, _hrange, _hx, _hm, _hCt,
      _hCs, _hsource, _hC, _hphase, _hinner, _houter, _hpre, _hgap, _hid, _hsection,
      _hbound, _hscale, hS, hhomS, hagree, heik, hsect, _hnormeq, hsharp⟩ :=
    hfamily H hDH hH hhom hsmall
  refine ⟨Φ, C, hj, hS, hhomS, hagree, heik, hsect, ?_⟩
  intro F hsymbol m
  apply (hsharp m).trans
  have hbudget := hsymbol (m + 1)
  have hn := cNorm_nonneg KF (m + 3) F
  have hm : m + 1 + 2 = m + 3 := by omega
  rw [hm] at hbudget
  have hh : 1 + cNorm (closedBall (transverseSectionState j ν (s₀, τ₀)) R) (m + 1) H.h ≤
      (1 + M (m + 1)) * (1 + cNorm KF (m + 3) F) := by nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (hB m).le

end JanetCartan.HamiltonPhase
