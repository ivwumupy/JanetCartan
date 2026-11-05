module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.TameContinuousFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.ConicExtension

/-!
# One common tame, continuous, homogeneous Hamilton family

The final assembly for `app:lem:common-hamilton-phase` identifies the actual
conic buffered charts with the tame continuous charts by root, ODE and inverse
uniqueness. All estimates retain scalar-symbol order `m + 1`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
local instance commonFamilyNormedSpaceE : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance commonFamilyNormedSpaceU : NormedSpace ℝ U := InnerProductSpace.toNormedSpace

private theorem cNorm_eq_of_eqOn_open
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f g : X → Y} {O K : Set X} (hO : IsOpen O) (hK : K ⊆ O)
    (he : EqOn f g O) (m : ℕ) : cNorm K m f = cNorm K m g := by
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  apply Set.image_congr
  intro z hz
  have hh : f =ᶠ[𝓝 z] g := eventuallyEq_of_mem (hO.mem_nhds (hK hz)) (fun w hw ↦ he hw)
  exact congrArg norm ((hh.iteratedFDeriv ℝ k).eq_of_nhds)

set_option maxHeartbeats 2000000 in
/-- The common homogeneous Hamilton phase of `app:lem:common-hamilton-phase`,
with all geometric buffers, uniform mixed and averaged inverse gaps, sharp
one-high joint estimates, and finite-order continuity on the same actual
charts. All domains and constants precede the variable symbol. The compact
normalized estimate box contains the entire middle canonical inverse buffer.
The scalar order is `m + 1`, hence coefficient order `m + 3` when the symbol
costs two coefficient derivatives. No phase, flow, inverse, or estimate is an
input: the hypotheses are the fixed transverse symbol and section data. -/
theorem exists_commonTameContinuousConicHamiltonPhases
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
    ∃ (ℓ : (ℝ × U) →L[ℝ] ℝ) (A : (ℝ × U) ≃L[ℝ] E)
      (r b ρ σ a δ ε β t : ℝ) (M : ℕ → ℝ)
      (V : Set (E × (ℝ × U))) (W : Set E)
      (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀),
      let B := ball (j s₀.1) ρ
      let P := ball s₀.2 (3 * a)
      let Q := canonicalCone ℓ P
      let Ω := CharacteristicRoot.conicDomain ℓ (B ×ˢ P)
      0 < r ∧ 0 < b ∧ 0 < ρ ∧ 0 < σ ∧ 0 < a ∧ 0 < δ ∧ 0 < ε ∧ 0 < β ∧
      0 < t ∧ (∀ m, 0 < M m) ∧ ℓ s₀.2 = 1 ∧ IsOpen V ∧ IsCompact (closure V) ∧
      IsOpen W ∧ IsCompact (closure W) ∧ Convex ℝ Ω ∧ Convex ℝ Q ∧
      closedBall (j s₀.1, s₀.2) ε ⊆ (B ×ˢ P) ∩ Ω ∧
      closedBall s₀.2 (3 * σ) ⊆ P ∩ Q ∧
      B ×ˢ P ⊆ V ∧
      closedBall (j s₀.1) (ρ / 2) ×ˢ closedBall s₀.2 (3 * σ) ⊆ Ω ∧
      ∃ (F : (H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
          H.ConicHomogeneous ∧ cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}) → HamiltonFlow H.1 U)
        (C : (H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
          H.ConicHomogeneous ∧ cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}) → ProjectionChart (F H)),
        (∀ H,
          let Φ := F H
          let C := C H
          let Ξ := fun x y η ↦ averagedPhaseGradient
            (fun η x ↦ phase C.coordinates (x, η)) η x y
          let Ξc := fun x y η ↦ averagedPhaseGradient
            (fun η x ↦ C.conicPhase ℓ (x, η)) η x y
          (∀ m : ℕ,
            cNorm (closedBall s₀ t ×ˢ Icc (-t) t) m
              (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) +
            cNorm (closedBall (j s₀.1) (ρ / 2) ×ˢ closedBall s₀.2 (3 * σ)) m C.coordinates +
            cNorm (closedBall (j s₀.1) (ρ / 2) ×ˢ closedBall s₀.2 (3 * σ)) m (C.conicPhase ℓ) ≤
              M m * (1 + cNorm (closedBall z₀ R) (m + 1) H.1.h)) ∧
          (∀ z ∈ B ×ˢ (P ∩ Q), C.conicPhase ℓ z = phase C.coordinates z) ∧
          (∀ u η, (0, (u, η)) ∈ C.source → phase C.coordinates (j u, η) = ⟪u, η.2⟫_ℝ) ∧
          (∀ z ∈ V, HasFDerivAt (phase C.coordinates)
            (phaseDifferential (Φ.momentum (chartLift C.coordinates z)) (C.coordinates z)) z ∧
            H.1.h (z.1, gradient (fun x ↦ phase C.coordinates (x, z.2)) z.1) = z.2.1) ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          C.target = V ∧ C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ s ∈ ball s₀ (3 * r), ∀ t ∈ Φ.time, ∀ a : ℝ, 0 < a →
            scaleSectionData a s ∈ ball s₀ (3 * r) →
            (Φ.position (t, scaleSectionData a s), Φ.momentum (t, scaleSectionData a s)) =
              (Φ.position (t, s), a • Φ.momentum (t, s))) ∧
          (∀ z ∈ C.target, ∀ a : ℝ, 0 < a →
            ((C.coordinates z).1, ((C.coordinates z).2, a • z.2)) ∈ C.source →
            C.coordinates (z.1, a • z.2) = C.coordinates z) ∧
          ContDiffOn ℝ ∞ (C.conicPhase ℓ) Ω ∧
          (∀ z, ∀ a : ℝ, 0 < a → C.conicPhase ℓ (z.1, a • z.2) = a * C.conicPhase ℓ z) ∧
          (∀ z ∈ closedBall (j s₀.1, s₀.2) ε, C.conicPhase ℓ z = phase C.coordinates z) ∧
          (∀ z ∈ Ω,
            (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) ∈ H.1.domain ∧
            H.1.h (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) = z.2.1 ∧
            HasFDerivAt (fun η ↦ C.conicPhase ℓ (z.1, η))
              (canonicalCovector (C.coordinates (CharacteristicRoot.normalize ℓ z))) z.2 ∧
            ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
              (fderiv ℝ (fun η ↦ gradient (fun x ↦ C.conicPhase ℓ (x, η)) z.1) z.2) -
                ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8) ∧
          (∀ u η, 0 < ℓ η → (0, (u, (ℓ η)⁻¹ • η)) ∈ C.source →
            C.conicPhase ℓ (j u, η) = ⟪u, η.2⟫_ℝ) ∧
          ∀ x ∈ B, ∀ y ∈ B,
            (∀ η ∈ Q, ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξc x y) η) -
                ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8) ∧
            InjOn (Ξc x y) Q ∧
            (∀ η ∈ Q, ∀ θ ∈ Q, ‖η - θ‖ / 2 ≤ ‖A.symm (Ξc x y η - Ξc x y θ)‖) ∧
            cthickening β (Ξ x y '' closedBall s₀.2 σ) ⊆ W ∧
            cthickening β (closure W) ⊆ Ξ x y '' ball s₀.2 (2 * σ) ∧
            (Ξ x y) ⁻¹' cthickening β (closure W) ∩ P ⊆ ball s₀.2 (2 * σ) ∧
            cthickening β (Ξc x y '' closedBall s₀.2 σ) ⊆ W ∧
            cthickening β (closure W) ⊆ Ξc x y '' ball s₀.2 (2 * σ) ∧
            (Ξc x y) ⁻¹' cthickening β (closure W) ∩ Q ⊆ ball s₀.2 (2 * σ) ) ∧
        (∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ H,
          cNorm (closedBall z₀ R) (m + 1) (fun z ↦ H.1.h z - H₀.h z) < d →
            cNorm (closedBall (j s₀.1) (ρ / 2) ×ˢ closedBall s₀.2 (3 * σ)) m
              (fun z ↦ (C H).conicPhase ℓ z - phase C₀.coordinates z) < ε) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  let y₀ := (j s₀.1, s₀.2)
  obtain ⟨rt, ρt, δt, R', M, At, Φ₀, C₀, hrt, hρt, hδt, hR', hRR, hM,
      hC₀t, hS₀, Ft, Ct, htprops, htcont⟩ :=
    exists_commonTameContinuousHamiltonPhases H₀ hD hDH₀ hH₀ j ν horth hspan
      hR hRD henergy htrans
  have hR'D : closedBall z₀ R' ⊆ D := (closedBall_subset_closedBall hRR.le).trans hRD
  let N := ‖(At.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U))‖
  let cap := fun r : ℝ ↦ min ρt (min (3 * rt) (3 * r) / (2 * (N + 1)))
  have hcap : ∀ r > 0, 0 < cap r := by intro r hr; dsimp [cap, N]; positivity
  obtain ⟨ℓ, A, r, b, ρ, σ, a, δc, ε, β, V, W,
      hr, hb, hρ, hσ, ha, hδc, hε, hβ, hℓ, hV, hVc, hW, hWc,
      hΩ, hQ, hbuf, hnormal, hBP, hcapBP, hcFamily⟩ :=
    exists_commonConicHamiltonPhases_with_targetRadius H₀ hD hDH₀ hH₀ j ν horth hspan
      hR' hR'D henergy htrans hξ cap hcap
  let δ := min δt δc
  have hδ : 0 < δ := lt_min hδt hδc
  let S := {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
    H.ConicHomogeneous ∧ cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}
  have hmono (f : E × E → ℝ) (hf : ContDiffOn ℝ ∞ f D) (m : ℕ) :
      cNorm (closedBall z₀ R') m f ≤ cNorm (closedBall z₀ R) m f :=
    cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hRR.le)
      (isCompact_closedBall _ _)
      (fun z hz ↦ (hf.contDiffAt (hD.mem_nhds (hRD hz))).of_le (by simp))
  let Ht (H : S) : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
      cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δt} :=
    ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.2.trans (min_le_left _ _)⟩
  have hex (H : S) := hcFamily H.1 H.2.1 H.2.2.1 H.2.2.2.1
    ((hmono _ (H.2.2.1.sub hH₀) 3).trans (H.2.2.2.2.trans (min_le_right _ _)))
  let F (H : S) : HamiltonFlow H.1 U := (hex H).choose
  let C (H : S) : ProjectionChart (F H) := (hex H).choose_spec.choose
  have hcprops (H : S) := (hex H).choose_spec.choose_spec
  let B := ball (j s₀.1) ρ
  let P := ball s₀.2 (3 * a)
  let Q := canonicalCone ℓ P
  let O := B ×ˢ (P ∩ Q)
  let K := closedBall (j s₀.1) (ρ / 2) ×ˢ closedBall s₀.2 (3 * σ)
  have hQopen : IsOpen Q := by
    have hh := (CharacteristicRoot.isOpen_conicDomain ℓ
      (isOpen_univ.prod (isOpen_ball : IsOpen P))).preimage
      (continuous_const.prodMk continuous_id : Continuous (fun η : ℝ × U ↦ ((0 : E), η)))
    simpa only [CharacteristicRoot.conicDomain, CharacteristicRoot.normalize,
      Set.preimage_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, canonicalCone, Q] using hh
  have hO : IsOpen O := isOpen_ball.prod (isOpen_ball.inter hQopen)
  have hKO : K ⊆ O := fun z hz ↦
    ⟨closedBall_subset_ball (by linarith) hz.1, hnormal hz.2⟩
  have hKB : K ⊆ B ×ˢ P := fun z hz ↦ ⟨(hKO hz).1, (hKO hz).2.1⟩
  have hKcompact : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hBPρ : B ×ˢ P ⊆ ball y₀ ρt :=
    hcapBP.trans (ball_subset_ball (min_le_left _ _))
  have hKρ : K ⊆ closedBall y₀ ρt := hKB.trans (hBPρ.trans ball_subset_closedBall)
  have hν : ν ≠ 0 := by intro he; apply htrans; rw [he, inner_zero_right]
  have heq (H : S) : EqOn (Ct (Ht H)).coordinates (C H).coordinates (B ×ˢ P) := by
    obtain ⟨hjt, htargett, _hsourcet, hbuft, hadmt, hhalft, hranget, htranst,
      _hxt, _hpt, _hCt, _hSt, _hidt, _hboundt⟩ := htprops (Ht H)
    obtain ⟨hj, _hx, _hp, hrange, htarget, hsource, _hbuf, hadm, _hC, _rest⟩ := hcprops H
    change (C H).target = V at htarget
    change (C H).source = ball ((0 : ℝ), s₀) (3 * r) ∩ (F H).augmentedProjection ⁻¹' V at hsource
    have hh := (Ct (Ht H)).coordinates_eq_on_transverse_overlap (C H) hD H.2.1 H.2.2.1
      hR'D j ν hν horth hspan hjt hj htranst
      (by positivity : 0 < 3 * rt) (by positivity : 0 < 3 * r) At hadmt
      (subset_closure.trans hadm) (hbuft.trans (ball_subset_ball (by linarith)))
      (by simpa only [htarget] using hsource) hhalft hranget hrange
    intro z hz
    exact hh ⟨⟨htargett (ball_subset_ball (by linarith) (hBPρ hz)), htarget.symm ▸ hBP hz⟩,
      ball_subset_ball (min_le_right _ _) (hcapBP hz)⟩
  have hphase (H : S) : EqOn ((C H).conicPhase ℓ) (phase (Ct (Ht H)).coordinates) O := by
    obtain ⟨_hj, _hx, _hp, _hrange, htarget, _rest⟩ := hcprops H
    change (C H).target = V at htarget
    intro z hz
    have hsub : ∀ η ∈ P, (z.1, η) ∈ (C H).target := by
      intro η hη
      rw [htarget]
      exact hBP ⟨hz.1, hη⟩
    have hlocal := (C H).conicPhase_eq_of_mem_convex ℓ isOpen_ball (convex_ball _ _)
      hsub hz.2.1 hz.2.2.1 hz.2.2.2
    exact hlocal.trans (by simp only [phase, heq H ⟨hz.1, hz.2.1⟩])
  let t := min rt r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht_rt : t < rt := by have hh := min_le_left rt r; dsimp [t]; linarith
  have ht_r : t < r := by have hh := min_le_right rt r; dsimp [t]; linarith
  have hbound (H : S) (m : ℕ) :
      cNorm (closedBall s₀ t ×ˢ Icc (-t) t) m
        (fun q ↦ ((F H).position (q.2, q.1), (F H).momentum (q.2, q.1))) +
      cNorm K m (C H).coordinates + cNorm K m ((C H).conicPhase ℓ) ≤
        M m * (1 + cNorm (closedBall z₀ R) (m + 1) H.1.h) := by
    obtain ⟨hjt, _htargett, _hsourcet, _hbuft, hadmt, _hhalft, hranget, htranst,
      hxt, hpt, hCt, hSt, _hidt, hboundt⟩ := htprops (Ht H)
    obtain ⟨hj, _hx, _hp, hrange, _htarget, _hsource, _hbuf, hadm, _hC, _rest⟩ := hcprops H
    let d := min (3 * rt) (3 * r)
    have hd : 0 < d := lt_min (by positivity) (by positivity)
    have hstate := (Ft (Ht H)).state_eq_on_transverse_ball (F H) hD H.2.1 H.2.2.1
      hR'D hd j ν hν horth hspan hjt hj htranst
      ((ball_subset_ball (min_le_left _ _)).trans hadmt)
      ((ball_subset_ball (min_le_right _ _)).trans (subset_closure.trans hadm)) hranget hrange
    have hswap : EqOn
        (fun q : InitialData U × ℝ ↦ ((Ft (Ht H)).position (q.2, q.1), (Ft (Ht H)).momentum (q.2, q.1)))
        (fun q : InitialData U × ℝ ↦ ((F H).position (q.2, q.1), (F H).momentum (q.2, q.1)))
        (ball s₀ d ×ˢ Ioo (-d) d) := by
      intro q hq
      exact hstate (by simpa only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right,
        Real.norm_eq_abs, abs_lt, mem_Ioo] using And.intro hq.2 (mem_ball.mp hq.1))
    have htd : t < d := lt_min (by linarith) (by linarith)
    have hsmall : closedBall s₀ t ×ˢ Icc (-t) t ⊆ ball s₀ d ×ˢ Ioo (-d) d := by
      intro q hq
      exact ⟨closedBall_subset_ball htd hq.1, ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
    rw [← cNorm_eq_of_eqOn_open (isOpen_ball.prod isOpen_Ioo) hsmall hswap m,
      ← cNorm_eq_of_eqOn_open (isOpen_ball.prod isOpen_ball) hKB (heq H) m,
      cNorm_eq_of_eqOn_open hO hKO (hphase H) m]
    have hflowmono := cNorm_mono_set_of_contDiffAt
      (show closedBall s₀ t ×ˢ Icc (-t) t ⊆ closedBall s₀ rt ×ˢ Icc (-rt) rt from by
        intro q hq
        exact ⟨closedBall_subset_closedBall ht_rt.le hq.1,
          ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩)
      ((isCompact_closedBall _ _).prod isCompact_Icc)
      (f := fun q : InitialData U × ℝ ↦
        ((Ft (Ht H)).position (q.2, q.1), (Ft (Ht H)).momentum (q.2, q.1)))
      (by
        intro q hq
        have hq' : (q.2, q.1) ∈ (Ft (Ht H)).time ×ˢ (Ft (Ht H)).parameters := by
          apply hadmt
          rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right, Real.norm_eq_abs, abs_lt]
          exact ⟨⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩,
            (mem_closedBall.mp hq.1).trans_lt (by linarith)⟩
        exact (((hxt.prodMk hpt).contDiffAt
          (((Ft (Ht H)).isOpen_time.prod (Ft (Ht H)).isOpen_parameters).mem_nhds hq')).comp q
            (contDiff_snd.prodMk contDiff_fst).contDiffAt).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    have hcmono := cNorm_mono_set_of_contDiffAt hKρ (isCompact_closedBall _ _)
      (fun z hz ↦ (hCt.contDiffAt (isOpen_ball.mem_nhds
        (closedBall_subset_ball (by linarith) hz))).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    have hsmono := cNorm_mono_set_of_contDiffAt hKρ (isCompact_closedBall _ _)
      (fun z hz ↦ (hSt.contDiffAt (isOpen_ball.mem_nhds
        (closedBall_subset_ball (by linarith) hz))).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
    linarith [hboundt m]
  refine ⟨ℓ, A, r, b, ρ, σ, a, δ, ε, β, t, M, V, W, Φ₀, C₀,
    hr, hb, hρ, hσ, ha, hδ, hε, hβ, ht, hM, hℓ, hV, hVc, hW, hWc,
    hΩ, hQ, hbuf, hnormal, hBP,
    (fun z hz ↦ ⟨(hKO hz).2.2.1, (hKO hz).1, (hKO hz).2.2.2⟩), F, C, ?_, ?_⟩
  · intro H
    refine ⟨hbound H, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have htarget : (C H).target = V := (hcprops H).2.2.2.2.1
      exact (C H).conicPhase_eq_of_mem_convex ℓ isOpen_ball (convex_ball _ _)
        (by
          intro η hη
          rw [htarget]
          exact hBP ⟨hz.1, hη⟩)
        hz.2.1 hz.2.2.1 hz.2.2.2
    · intro u η hs
      have hj : (F H).sectionMap = j.toContinuousLinearMap := (hcprops H).1
      simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using (C H).initial_value hs
    · intro z hz
      have htarget := (hcprops H).2.2.2.2.1
      exact ⟨(C H).hasFDerivAt_phase (htarget.symm ▸ hz), (C H).eikonal (htarget.symm ▸ hz)⟩
    · obtain ⟨hj, hx, hp, hrange, hrest⟩ := hcprops H
      exact ⟨hj, hx, hp, fun q hq ↦ closedBall_subset_closedBall hRR.le (hrange q hq), hrest⟩
  · intro m e he
    obtain ⟨d, hd, hcont⟩ := htcont m e he
    refine ⟨d, hd, ?_⟩
    intro H hsmall
    have hh := hcont (Ht H) hsmall
    rw [cNorm_eq_of_eqOn_open hO hKO
      (show EqOn (fun z ↦ (C H).conicPhase ℓ z - phase C₀.coordinates z)
        (fun z ↦ phase (Ct (Ht H)).coordinates z - phase C₀.coordinates z) O from
          fun z hz ↦ congrArg (fun v ↦ v - phase C₀.coordinates z) (hphase H hz)) m]
    obtain ⟨_hj, _htarget, _hsource, _hbuf, _hadm, _hhalf, _hrange, _htrans,
      _hx, _hp, _hC, hSt, _hid, _hbound⟩ := htprops (Ht H)
    have hdiff := hSt.sub hS₀
    exact (cNorm_mono_set_of_contDiffAt hKρ (isCompact_closedBall _ _)
      (fun z hz ↦ (hdiff.contDiffAt (isOpen_ball.mem_nhds
        (closedBall_subset_ball (by linarith) hz))).of_le (by simp))).trans_lt hh

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ U] in
/-- The separate sharp phase estimate at coefficient order `m + 3`
(`app:lem:common-hamilton-phase`). The joint budget is produced on these exact
charts by `exists_commonTameContinuousConicHamiltonPhases`; the scalar-symbol
budget is the coefficient-symbol producer's input from the manuscript.
At `m = r + 3` this gives the coefficient order `r + 6` consumed by
`FullPhaseCharts.InverseEstimates.exists_carrierQuotient_inverse_epsilon_map_bound`.
There is no additional loss from combining flow and inverse estimates. -/
theorem ProjectionChart.conicPhase_cNorm_coefficient_order_three
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U} (C : ProjectionChart Φ)
    (ℓ : (ℝ × U) →L[ℝ] ℝ) (K : Set (E × (ℝ × U)))
    (Kt : Set (InitialData U × ℝ)) (KH : Set (E × E)) (KF : Set X)
    (F : X → Y) (m : ℕ) {M L : ℝ} (hM : 0 ≤ M)
    (hjoint : cNorm Kt m (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))) +
      cNorm K m C.coordinates + cNorm K m (C.conicPhase ℓ) ≤
        M * (1 + cNorm KH (m + 1) H.h))
    (hsymbol : cNorm KH (m + 1) H.h ≤ L * (1 + cNorm KF (m + 3) F)) :
    cNorm K m (C.conicPhase ℓ) ≤ M * (1 + L) * (1 + cNorm KF (m + 3) F) := by
  have hp : cNorm K m (C.conicPhase ℓ) ≤ M * (1 + cNorm KH (m + 1) H.h) := by
    linarith [cNorm_nonneg Kt m (fun q ↦ (Φ.position (q.2, q.1), Φ.momentum (q.2, q.1))),
      cNorm_nonneg K m C.coordinates]
  have hb : 1 + cNorm KH (m + 1) H.h ≤ (1 + L) * (1 + cNorm KF (m + 3) F) := by
    nlinarith [cNorm_nonneg KF (m + 3) F]
  exact hp.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hM)

end JanetCartan.HamiltonPhase
