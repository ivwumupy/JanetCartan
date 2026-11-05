module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FamilyMixedHessian
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.Scaling
public import JanetCartan.Analysis.Microlocal.CharacteristicRoot.Gap

/-!
# Positive conic continuation of Hamilton phases

The continuation in `app:lem:common-hamilton-phase` uses a linear transverse
normalization, retaining the physical point. Its physical gradient is the
positively rescaled momentum of the actual local chart, so the eikonal equation
continues on the symbol's conic domain.
-/

@[expose] public noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Euler's identity and the transverse gap exclude zero canonical data even
when the tangential momentum vanishes (`app:lem:common-hamilton-phase`). This
supplies the nonzero input for the transverse normalization of the common phase. -/
theorem sectionCanonical_ne_zero (H : HomogeneousSymbol E)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {s : InitialData U} {τ : ℝ}
    (hmem : transverseSectionState j ν (s, τ) ∈ H.domain)
    (henergy : H.h (transverseSectionState j ν (s, τ)) = s.2.1)
    (htrans : ⟪H.hp (transverseSectionState j ν (s, τ)), ν⟫_ℝ ≠ 0)
    (hξ : (transverseSectionState j ν (s, τ)).2 ≠ 0) : s.2 ≠ 0 := by
  intro hs
  have he := (H.euler hmem).trans henergy
  have hη : s.2.2 = 0 := congrArg Prod.snd hs
  have he₀ : s.2.1 = 0 := congrArg Prod.fst hs
  have hτ : τ ≠ 0 := by
    intro h
    apply hξ
    simp [transverseSectionState, hη, h]
  have hprod : τ * ⟪H.hp (transverseSectionState j ν (s, τ)), ν⟫_ℝ = 0 := by
    calc
      _ = ⟪(transverseSectionState j ν (s, τ)).2,
          H.hp (transverseSectionState j ν (s, τ))⟫_ℝ := by
        simp only [transverseSectionState, hη, map_zero, add_zero, inner_smul_left]
        simp [real_inner_comm]
      _ = 0 := he.trans he₀
  exact htrans ((mul_eq_zero.mp hprod).resolve_left hτ)

/-- A nonzero canonical covector admits a transverse slice through itself
(`app:lem:common-hamilton-phase`). -/
theorem exists_canonicalNormalization {η : ℝ × U} (hη : η ≠ 0) :
    ∃ ℓ : (ℝ × U) →L[ℝ] ℝ, ℓ η = 1 :=
  SeparatingDual.exists_eq_one hη

/-- The positive cone over a transverse canonical patch, used for the
injectivity assertion in `app:lem:common-hamilton-phase`. -/
def canonicalCone (ℓ : (ℝ × U) →L[ℝ] ℝ) (P : Set (ℝ × U)) : Set (ℝ × U) :=
  {η | 0 < ℓ η ∧ (ℓ η)⁻¹ • η ∈ P}

/-- Transverse linear normalization preserves convexity of the canonical
cone (`app:lem:common-hamilton-phase`). -/
theorem convex_canonicalCone (ℓ : (ℝ × U) →L[ℝ] ℝ) {P : Set (ℝ × U)} (hP : Convex ℝ P) :
    Convex ℝ (canonicalCone ℓ P) := by
  intro η hη θ hθ a b ha hb hab
  have hL : 0 < a * ℓ η + b * ℓ θ := by
    have hη0 := hη.1
    have hθ0 := hθ.1
    by_cases ha0 : a = 0
    · simp_all
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hη0)
        (mul_nonneg hb hθ0.le)
  have hsum : a * ℓ η / (a * ℓ η + b * ℓ θ) +
      b * ℓ θ / (a * ℓ η + b * ℓ θ) = 1 := by
    rw [← add_div, div_self hL.ne']
  have hnorm := hP hη.2 hθ.2
    (div_nonneg (mul_nonneg ha hη.1.le) hL.le)
    (div_nonneg (mul_nonneg hb hθ.1.le) hL.le) hsum
  constructor
  · simpa using hL
  · change (ℓ (a • η + b • θ))⁻¹ • (a • η + b • θ) ∈ P
    convert hnorm using 1
    simp only [map_add, map_smul, smul_eq_mul, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> field_simp [hη.1.ne', hθ.1.ne']

/-- Product physical and canonical boxes have a convex conic extension
(`app:lem:common-hamilton-phase`). -/
theorem convex_conicDomain_prod (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {B : Set E} {P : Set (ℝ × U)} (hB : Convex ℝ B) (hP : Convex ℝ P) :
    Convex ℝ (CharacteristicRoot.conicDomain ℓ (B ×ˢ P)) := by
  convert hB.prod (convex_canonicalCone ℓ hP) using 1
  ext z
  simp [CharacteristicRoot.conicDomain, CharacteristicRoot.normalize,
    canonicalCone, and_left_comm]

/-- Every point in the positive canonical cone is nonzero
(`app:lem:common-hamilton-phase`). -/
theorem canonicalCone_ne_zero (ℓ : (ℝ × U) →L[ℝ] ℝ) {P : Set (ℝ × U)}
    {η : ℝ × U} (hη : η ∈ canonicalCone ℓ P) : η ≠ 0 := by
  intro he
  have := hη.1
  simp [he] at this

/-- A normalized point admits a closed overlap buffer chosen entirely from
its physical and canonical boxes, independently of the perturbed symbol
(`app:lem:common-hamilton-phase`). -/
theorem exists_normalization_buffer (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {B : Set E} {P : Set (ℝ × U)} (hB : IsOpen B) (hP : IsOpen P)
    {z : E × (ℝ × U)} (hz : z ∈ B ×ˢ P) (hℓ : ℓ z.2 = 1) :
    ∃ ε : ℝ, 0 < ε ∧ closedBall z ε ⊆
      (B ×ˢ P) ∩ CharacteristicRoot.conicDomain ℓ (B ×ˢ P) := by
  have hc : z ∈ CharacteristicRoot.conicDomain ℓ (B ×ˢ P) := by
    refine ⟨by rw [hℓ]; norm_num, ?_⟩
    simpa [CharacteristicRoot.normalize, hℓ] using hz
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp
    (((hB.prod hP).inter (CharacteristicRoot.isOpen_conicDomain ℓ (hB.prod hP))).mem_nhds
      ⟨hz, hc⟩)
  exact ⟨ε / 2, half_pos hε, fun _ hw ↦
    hsub (closedBall_subset_ball (half_lt_self hε) hw)⟩

/-- Degree-zero differentiation used for the conic mixed and averaged gaps. -/
private theorem fderiv_smul_of_homogeneous {f : (ℝ × U) → E} {D : Set (ℝ × U)} (hD : IsOpen D)
    (hf : ∀ η ∈ D, DifferentiableAt ℝ f η)
    (hscale : ∀ η ∈ D, ∀ r : ℝ, 0 < r → r • η ∈ D)
    (hhom : ∀ η ∈ D, ∀ r : ℝ, 0 < r → f (r • η) = r • f η)
    {η : ℝ × U} (hη : η ∈ D) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ f (r • η) = fderiv ℝ f η := by
  have he : (fun θ ↦ f (r • θ)) =ᶠ[𝓝 η] (fun θ ↦ r • f θ) := by
    filter_upwards [hD.mem_nhds hη] with θ hθ using hhom θ hθ r hr
  have hd := ((hf (r • η) (hscale η hη r hr)).hasFDerivAt.comp η
    ((hasFDerivAt_id η).const_smul r)).congr_of_eventuallyEq he.symm
  have hd' := (hf η hη).hasFDerivAt.const_smul r
  have heq := hd.unique hd'
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : (ℝ × U) →L[ℝ] E ↦ L v) heq
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul] at hv
  exact (smul_right_injective E hr.ne') hv

/-- Initial-root compatibility under positive scaling follows from the exact
energy equation and uniqueness in the scalar band
(`app:lem:common-hamilton-phase`). Both parameter and band memberships are
retained; `exists_uniform_C1_stable_sectionRoot` supplies these root hypotheses. -/
theorem sectionRoot_smul_of_unique
    (H : HomogeneousSymbol E) (hH : H.ConicHomogeneous)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {g : InitialData U → ℝ}
    {P : Set (InitialData U)} {I : Set ℝ}
    (hroot : ∀ s ∈ P, transverseSectionState j ν (s, g s) ∈ H.domain ∧
      H.h (transverseSectionState j ν (s, g s)) = s.2.1)
    (hunique : ∀ s ∈ P, ∀ τ ∈ I,
      H.h (transverseSectionState j ν (s, τ)) = s.2.1 ↔ g s = τ)
    {s : InitialData U} (hs : s ∈ P) {r : ℝ} (hr : 0 < r)
    (hrs : scaleSectionData r s ∈ P) (hband : r * g s ∈ I) :
    g (scaleSectionData r s) = r * g s ∧
      sectionRootMomentum j ν g (scaleSectionData r s) =
        r • sectionRootMomentum j ν g s := by
  have he : g (scaleSectionData r s) = r * g s := by
    apply (hunique _ hrs _ hband).mp
    have hstate : transverseSectionState j ν (scaleSectionData r s, r * g s) =
        ((transverseSectionState j ν (s, g s)).1,
          r • (transverseSectionState j ν (s, g s)).2) := by
      simp [transverseSectionState, scaleSectionData, smul_add, mul_smul]
    rw [hstate, hH.scale_symbol _ (hroot s hs).1 r hr, (hroot s hs).2]
    rfl
  refine ⟨he, ?_⟩
  simp only [sectionRootMomentum, he]
  simp [scaleSectionData, smul_add, mul_smul]

/-- Energy-section momenta are determined by their normal component and their
pairings with the tangent section (`app:lem:common-hamilton-phase`). This also
identifies independently constructed initial data on a common transverse patch. -/
theorem sectionMomentum_eq_normal_add_tangent (j : U →ₗᵢ[ℝ] E) (ν p : E) (hν : ν ≠ 0)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    (η : U) (hp : ∀ v : U, ⟪p, j v⟫_ℝ = ⟪η, v⟫_ℝ) :
    p = (⟪ν, p⟫_ℝ / ⟪ν, ν⟫_ℝ) • ν + j η := by
  have hn : ⟪ν, ν⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hν
  have he : ⟪ν, p - (⟪ν, p⟫_ℝ / ⟪ν, ν⟫_ℝ) • ν - j η⟫_ℝ = 0 := by
    simp only [inner_sub_right, inner_smul_right, horth, div_mul_cancel₀ _ hn, sub_self]
  obtain ⟨v, hv⟩ := hspan _ he
  have hz : ⟪j v, j v⟫_ℝ = 0 := by
    conv_lhs => lhs; rw [hv]
    simp [inner_sub_left, inner_smul_left, horth, hp, j.inner_map_map]
  have hv0 : j v = 0 := inner_self_eq_zero.mp hz
  rw [hv] at hv0
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hv0)).trans (add_comm _ _)


private theorem initial_root_locally_homogeneous [CompleteSpace U]
    {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)
    {D : Set (E × E)} (hD : IsOpen D) (hH : ContDiffOn ℝ ∞ H.h D)
    (hstate : ∀ s ∈ Φ.parameters, (Φ.position (0, s), Φ.momentum (0, s)) ∈ D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s : InitialData U} (hs : s ∈ Φ.parameters) :
    let g := fun a ↦ ⟪ν, Φ.momentum (0, a)⟫_ℝ / ⟪ν, ν⟫_ℝ
    ∀ᶠ r : ℝ in 𝓝 1, g (scaleSectionData r s) = r * g s := by
  let g := fun a ↦ ⟪ν, Φ.momentum (0, a)⟫_ℝ / ⟪ν, ν⟫_ℝ
  have hg (a : InitialData U) (ha : a ∈ Φ.parameters) : DifferentiableAt ℝ g a := by
    simpa only [g, div_eq_mul_inv, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, innerSL_apply_apply, mul_comm, Function.comp_def] using
      ((((⟪ν, ν⟫_ℝ)⁻¹ • innerSL ℝ ν) : E →L[ℝ] ℝ).differentiableAt.comp a
        (((Φ.momentum_derivative 0 Φ.zero_mem_time a ha).differentiableAt).comp a
          (hasFDerivAt_prodMk_right (0 : ℝ) a).differentiableAt))

  have hrep (a : InitialData U) (ha : a ∈ Φ.parameters) :
      Φ.momentum (0, a) = sectionRootMomentum j ν g a :=
    sectionMomentum_eq_normal_add_tangent j ν _ hν horth hspan _
      (by simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using Φ.initial_momentum a ha)
  have hst (a : InitialData U) (ha : a ∈ Φ.parameters) :
      transverseSectionState j ν (a, g a) = (Φ.position (0, a), Φ.momentum (0, a)) := by
    rw [Φ.initial_position a ha, hj, hrep a ha]
    rfl
  have he (a : InitialData U) (ha : a ∈ Φ.parameters) :
      H.h (transverseSectionState j ν (a, g a)) = a.2.1 := by
    rw [hst a ha]; exact Φ.initial_energy a ha
  have hmem : transverseSectionState j ν (s, g s) ∈ H.domain := by
    rw [hst s hs]; exact Φ.state_mem 0 Φ.zero_mem_time s hs
  have htrans : ⟪H.hp (transverseSectionState j ν (s, g s)), ν⟫_ℝ ≠ 0 := by
    have hd := (H.hasFDerivAt_h _ hmem).comp s
      ((j.toContinuousLinearMap.hasFDerivAt.comp s
        (ContinuousLinearMap.fst ℝ U (ℝ × U)).hasFDerivAt).prodMk
        (((hg s hs).hasFDerivAt.smul_const ν).add
          (j.toContinuousLinearMap.hasFDerivAt.comp s
            ((ContinuousLinearMap.snd ℝ ℝ U).hasFDerivAt.comp s
              (ContinuousLinearMap.snd ℝ U (ℝ × U)).hasFDerivAt))))
    have heq : (fun a ↦ H.h (j a.1, g a • ν + j a.2.2)) =ᶠ[𝓝 s]
        (fun a : InitialData U ↦ a.2.1) := by
      filter_upwards [Φ.isOpen_parameters.mem_nhds hs] with a ha using he a ha
    have hd' := (hd.congr_of_eventuallyEq heq.symm).unique
      ((ContinuousLinearMap.fst ℝ ℝ U).hasFDerivAt.comp s
        (ContinuousLinearMap.snd ℝ U (ℝ × U)).hasFDerivAt)
    have hv := congrArg (fun L : InitialData U →L[ℝ] ℝ ↦ L (0, (1, 0))) hd'
    intro hz
    simp [hamiltonDifferential_apply, inner_smul_right, hz] at hv
  let f := sectionEnergyEquation H j ν
  have hf : ContDiffAt ℝ ∞ f (s, g s) := by
    apply ((hH.contDiffAt (hD.mem_nhds (hst s hs ▸ hstate s hs))).comp
      (s, g s) (contDiff_transverseSectionState j ν).contDiffAt).sub
        contDiffAt_fst.snd.fst
  have hfzero : f (s, g s) = 0 := sub_eq_zero.mpr (he s hs)
  have hfd : CharacteristicRoot.scalarDerivative f (s, g s) ≠ 0 := by
    rw [scalarDerivative_sectionEnergyEquation H j ν hmem]; exact htrans
  have huniq := CharacteristicRoot.localRoot_eventually_unique hf hfd hfzero
  have hscale : Tendsto (fun r : ℝ ↦ scaleSectionData r s) (𝓝 1) (𝓝 s) := by
    simpa only [scaleSectionData_one] using
      (continuousAt_const.prodMk (continuousAt_id.smul continuousAt_const)).tendsto
        (f := fun r : ℝ ↦ scaleSectionData r s) (x := 1)
  have hgscale := (hg s hs).continuousAt.tendsto.comp hscale
  have hpath : Tendsto (fun r : ℝ ↦ (scaleSectionData r s, g (scaleSectionData r s)))
      (𝓝 1) (𝓝 (s, g s)) := hscale.prodMk_nhds hgscale
  have hpath' : Tendsto (fun r : ℝ ↦ (scaleSectionData r s, r * g s))
      (𝓝 1) (𝓝 (s, g s)) := by
    exact hscale.prodMk_nhds (by simpa using
      (continuousAt_id.mul continuousAt_const).tendsto (x := 1) (f := fun r : ℝ ↦ r * g s))
  filter_upwards [hpath.eventually huniq, hpath'.eventually huniq,
    hscale.eventually (Φ.isOpen_parameters.mem_nhds hs), H.homogeneous _ hmem]
    with r hr hr' hrs hhom
  have he' : f (scaleSectionData r s, r * g s) = 0 := by
    have hst' : transverseSectionState j ν (scaleSectionData r s, r * g s) =
        ((transverseSectionState j ν (s, g s)).1,
          r • (transverseSectionState j ν (s, g s)).2) := by
      simp [transverseSectionState, scaleSectionData, smul_add, mul_smul]
    change H.h (transverseSectionState j ν (scaleSectionData r s, r * g s)) - r * s.2.1 = 0
    rw [hst', hhom, he s hs, sub_self]
  exact (hr.mp (sub_eq_zero.mpr (he _ hrs))).symm.trans (hr'.mp he')


private theorem initialRoot_homogeneous_on_convex
    {P : Set (InitialData U)} (hP : IsOpen P) (hPc : Convex ℝ P)
    {g : InitialData U → ℝ}
    (hg : ∀ s ∈ P, ∀ᶠ r : ℝ in 𝓝 1, g (scaleSectionData r s) = r * g s)
    {s : InitialData U} (hs : s ∈ P) {r : ℝ} (hr : 0 < r)
    (hrs : scaleSectionData r s ∈ P) : g (scaleSectionData r s) = r * g s := by
  let I : Set ℝ := {t | scaleSectionData t s ∈ P} ∩ Ioi 0
  have hscale : Continuous (fun t : ℝ ↦ scaleSectionData t s) :=
    continuous_const.prodMk (continuous_id.smul continuous_const)
  have hI : IsOpen I := (hP.preimage hscale).inter isOpen_Ioi
  have hIc : Convex ℝ I := by
    apply Convex.inter ?_ (convex_Ioi 0)
    intro a ha b hb c d hc hd hcd
    have hh := hPc ha hb hc hd hcd
    change scaleSectionData (c • a + d • b) s ∈ P
    have he : scaleSectionData (c • a + d • b) s =
        c • scaleSectionData a s + d • scaleSectionData b s := by
      apply Prod.ext
      · simp [scaleSectionData, ← add_smul, hcd]
      · simp [scaleSectionData, add_smul, mul_smul]
    rwa [he]
  have h1 : (1 : ℝ) ∈ I := ⟨by simpa using hs, by norm_num⟩
  have hrI : r ∈ I := ⟨hrs, hr⟩
  let q : ℝ → ℝ := fun t ↦ g (scaleSectionData t s) / t
  have hq : ∀ t ∈ I, HasDerivAt q 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.2
    have hc : Tendsto (fun a : ℝ ↦ a / t) (𝓝 t) (𝓝 1) := by
      simpa [ht0] using ((continuousAt_id : ContinuousAt (fun a : ℝ ↦ a) t).div_const t).tendsto
    have he : q =ᶠ[𝓝 t] (fun _ ↦ q t) := by
      filter_upwards [hc.eventually (hg _ ht.1),
        eventually_ne_nhds ht0] with a ha ha0
      dsimp [q]
      have heq : g (scaleSectionData a s) = a / t * g (scaleSectionData t s) := by
        simpa [div_mul_cancel₀ _ ht0] using ha
      rw [heq]
      field_simp
    exact (hasDerivAt_const t (q t)).congr_of_eventuallyEq he
  have he := hI.is_const_of_deriv_eq_zero hIc.isPreconnected
    (fun t ht ↦ (hq t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hq t ht).deriv) hrI h1
  have he' : g (scaleSectionData r s) / r = g s := by simpa [q] using he
  exact (div_eq_iff (ne_of_gt hr)).mp he' |>.trans (mul_comm _ _)


/-- Initial momentum scaling follows from the energy equation and local scalar
root uniqueness on any convex section patch (`app:lem:common-hamilton-phase`).
This applies to the actual common family flow without a supplied root branch. -/
theorem HamiltonFlow.initial_momentum_smul_of_section [CompleteSpace U]
    {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U)
    {D : Set (E × E)} (hD : IsOpen D) (hH : ContDiffOn ℝ ∞ H.h D)
    (hstate : ∀ s ∈ Φ.parameters, (Φ.position (0, s), Φ.momentum (0, s)) ∈ D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {P : Set (InitialData U)} (hP : IsOpen P) (hPc : Convex ℝ P) (hPsub : P ⊆ Φ.parameters)
    {s : InitialData U} (hs : s ∈ P) {r : ℝ} (hr : 0 < r)
    (hrs : scaleSectionData r s ∈ P) :
    Φ.momentum (0, scaleSectionData r s) = r • Φ.momentum (0, s) := by
  let g := fun a ↦ ⟪ν, Φ.momentum (0, a)⟫_ℝ / ⟪ν, ν⟫_ℝ
  have hg : g (scaleSectionData r s) = r * g s :=
    initialRoot_homogeneous_on_convex hP hPc
      (fun a ha ↦ initial_root_locally_homogeneous Φ hD hH hstate j ν hν hj horth hspan
        (hPsub ha)) hs hr hrs
  have hrep (a : InitialData U) (ha : a ∈ P) :
      Φ.momentum (0, a) = sectionRootMomentum j ν g a :=
    sectionMomentum_eq_normal_add_tangent j ν _ hν horth hspan _
      (by simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using Φ.initial_momentum a (hPsub ha))
  rw [hrep _ hrs, hrep _ hs]
  simp only [sectionRootMomentum, hg]
  simp [scaleSectionData, smul_add, mul_smul]


private theorem solution_eqOn_on_symbolPatch
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : F → F} {D : Set F} (hD : IsOpen D) (hV : ContDiffOn ℝ 1 V D)
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → F} (hf : ∀ t ∈ I, HasDerivAt f (V (f t)) t)
    (hg : ∀ t ∈ I, HasDerivAt g (V (g t)) t)
    (hfm : ∀ t ∈ I, f t ∈ D) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (heq : f t₀ = g t₀) : EqOn f g I := by
  let S := {t | f t = g t} ∩ I
  have hlocal (t : ℝ) (ht : t ∈ S) : f =ᶠ[𝓝 t] g := by
    obtain ⟨K, B, hB, hVB⟩ :=
      ((hV (f t) (hfm t ht.2)).contDiffAt
        (hD.mem_nhds (hfm t ht.2))).exists_lipschitzOnWith
    have hfb : ∀ᶠ s in 𝓝 t, f s ∈ B := (hf t ht.2).continuousAt hB
    have hgb : ∀ᶠ s in 𝓝 t, g s ∈ B := (hg t ht.2).continuousAt (ht.1 ▸ hB)
    have htime : ∀ᶠ s in 𝓝 t, s ∈ I := hI.mem_nhds ht.2
    exact ODE_solution_unique_of_eventually (v := fun _ ↦ V) (s := fun _ ↦ B)
      (Eventually.of_forall (fun _ ↦ hVB))
      ((htime.and hfb).mono (fun s hs ↦ ⟨hf s hs.1, hs.2⟩))
      ((htime.and hgb).mono (fun s hs ↦ ⟨hg s hs.1, hs.2⟩)) ht.1
  have hSo : IsOpen S := isOpen_iff_mem_nhds.mpr fun t ht ↦
    (hlocal t ht).and (hI.mem_nhds ht.2)
  have hSc : closure S ∩ I ⊆ S := by
    intro t ht
    refine ⟨?_, ht.2⟩
    apply sub_eq_zero.mp
    exact ((hf t ht.2).continuousAt.sub (hg t ht.2).continuousAt).continuousWithinAt
      |>.eq_const_of_mem_closure ht.1 (fun y hy ↦ sub_eq_zero.mpr hy.1)
  have hsub := hIc.subset_of_closure_inter_subset hSo ⟨t₀, ht₀, heq, ht₀⟩ hSc
  exact fun t ht ↦ (hsub ht).1

/-- ODE scaling using smoothness only on the actual common state patch
(`app:lem:common-hamilton-phase`). The compared scaled curve may leave this
patch; the unscaled symbol itself is defined on its full conic domain. -/
theorem HamiltonFlow.state_smul_on_symbolPatch {H : HomogeneousSymbol E} (Φ : HamiltonFlow H U) (hH : H.ConicHomogeneous)
    {D : Set (E × E)} (hD : IsOpen D)
    (hstate : ∀ t ∈ Φ.time, ∀ s ∈ Φ.parameters,
      (Φ.position (t, s), Φ.momentum (t, s)) ∈ D)
    (hfield : ContDiffOn ℝ 1 H.vectorField D)
    {u : U} {η : ℝ × U} {r : ℝ} (hr : 0 < r)
    (hs : (u, η) ∈ Φ.parameters) (hrs : (u, r • η) ∈ Φ.parameters)
    (hinit : Φ.momentum (0, (u, r • η)) = r • Φ.momentum (0, (u, η)))
    {t : ℝ} (ht : t ∈ Φ.time) :
    (Φ.position (t, (u, r • η)), Φ.momentum (t, (u, r • η))) =
      (Φ.position (t, (u, η)), r • Φ.momentum (t, (u, η))) := by
  let f : ℝ → E × E := fun a ↦
    (Φ.position (a, (u, r • η)), Φ.momentum (a, (u, r • η)))
  let g : ℝ → E × E := fun a ↦
    covectorScaling r (Φ.position (a, (u, η)), Φ.momentum (a, (u, η)))
  have hf (a : ℝ) (ha : a ∈ Φ.time) : HasDerivAt f (H.vectorField (f a)) a :=
    (Φ.position_hasDerivAt ha hrs).prodMk (Φ.momentum_hasDerivAt ha hrs)
  have hg (a : ℝ) (ha : a ∈ Φ.time) : HasDerivAt g (H.vectorField (g a)) a := by
    have hd := (covectorScaling (E := E) r).hasFDerivAt.comp_hasDerivAt a
      ((Φ.position_hasDerivAt ha hs).prodMk (Φ.momentum_hasDerivAt ha hs))
    change HasDerivAt g (H.vectorField (covectorScaling r
      (Φ.position (a, (u, η)), Φ.momentum (a, (u, η))))) a
    rw [H.vectorField_smul hH (Φ.state_mem a ha (u, η) hs) hr]
    exact hd
  have hi : f 0 = g 0 := by
    apply Prod.ext
    · exact (Φ.initial_position _ hrs).trans (Φ.initial_position _ hs).symm
    · exact hinit
  exact solution_eqOn_on_symbolPatch hD hfield Φ.isOpen_time
    Φ.isPreconnected_time hf hg (fun a ha ↦ hstate a ha _ hrs)
    Φ.zero_mem_time hi ht


/-- Root uniqueness and ODE uniqueness give scaling compatibility for an
actual chart on a convex section patch (`app:lem:common-hamilton-phase`).
The scaled lift must belong to the actual source. -/
theorem ProjectionChart.coordinates_smul_of_sectionData [CompleteSpace E] [CompleteSpace U]
    {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U} (C : ProjectionChart Φ)
    {D : Set (E × E)} (hD : IsOpen D) (hDH : D ⊆ H.domain)
    (hH : ContDiffOn ℝ ∞ H.h D) (hconic : H.ConicHomogeneous)
    (hstate : ∀ t ∈ Φ.time, ∀ s ∈ Φ.parameters,
      (Φ.position (t, s), Φ.momentum (t, s)) ∈ D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (hν : ν ≠ 0)
    (hj : Φ.sectionMap = j.toContinuousLinearMap)
    (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {P : Set (InitialData U)} (hP : IsOpen P) (hPc : Convex ℝ P)
    (hPsub : P ⊆ Φ.parameters) (hsource : ∀ q ∈ C.source, q.2 ∈ P)
    {z : E × (ℝ × U)} (hz : z ∈ C.target) {r : ℝ} (hr : 0 < r)
    (hs : ((C.coordinates z).1, ((C.coordinates z).2, r • z.2)) ∈ C.source) :
    C.coordinates (z.1, r • z.2) = C.coordinates z := by
  have ha := C.source_admissible _ (C.maps_to_source _ hz)
  have hra := C.source_admissible _ hs
  have hinit := Φ.initial_momentum_smul_of_section hD hH
    (hstate 0 Φ.zero_mem_time) j ν hν hj horth hspan hP hPc hPsub
    (hsource _ (C.maps_to_source _ hz)) hr (hsource _ hs)
  apply C.coordinates_smul hz hs
  exact congrArg Prod.fst (Φ.state_smul_on_symbolPatch hconic hD hstate
    (H.contDiffOn_vectorField_of_subset hD hDH (hH.of_le (by simp))) hr ha.2 hra.2 hinit ha.1)


namespace ProjectionChart

variable {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U} (C : ProjectionChart Φ)

/-- Root uniqueness and Hamilton ODE uniqueness discharge the scaling premises
of the local inverse chart (`app:lem:common-hamilton-phase`). The root's scalar
band and the actual scaled-source membership remain explicit, as required for
the root and chart left inverses. No phase or flow scaling is an input. -/
theorem coordinates_smul_of_sectionRoot_unique (hH : H.ConicHomogeneous)
    (hfield : ContDiffOn ℝ 1 H.vectorField H.domain)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {g : InitialData U → ℝ}
    {P : Set (InitialData U)} {I : Set ℝ}
    (hroot : ∀ s ∈ P, transverseSectionState j ν (s, g s) ∈ H.domain ∧
      H.h (transverseSectionState j ν (s, g s)) = s.2.1)
    (hunique : ∀ s ∈ P, ∀ τ ∈ I,
      H.h (transverseSectionState j ν (s, τ)) = s.2.1 ↔ g s = τ)
    (hinitial : ∀ s ∈ Φ.parameters, Φ.momentum (0, s) = sectionRootMomentum j ν g s)
    {x : E} {η : ℝ × U} {r : ℝ} (hr : 0 < r) (hz : (x, η) ∈ C.target)
    (hs : ((C.coordinates (x, η)).1, ((C.coordinates (x, η)).2, r • η)) ∈ C.source)
    (hP : ((C.coordinates (x, η)).2, η) ∈ P)
    (hrP : ((C.coordinates (x, η)).2, r • η) ∈ P)
    (hband : r * g ((C.coordinates (x, η)).2, η) ∈ I) :
    C.coordinates (x, r • η) = C.coordinates (x, η) := by
  apply C.coordinates_smul_of_initial_momentum hH hfield hr hz hs
  have hi := hinitial _ (C.source_admissible _ (C.maps_to_source _ hz)).2
  change Φ.momentum (0, ((C.coordinates (x, η)).2, η)) = _ at hi
  rw [hinitial _ (C.source_admissible _ hs).2, hi]
  exact (sectionRoot_smul_of_unique H hH j ν hroot hunique hP hr hrP hband).2

end ProjectionChart

namespace ProjectionChart

variable {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U} (C : ProjectionChart Φ)

/-- The actual degree-one extension of the local Hamilton phase, normalized in
canonical variables (`app:lem:common-hamilton-phase`). -/
def conicPhase (ℓ : (ℝ × U) →L[ℝ] ℝ) : E × (ℝ × U) → ℝ :=
  CharacteristicRoot.homogeneousExtension ℓ (phase C.coordinates)

/-- Smoothness of the actual continued phase on its open conic domain
(`app:lem:common-hamilton-phase`). -/
theorem contDiffOn_conicPhase (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target) :
    ContDiffOn ℝ ∞ (C.conicPhase ℓ) (CharacteristicRoot.conicDomain ℓ C.target) :=
  CharacteristicRoot.contDiffOn_homogeneousExtension ℓ C.isOpen_target
    (C.contDiffOn_phase hC)

/-- Positive homogeneity holds at every scale for the constructed phase
(`app:lem:common-hamilton-phase`). -/
theorem conicPhase_smul (ℓ : (ℝ × U) →L[ℝ] ℝ) (z : E × (ℝ × U))
    {r : ℝ} (hr : 0 < r) :
    C.conicPhase ℓ (z.1, r • z.2) = r * C.conicPhase ℓ z :=
  CharacteristicRoot.homogeneousExtension_smul ℓ (phase C.coordinates) z hr

/-- The continuation restricts to the given phase on the normalization slice
(`app:lem:common-hamilton-phase`). Agreement on an open overlap additionally
uses local radial compatibility. -/
theorem conicPhase_eq_on_slice (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {z : E × (ℝ × U)} (hz : ℓ z.2 = 1) :
    C.conicPhase ℓ z = phase C.coordinates z := by
  simp [conicPhase, CharacteristicRoot.homogeneousExtension,
    CharacteristicRoot.normalize, hz]

/-- The physical differential of the continued phase is its scaled local
Hamilton momentum (`app:ch_regular_base:eq:actual-eikonal`). -/
theorem hasFDerivAt_conicPhase_position (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {z : E × (ℝ × U)} (hz : z ∈ CharacteristicRoot.conicDomain ℓ C.target) :
    HasFDerivAt (fun x ↦ C.conicPhase ℓ (x, z.2))
      (innerSL ℝ (ℓ z.2 • C.chartMomentum (CharacteristicRoot.normalize ℓ z))) z.1 := by
  have ha := C.source_admissible _ (C.maps_to_source _ hz.2)
  have hd := Φ.hasFDerivAt_phase_position
    (C.hasFDerivAt_coordinates _ hz.2) ha.1 ha.2
    (eventuallyEq_of_mem (C.isOpen_target.mem_nhds hz.2)
      (fun w hw ↦ C.right_inverse w hw))
  convert! hd.const_mul (ℓ z.2) using 1
  ext v
  simp [chartMomentum]

/-- The exact eikonal equation and symbol-domain membership survive positive
conic continuation (`app:ch_regular_base:eq:actual-eikonal`). No equation is
asserted outside the normalized chart or the symbol's conic domain. -/
theorem conicPhase_eikonal [CompleteSpace E] (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hH : H.ConicHomogeneous) {z : E × (ℝ × U)}
    (hz : z ∈ CharacteristicRoot.conicDomain ℓ C.target) :
    (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) ∈ H.domain ∧
      H.h (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) = z.2.1 := by
  have hg : HasGradientAt (fun x ↦ C.conicPhase ℓ (x, z.2))
      (ℓ z.2 • C.chartMomentum (CharacteristicRoot.normalize ℓ z)) z.1 :=
    C.hasFDerivAt_conicPhase_position ℓ hz
  rw [hg.gradient]
  have ha := C.source_admissible _ (C.maps_to_source _ hz.2)
  have hmem := Φ.state_mem _ ha.1 _ ha.2
  have he := Φ.energy ha.1 ha.2
  rw [C.right_inverse _ hz.2] at hmem he
  change (z.1, C.chartMomentum (CharacteristicRoot.normalize ℓ z)) ∈ H.domain at hmem
  change H.h (z.1, C.chartMomentum (CharacteristicRoot.normalize ℓ z)) =
    (ℓ z.2)⁻¹ * z.2.1 at he
  refine ⟨hH.scale_mem _ hmem _ hz.1, ?_⟩
  rw [hH.scale_symbol _ hmem _ hz.1]
  rw [he]
  change ℓ z.2 * ((ℓ z.2)⁻¹ * z.2.1) = z.2.1
  rw [← mul_assoc, mul_inv_cancel₀ hz.1.ne', one_mul]

/-- Radial compatibility of the actual phase on a convex canonical patch follows
from its proved canonical differential and Euler identity
(`app:lem:common-hamilton-phase`). No phase scaling is assumed. -/
theorem phase_smul_on_convex {P : Set (ℝ × U)} (hP : IsOpen P) (hPc : Convex ℝ P)
    {x : E} (hPt : ∀ η ∈ P, (x, η) ∈ C.target)
    {η : ℝ × U} (hη : η ∈ P) {r : ℝ} (hr : 0 < r) (hrη : r • η ∈ P) :
    phase C.coordinates (x, r • η) = r * phase C.coordinates (x, η) := by
  let I : Set ℝ := {t | t • η ∈ P} ∩ Ioi 0
  have hI : IsOpen I := (hP.preimage (continuous_id.smul continuous_const)).inter isOpen_Ioi
  have hIc : Convex ℝ I := by
    refine Convex.inter ?_ (convex_Ioi 0)
    intro a ha b hb c d hc hd hcd
    change (c • a + d • b) • η ∈ P
    simpa only [smul_smul, add_smul, smul_eq_mul] using hPc ha hb hc hd hcd
  have h1 : (1 : ℝ) ∈ I := ⟨by simpa using hη, by norm_num⟩
  have hrI : r ∈ I := ⟨hrη, hr⟩
  let q : ℝ → ℝ := fun t ↦ phase C.coordinates (x, t • η) / t
  have hq : ∀ t ∈ I, HasDerivAt q 0 t := by
    intro t ht
    have hd := (C.hasFDerivAt_phase_canonical (hPt _ ht.1)).comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const η)
    have hnum : canonicalCovector (C.coordinates (x, t • η)) η * t -
        phase C.coordinates (x, t • η) * 1 = 0 := by
      simp only [canonicalCovector_apply, phase, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, inner_smul_right]
      ring
    convert! hd.div (hasDerivAt_id t) ht.2.ne' using 1
    simp only [one_smul, Function.comp_apply, id_eq, hnum, zero_div]
  have he := hI.is_const_of_deriv_eq_zero hIc.isPreconnected
    (fun t ht ↦ (hq t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hq t ht).deriv) hrI h1
  have he' : phase C.coordinates (x, r • η) / r = phase C.coordinates (x, η) := by
    simpa [q] using he
  exact (div_eq_iff hr.ne').mp he' |>.trans (mul_comm _ _)

/-- Agreement on an open overlap whenever both canonical representatives lie
in the same convex local patch (`app:lem:common-hamilton-phase`). -/
theorem conicPhase_eq_of_mem_convex (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {P : Set (ℝ × U)} (hP : IsOpen P) (hPc : Convex ℝ P)
    {x : E} (hPt : ∀ η ∈ P, (x, η) ∈ C.target)
    {η : ℝ × U} (hη : η ∈ P) (hℓ : 0 < ℓ η)
    (hn : (ℓ η)⁻¹ • η ∈ P) : C.conicPhase ℓ (x, η) = phase C.coordinates (x, η) := by
  have he := C.phase_smul_on_convex hP hPc hPt hη (inv_pos.mpr hℓ) hn
  change ℓ η * phase C.coordinates (x, (ℓ η)⁻¹ • η) = _
  rw [he, ← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul]

/-- The continued gradient is the normalized local momentum
(`app:ch_regular_base:eq:actual-eikonal`). -/
theorem gradient_conicPhase [CompleteSpace E] (ℓ : (ℝ × U) →L[ℝ] ℝ) {z : E × (ℝ × U)}
    (hz : z ∈ CharacteristicRoot.conicDomain ℓ C.target) :
    gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1 =
      ℓ z.2 • C.chartMomentum (CharacteristicRoot.normalize ℓ z) :=
  (show HasGradientAt _ _ _ from C.hasFDerivAt_conicPhase_position ℓ hz).gradient
/-- The physical gradient has positive degree one in canonical momentum
(`app:lem:common-hamilton-phase`). -/
theorem gradient_conicPhase_smul [CompleteSpace E] (ℓ : (ℝ × U) →L[ℝ] ℝ) {z : E × (ℝ × U)}
    (hz : z ∈ CharacteristicRoot.conicDomain ℓ C.target) {r : ℝ} (hr : 0 < r) :
    gradient (fun x ↦ C.conicPhase ℓ (x, r • z.2)) z.1 =
      r • gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1 := by
  rw [C.gradient_conicPhase ℓ (CharacteristicRoot.mem_conicDomain_smul ℓ C.target hz hr),
    C.gradient_conicPhase ℓ hz, CharacteristicRoot.normalize_smul ℓ z hr.ne']
  simp [smul_smul]

/-- Joint smoothness of the continued physical gradient, used for the mixed
derivative on the cone (`app:lem:common-hamilton-phase`). -/
theorem contDiffOn_gradient_conicPhase [CompleteSpace E] (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target) :
    ContDiffOn ℝ ∞ (fun z : E × (ℝ × U) ↦
      gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1)
        (CharacteristicRoot.conicDomain ℓ C.target) := by
  have hlocal : ContDiffOn ℝ ∞ (fun z ↦ ℓ z.2 •
      C.chartMomentum (CharacteristicRoot.normalize ℓ z))
      (CharacteristicRoot.conicDomain ℓ C.target) := by
    intro z hz
    exact ((ℓ.contDiff.contDiffAt.comp z contDiffAt_snd).smul
      (((C.contDiffOn_chartMomentum hp hC).contDiffAt
        (C.isOpen_target.mem_nhds hz.2)).comp z
          (CharacteristicRoot.contDiffAt_normalize ℓ hz.1.ne'))).contDiffWithinAt
  exact hlocal.congr (fun z hz ↦ C.gradient_conicPhase ℓ hz)

/-- On the open overlap the continued gradient is the actual local momentum
(`app:ch_regular_base:eq:actual-eikonal`). -/
theorem gradient_conicPhase_eq_on_overlap [CompleteSpace E] (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {B : Set E} {P : Set (ℝ × U)} (hB : IsOpen B)
    (hP : IsOpen P) (hPc : Convex ℝ P) (hsub : B ×ˢ P ⊆ C.target)
    {z : E × (ℝ × U)} (hz : z ∈ (B ×ˢ P) ∩ CharacteristicRoot.conicDomain ℓ (B ×ˢ P)) :
    gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1 = C.chartMomentum z := by
  have he : (fun x ↦ C.conicPhase ℓ (x, z.2)) =ᶠ[𝓝 z.1]
      (fun x ↦ phase C.coordinates (x, z.2)) := by
    filter_upwards [hB.mem_nhds hz.1.1] with x hx
    exact C.conicPhase_eq_of_mem_convex ℓ hP hPc (fun η hη ↦ hsub ⟨hx, hη⟩)
      hz.1.2 hz.2.1 hz.2.2.2
  exact he.gradient_eq.trans (C.gradient_phase_eq_chartMomentum (hsub hz.1))

/-- The mixed derivative is invariant under every positive canonical dilation
(`app:lem:common-hamilton-phase`). -/
theorem fderiv_gradient_conicPhase_smul [CompleteSpace E] (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {z : E × (ℝ × U)} (hz : z ∈ CharacteristicRoot.conicDomain ℓ C.target)
    {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (fun η ↦ gradient (fun x ↦ C.conicPhase ℓ (x, η)) z.1) (r • z.2) =
      fderiv ℝ (fun η ↦ gradient (fun x ↦ C.conicPhase ℓ (x, η)) z.1) z.2 := by
  let f : (ℝ × U) → E := fun η ↦ gradient (fun x ↦ C.conicPhase ℓ (x, η)) z.1
  let D : Set (ℝ × U) := {η | (z.1, η) ∈ CharacteristicRoot.conicDomain ℓ C.target}
  have hD : IsOpen D := (CharacteristicRoot.isOpen_conicDomain ℓ C.isOpen_target).preimage
    (continuous_const.prodMk continuous_id)
  have hf : ∀ η ∈ D, DifferentiableAt ℝ f η := by
    intro η hη
    exact (((C.contDiffOn_gradient_conicPhase ℓ hp hC).contDiffAt
      ((CharacteristicRoot.isOpen_conicDomain ℓ C.isOpen_target).mem_nhds hη)).differentiableAt
        (by simp)).comp η (hasFDerivAt_prodMk_right z.1 η).differentiableAt
  exact fderiv_smul_of_homogeneous hD hf
    (fun _ hη _ hr ↦ CharacteristicRoot.mem_conicDomain_smul ℓ C.target hη hr)
    (fun _ hη _ hr ↦ C.gradient_conicPhase_smul ℓ hη hr) hz hr

/-- Agreement on a closed overlap buffer shared by every chart containing
these same boxes (`app:lem:common-hamilton-phase`). -/
theorem exists_conicPhase_overlap (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {B : Set E} {P : Set (ℝ × U)} (hB : IsOpen B)
    (hP : IsOpen P) (hPc : Convex ℝ P) (hsub : B ×ˢ P ⊆ C.target)
    {z : E × (ℝ × U)} (hz : z ∈ B ×ˢ P) (hℓ : ℓ z.2 = 1) :
    ∃ ε : ℝ, 0 < ε ∧ closedBall z ε ⊆
      (B ×ˢ P) ∩ CharacteristicRoot.conicDomain ℓ (B ×ˢ P) ∧
      ∀ w ∈ closedBall z ε, C.conicPhase ℓ w = phase C.coordinates w := by
  obtain ⟨ε, hε, hbuf⟩ := exists_normalization_buffer ℓ hB hP hz hℓ
  refine ⟨ε, hε, hbuf, ?_⟩
  intro w hw
  have hm := hbuf hw
  exact C.conicPhase_eq_of_mem_convex ℓ hP hPc (fun η hη ↦ hsub ⟨hm.1.1, hη⟩)
    hm.1.2 hm.2.1 hm.2.2.2

/-- The continued phase has the exact section value wherever the normalized
initial datum is in the actual chart source
(`app:ch_regular_base:eq:actual-eikonal`). -/
theorem conicPhase_initial_value (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {u : U} {η : ℝ × U} (hℓ : 0 < ℓ η)
    (hs : (0, (u, (ℓ η)⁻¹ • η)) ∈ C.source) :
    C.conicPhase ℓ (Φ.sectionMap u, η) = ⟪u, η.2⟫_ℝ := by
  change ℓ η * phase C.coordinates (Φ.sectionMap u, (ℓ η)⁻¹ • η) = _
  rw [C.initial_value hs]
  simp only [Prod.smul_snd, inner_smul_right]
  rw [← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul]

/-- The continued mixed derivative is exactly the local mixed derivative at
the normalized covector. This transfers the common local family gap to the cone
without increasing its constant (`app:lem:common-hamilton-phase`). -/
theorem fderiv_gradient_conicPhase_eq_normalized [CompleteSpace E] (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {B : Set E} {P : Set (ℝ × U)} (hB : IsOpen B)
    (hP : IsOpen P) (hPc : Convex ℝ P) (hsub : B ×ˢ P ⊆ C.target)
    {z : E × (ℝ × U)} (hz : z ∈ CharacteristicRoot.conicDomain ℓ (B ×ˢ P)) :
    fderiv ℝ (fun η ↦ gradient (fun x ↦ C.conicPhase ℓ (x, η)) z.1) z.2 =
      C.mixedMomentumDerivative (CharacteristicRoot.normalize ℓ z) := by
  have hzC : z ∈ CharacteristicRoot.conicDomain ℓ C.target := ⟨hz.1, hsub hz.2⟩
  rw [← C.fderiv_gradient_conicPhase_smul ℓ hp hC hzC (inv_pos.mpr hz.1)]
  let w := CharacteristicRoot.normalize ℓ z
  have hℓw : ℓ w.2 = 1 := by
    dsimp [w, CharacteristicRoot.normalize]
    simp [hz.1.ne']
  have hw : w ∈ (B ×ˢ P) ∩ CharacteristicRoot.conicDomain ℓ (B ×ˢ P) := by
    refine ⟨hz.2, ?_, ?_⟩
    · rw [hℓw]; norm_num
    · simpa [CharacteristicRoot.normalize, hℓw] using (show w ∈ B ×ˢ P from hz.2)
  have hopen : IsOpen ((B ×ˢ P) ∩ CharacteristicRoot.conicDomain ℓ (B ×ˢ P)) :=
    (hB.prod hP).inter (CharacteristicRoot.isOpen_conicDomain ℓ (hB.prod hP))
  have he : (fun η ↦ gradient (fun x ↦ C.conicPhase ℓ (x, η)) z.1) =ᶠ[𝓝 w.2]
      (fun η ↦ gradient (fun x ↦ phase C.coordinates (x, η)) z.1) := by
    have hn := (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      (hopen.mem_nhds hw)
    filter_upwards [hn] with η hη
    exact (C.gradient_conicPhase_eq_on_overlap ℓ hB hP hPc hsub hη).trans
      (C.gradient_phase_eq_chartMomentum (hsub hη.1)).symm
  exact he.fderiv_eq


/-- The canonical differential of the continued phase is the actual Hamilton
time and section point at the normalized covector
(`app:lem:common-hamilton-phase`). These coordinates have degree zero. -/
theorem hasFDerivAt_conicPhase_canonical (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {B : Set E} {P : Set (ℝ × U)} (hP : IsOpen P) (hPc : Convex ℝ P)
    (hsub : B ×ˢ P ⊆ C.target) {z : E × (ℝ × U)}
    (hz : z ∈ CharacteristicRoot.conicDomain ℓ (B ×ˢ P)) :
    HasFDerivAt (fun η ↦ C.conicPhase ℓ (z.1, η))
      (canonicalCovector (C.coordinates (CharacteristicRoot.normalize ℓ z))) z.2 := by
  let f : (ℝ × U) → ℝ := fun η ↦ C.conicPhase ℓ (z.1, η)
  let Q : Set (ℝ × U) := {η | (z.1, η) ∈ CharacteristicRoot.conicDomain ℓ C.target}
  have hQ : IsOpen Q := (CharacteristicRoot.isOpen_conicDomain ℓ C.isOpen_target).preimage
    (continuous_const.prodMk continuous_id)
  have hf : ∀ η ∈ Q, DifferentiableAt ℝ f η := by
    intro η hη
    exact (((C.contDiffOn_conicPhase ℓ hC).contDiffAt
      ((CharacteristicRoot.isOpen_conicDomain ℓ C.isOpen_target).mem_nhds hη)).differentiableAt
        (by simp)).comp η (hasFDerivAt_prodMk_right z.1 η).differentiableAt
  have hzQ : z.2 ∈ Q := ⟨hz.1, hsub hz.2⟩
  have hscale : fderiv ℝ f ((ℓ z.2)⁻¹ • z.2) = fderiv ℝ f z.2 :=
    fderiv_smul_of_homogeneous hQ hf
      (fun _ hη _ hr ↦ CharacteristicRoot.mem_conicDomain_smul ℓ C.target hη hr)
      (fun η _ r hr ↦ C.conicPhase_smul ℓ (z.1, η) hr) hzQ (inv_pos.mpr hz.1)
  let θ := (ℓ z.2)⁻¹ • z.2
  have hℓθ : ℓ θ = 1 := by simp [θ, hz.1.ne']
  have hn : ContinuousAt (fun η : ℝ × U ↦ (ℓ η)⁻¹ • η) θ :=
    ((ℓ.continuous.continuousAt).inv₀ (by rw [hℓθ]; norm_num)).smul continuousAt_id
  have hθP : θ ∈ P := hz.2.2
  have hnorm : ∀ᶠ η in 𝓝 θ, (ℓ η)⁻¹ • η ∈ P :=
    hn.preimage_mem_nhds (by simpa [hℓθ] using hP.mem_nhds hθP)
  have hpos : ∀ᶠ η in 𝓝 θ, 0 < ℓ η :=
    ℓ.continuous.continuousAt.eventually (lt_mem_nhds (show 0 < ℓ θ by rw [hℓθ]; norm_num))
  have he : f =ᶠ[𝓝 θ] (fun η ↦ phase C.coordinates (z.1, η)) := by
    filter_upwards [hP.mem_nhds hθP, hnorm, hpos] with η hη hnη hpη
    exact C.conicPhase_eq_of_mem_convex ℓ hP hPc
      (fun ξ hξ ↦ hsub ⟨hz.2.1, hξ⟩) hη hpη hnη
  have hd := (C.hasFDerivAt_phase_canonical (hsub hz.2)).congr_of_eventuallyEq he
  convert (hf _ hzQ).hasFDerivAt using 1
  exact hd.fderiv.symm.trans hscale

/-- The averaged gradients agree on the normalization overlap, so the local
inverse buffer transfers to the conic map (`app:ch_regular_base:eq:averaged-gradient`). -/
theorem conicAveragedGradient_eq_on_overlap [CompleteSpace E]
    (ℓ : (ℝ × U) →L[ℝ] ℝ)
    {B : Set E} {P : Set (ℝ × U)} (hB : IsOpen B) (hBc : Convex ℝ B)
    (hP : IsOpen P) (hPc : Convex ℝ P) (hsub : B ×ˢ P ⊆ C.target)
    {x y : E} (hx : x ∈ B) (hy : y ∈ B) {η : ℝ × U}
    (hη : η ∈ P ∩ canonicalCone ℓ P) :
    averagedPhaseGradient (fun θ x ↦ C.conicPhase ℓ (x, θ)) η x y =
      averagedPhaseGradient (fun θ x ↦ phase C.coordinates (x, θ)) η x y := by
  apply intervalIntegral.integral_congr
  intro t ht
  have hm : y + t • (x - y) ∈ B := hBc.add_smul_sub_mem hy hx (by simpa using ht)
  exact (C.gradient_conicPhase_eq_on_overlap ℓ hB hP hPc hsub
    (z := (y + t • (x - y), η)) ⟨⟨hm, hη.1⟩, hη.2.1, hm, hη.2.2⟩).trans
    (C.gradient_phase_eq_chartMomentum (hsub ⟨hm, hη.1⟩)).symm

private theorem averagedDerivativeGap_for_conicBuffer [CompleteSpace E] [FiniteDimensional ℝ U]
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {V : Set (ℝ × U)} (hV : IsOpen V) {x y : E}
    (hseg : ∀ η ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      (y + t • (x - y), η) ∈ C.target)
    (A : (ℝ × U) ≃L[ℝ] E) {c : ℝ} {η : ℝ × U} (hη : η ∈ V)
    (hgap : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
        (C.mixedMomentumDerivative (y + t • (x - y), η)) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ c) :
    ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (fderiv ℝ (fun η ↦ averagedPhaseGradient
        (fun η x ↦ phase C.coordinates (x, η)) η x y) η) -
      ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ c := by
  let : NormedSpace ℝ (ℝ × U) := inferInstance
  let : NormedAddCommGroup ((ℝ × U) →L[ℝ] E) := inferInstance
  let : NormedAddCommGroup ((ℝ × U) →L[ℝ] (ℝ × U)) := inferInstance
  rw [(C.hasFDerivAt_averagedPhaseGradient hp hC hV hseg hη).fderiv]
  have hc : ContinuousOn (fun t : ℝ ↦ C.mixedMomentumDerivative
      (y + t • (x - y), η)) (Icc 0 1) :=
    (C.continuousOn_mixedMomentumDerivative hp hC).comp (by fun_prop) (hseg η hη)
  let L := (ContinuousLinearMap.compL ℝ (ℝ × U) E (ℝ × U))
    (A.symm : E →L[ℝ] (ℝ × U))
  have hi : IntervalIntegrable (fun t : ℝ ↦ C.mixedMomentumDerivative
      (y + t • (x - y), η)) volume 0 1 := hc.intervalIntegrable_of_Icc zero_le_one
  change ‖L (∫ t in (0 : ℝ)..1, C.mixedMomentumDerivative
    (y + t • (x - y), η)) - ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ _
  have hL : (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
      (y + t • (x - y), η))) = L (∫ t in (0 : ℝ)..1,
        C.mixedMomentumDerivative (y + t • (x - y), η)) :=
    ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) L hi
  rw [← hL]
  have hiL : IntervalIntegrable (fun t ↦ L (C.mixedMomentumDerivative
      (y + t • (x - y), η))) volume 0 1 :=
    ⟨L.integrable_comp hi.1, L.integrable_comp hi.2⟩
  have he : (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
      (y + t • (x - y), η)) - ContinuousLinearMap.id ℝ (ℝ × U)) =
      (∫ t in (0 : ℝ)..1, L (C.mixedMomentumDerivative
        (y + t • (x - y), η))) - ContinuousLinearMap.id ℝ (ℝ × U) := by
    rw [intervalIntegral.integral_sub hiL intervalIntegrable_const]
    simp
  rw [← he]
  simpa [L] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := c)
    (fun t ht ↦ hgap t (by simpa using uIoc_subset_uIcc ht))

variable [CompleteSpace E] [FiniteDimensional ℝ U]

/-- The averaged gradient of the continued phase has exactly the local averaged
canonical derivative at the normalized covector. This is the degree-zero gap
transfer in `app:ch_regular_base:eq:averaged-gradient`. -/
theorem hasFDerivAt_conicAveragedGradient (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {B : Set E} {P : Set (ℝ × U)} (hB : IsOpen B) (hBc : Convex ℝ B)
    (hP : IsOpen P) (hPc : Convex ℝ P) (hsub : B ×ˢ P ⊆ C.target)
    {x y : E} (hx : x ∈ B) (hy : y ∈ B) {η : ℝ × U}
    (hη : η ∈ canonicalCone ℓ P) :
    HasFDerivAt
      (fun θ ↦ averagedPhaseGradient (fun θ x ↦ C.conicPhase ℓ (x, θ)) θ x y)
      (fderiv ℝ (fun θ ↦ averagedPhaseGradient
        (fun θ x ↦ phase C.coordinates (x, θ)) θ x y) ((ℓ η)⁻¹ • η)) η := by
  let Q := canonicalCone ℓ P
  have hQ : IsOpen Q := by
    simpa [Q, canonicalCone, CharacteristicRoot.conicDomain, CharacteristicRoot.normalize] using
      (CharacteristicRoot.isOpen_conicDomain ℓ (isOpen_univ.prod hP)).preimage
      (f := fun θ ↦ ((0 : E), θ)) (continuous_const.prodMk continuous_id)
  let F : ℝ × (ℝ × U) → E := fun q ↦
    gradient (fun x ↦ C.conicPhase ℓ (x, q.2)) (y + q.1 • (x - y))
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : y + t • (x - y) ∈ B :=
    hBc.add_smul_sub_mem hy hx ht
  have hF : ∀ q ∈ uIcc (0 : ℝ) 1 ×ˢ Q, ContDiffAt ℝ ∞ F q := by
    intro q hq
    have hm : (y + q.1 • (x - y), q.2) ∈
        CharacteristicRoot.conicDomain ℓ C.target :=
      ⟨hq.2.1, hsub ⟨hseg _ (by simpa using hq.1), hq.2.2⟩⟩
    exact ((C.contDiffOn_gradient_conicPhase ℓ hp hC).contDiffAt
      ((CharacteristicRoot.isOpen_conicDomain ℓ C.isOpen_target).mem_nhds hm)).comp
        (g := fun z : E × (ℝ × U) ↦ gradient
          (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1)
        (f := fun q : ℝ × (ℝ × U) ↦ (y + q.1 • (x - y), q.2)) q (by fun_prop)
  have hd := hasFDerivAt_fixedIntervalIntegral hQ hF hη
  have he : (∫ t in (0 : ℝ)..1,
      (fderiv ℝ F (t, η)).comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × U))) =
      ∫ t in (0 : ℝ)..1,
        C.mixedMomentumDerivative (y + t • (x - y), (ℓ η)⁻¹ • η) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hc := (((hF (t, η) ⟨ht, hη⟩).differentiableAt (by simp)).hasFDerivAt.comp η
      (hasFDerivAt_prodMk_right t η)).fderiv
    exact hc.symm.trans (C.fderiv_gradient_conicPhase_eq_normalized ℓ hp hC
      hB hP hPc hsub (z := (y + t • (x - y), η)) ⟨hη.1, hseg t ht', hη.2⟩)
  rw [he] at hd
  rw [(C.hasFDerivAt_averagedPhaseGradient hp hC hP
    (fun θ hθ t ht ↦ hsub ⟨hseg t ht, hθ⟩) hη.2).fderiv]
  exact hd

/-- The local family averaged derivative gap transfers with its exact constant
to the whole convex canonical cone (`app:lem:common-hamilton-phase`). -/
theorem conicAveragedGradient_derivative_gap (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {B : Set E} {P : Set (ℝ × U)} (hB : IsOpen B) (hBc : Convex ℝ B)
    (hP : IsOpen P) (hPc : Convex ℝ P) (hsub : B ×ˢ P ⊆ C.target)
    {x y : E} (hx : x ∈ B) (hy : y ∈ B) (A : (ℝ × U) ≃L[ℝ] E) {c : ℝ}
    (hgap : ∀ θ ∈ P, ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (fderiv ℝ (fun θ ↦ averagedPhaseGradient
        (fun θ x ↦ phase C.coordinates (x, θ)) θ x y) θ) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ c)
    {η : ℝ × U} (hη : η ∈ canonicalCone ℓ P) :
    ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (fderiv ℝ (fun θ ↦ averagedPhaseGradient
        (fun θ x ↦ C.conicPhase ℓ (x, θ)) θ x y) η) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ c := by
  rw [(C.hasFDerivAt_conicAveragedGradient ℓ hp hC hB hBc hP hPc hsub hx hy hη).fderiv]
  exact hgap _ hη.2

/-- The averaged-gradient canonical map is injective on the full convex cone,
with a quantitative separation estimate (`app:lem:common-hamilton-phase`). The
local gap is supplied by `exists_commonBufferedAveragedGradient`. -/
theorem conicAveragedGradient_injective (ℓ : (ℝ × U) →L[ℝ] ℝ)
    (hp : ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters))
    (hC : ContDiffOn ℝ ∞ C.coordinates C.target)
    {B : Set E} {P : Set (ℝ × U)} (hB : IsOpen B) (hBc : Convex ℝ B)
    (hP : IsOpen P) (hPc : Convex ℝ P) (hsub : B ×ˢ P ⊆ C.target)
    {x y : E} (hx : x ∈ B) (hy : y ∈ B) (A : (ℝ × U) ≃L[ℝ] E)
    (hgap : ∀ θ ∈ P, ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
      (fderiv ℝ (fun θ ↦ averagedPhaseGradient
        (fun θ x ↦ phase C.coordinates (x, θ)) θ x y) θ) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8) :
    let Ξ := fun θ ↦ averagedPhaseGradient (fun θ x ↦ C.conicPhase ℓ (x, θ)) θ x y
    InjOn Ξ (canonicalCone ℓ P) ∧
      ∀ η ∈ canonicalCone ℓ P, ∀ θ ∈ canonicalCone ℓ P,
        ‖η - θ‖ / 2 ≤ ‖A.symm (Ξ η - Ξ θ)‖ := by
  have hd := fun (η : ℝ × U) (hη : η ∈ canonicalCone ℓ P) ↦ (C.hasFDerivAt_conicAveragedGradient ℓ hp hC
    hB hBc hP hPc hsub hx hy hη).differentiableAt
  have hg := fun (η : ℝ × U) (hη : η ∈ canonicalCone ℓ P) ↦ (C.conicAveragedGradient_derivative_gap ℓ hp hC
    hB hBc hP hPc hsub hx hy A hgap (η := η) hη).trans (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)
  exact ⟨injOn_of_normalized_derivative_gap (convex_canonicalCone ℓ hPc) A hd hg,
    fun _ hη _ hθ ↦ normalized_lower_lipschitz_of_derivative_gap
      (convex_canonicalCone ℓ hPc) A hd hg hη hθ⟩

end ProjectionChart

variable [CompleteSpace E] [CompleteSpace U]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]

/-- Refine the local family inverse buffer inside the normalization overlap.
The mixed gap on the larger ball is retained for `exists_commonConicHamiltonPhases`
and the conic injectivity in `app:lem:common-hamilton-phase`. -/
private theorem exists_commonBufferedAveragedGradient_normalization
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (ℓ : (ℝ × U) →L[ℝ] ℝ) (hℓ : ℓ s₀.2 = 1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0)
    (targetRadius : ℝ → ℝ) (hTargetRadius : ∀ r > 0, 0 < targetRadius r) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀)
      (A : (ℝ × U) ≃L[ℝ] E) (r b ρ σ a δ K β : ℝ)
      (V : Set (E × (ℝ × U))) (W : Set E),
      0 < r ∧ 0 < b ∧ 0 < ρ ∧ 0 < σ ∧ 0 < a ∧ 0 < δ ∧ 0 < K ∧ 0 < β ∧
      ρ ≤ a ∧ 3 * a < targetRadius r ∧
      IsOpen V ∧ IsCompact (closure V) ∧ IsOpen W ∧ IsCompact (closure W) ∧
      closedBall (j s₀.1) (3 * ρ) ×ˢ closedBall s₀.2 (3 * a) ⊆ V ∧
      closedBall s₀.2 (3 * σ) ⊆ ball s₀.2 (3 * a) ∩
        canonicalCone ℓ (ball s₀.2 (3 * a)) ∧
      C₀.target = V ∧
      ContDiffOn ℝ ∞ Φ₀.momentum (Φ₀.time ×ˢ Φ₀.parameters) ∧
      ContDiffOn ℝ ∞ C₀.coordinates V ∧
      (A : (ℝ × U) →L[ℝ] E) = C₀.mixedMomentumDerivative (j s₀.1, s₀.2) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          let Ξ : E → E → (ℝ × U) → E := fun x y η ↦
            averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y
          Φ.time = Φ₀.time ∧ Φ.parameters = Φ₀.parameters ∧
          Φ.sectionMap = j.toContinuousLinearMap ∧
          ContDiffOn ℝ ∞ Φ.position (Φ.time ×ˢ Φ.parameters) ∧
          ContDiffOn ℝ ∞ Φ.momentum (Φ.time ×ˢ Φ.parameters) ∧
          (∀ q ∈ Φ.time ×ˢ Φ.parameters,
            (Φ.position q, Φ.momentum q) ∈ closedBall z₀ R) ∧
          C.target = V ∧
          C.source = ball ((0 : ℝ), s₀) (3 * r) ∩ Φ.augmentedProjection ⁻¹' V ∧
          C.source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          closure (ball ((0 : ℝ), s₀) (3 * r)) ⊆ Φ.time ×ˢ Φ.parameters ∧
          ContDiffOn ℝ ∞ C.coordinates V ∧
          cthickening b (Φ.augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ Φ.augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          Φ.augmentedProjection ⁻¹' cthickening b (closure V) ∩
            ball ((0 : ℝ), s₀) (3 * r) ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ z ∈ V, ‖C.mixedMomentumDerivative z - C₀.mixedMomentumDerivative z‖ ≤
            K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)) ∧
          (∀ z ∈ closedBall (j s₀.1) (3 * ρ) ×ˢ closedBall s₀.2 (3 * a),
            ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (C.mixedMomentumDerivative z) -
              ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8) ∧
          ContDiffOn ℝ ∞ (fun q : (E × E) × (ℝ × U) ↦ Ξ q.1.1 q.1.2 q.2)
            ((ball (j s₀.1) ρ ×ˢ ball (j s₀.1) ρ) ×ˢ ball s₀.2 (3 * σ)) ∧
          ∀ x ∈ ball (j s₀.1) ρ, ∀ y ∈ ball (j s₀.1) ρ,
            (∀ η ∈ ball s₀.2 (3 * σ), ∀ t ∈ Icc (0 : ℝ) 1,
              (y + t • (x - y), η) ∈ C.target) ∧
            (∀ η ∈ ball s₀.2 (3 * σ), HasFDerivAt (Ξ x y)
              (∫ t in (0 : ℝ)..1, C.mixedMomentumDerivative (y + t • (x - y), η)) η) ∧
            (∀ η ∈ ball s₀.2 (3 * σ),
              ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
                ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8) ∧
            InjOn (Ξ x y) (ball s₀.2 (3 * σ)) ∧
            (∀ η ∈ ball s₀.2 (3 * σ), ∀ θ ∈ ball s₀.2 (3 * σ),
              ‖η - θ‖ / 2 ≤ ‖A.symm (Ξ x y η - Ξ x y θ)‖) ∧
            IsCompact (Ξ x y '' closedBall s₀.2 σ) ∧
            cthickening β (Ξ x y '' closedBall s₀.2 σ) ⊆ W ∧
            cthickening β (closure W) ⊆ Ξ x y '' ball s₀.2 (2 * σ) ∧
            (Ξ x y) ⁻¹' cthickening β (closure W) ∩ ball s₀.2 (3 * σ) ⊆
              ball s₀.2 (2 * σ) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  let x₀ := j s₀.1
  obtain ⟨Φ₀, C₀, A, r, b, a₀, δ, K, V, hr, hb, ha₀, hδ, hK,
    hV, hVc, hbox₀, hCt₀, hp₀, hC₀, hA, hgap₀, hfamily⟩ :=
    exists_commonBufferedMixedGap H₀ hD hDH₀ hH₀ j ν horth hspan hR hRD henergy htrans
  let a := min a₀ (targetRadius r / 4)
  have ha : 0 < a := lt_min ha₀ (div_pos (hTargetRadius r hr) (by norm_num))
  have haa : 3 * a ≤ 3 * a₀ := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  have hacap : 3 * a < targetRadius r := by
    have hh : a ≤ targetRadius r / 4 := min_le_right _ _
    linarith [hTargetRadius r hr]
  have hbox : closedBall x₀ (3 * a) ×ˢ closedBall s₀.2 (3 * a) ⊆ V :=
    (Set.prod_mono (closedBall_subset_closedBall haa) (closedBall_subset_closedBall haa)).trans hbox₀
  have hC₀' : ContDiffOn ℝ ∞ C₀.coordinates C₀.target := hCt₀.symm ▸ hC₀
  let Ξ₀ : E → E → (ℝ × U) → E := fun x y η ↦
    averagedPhaseGradient (fun η x ↦ phase C₀.coordinates (x, η)) η x y
  obtain ⟨εn, hεn, hnorm⟩ := exists_normalization_buffer ℓ isOpen_ball isOpen_ball
    (show (x₀, s₀.2) ∈ ball x₀ (3 * a) ×ˢ ball s₀.2 (3 * a) from
      ⟨mem_ball_self (by positivity), mem_ball_self (by positivity)⟩) hℓ
  let σ := min (a / 2) (εn / 4)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσa : σ ≤ a / 2 := min_le_left _ _
  have hσε : σ ≤ εn / 4 := min_le_right _ _
  have hnormal : closedBall s₀.2 (3 * σ) ⊆ ball s₀.2 (3 * a) ∩
      canonicalCone ℓ (ball s₀.2 (3 * a)) := by
    intro η hη
    have hm : (x₀, η) ∈ closedBall (x₀, s₀.2) εn := by
      rw [mem_closedBall, Prod.dist_eq, max_le_iff, dist_self]
      exact ⟨hεn.le, (mem_closedBall.mp hη).trans (by linarith)⟩
    exact ⟨(hnorm hm).1.2, (hnorm hm).2.1, (hnorm hm).2.2.2⟩
  have hsmall : closedBall s₀.2 (3 * σ) ⊆ ball s₀.2 (3 * a) :=
    closedBall_subset_ball (by linarith)
  have hDR : ball s₀.2 (3 * σ) ⊆ ball s₀.2 (3 * a) :=
    ball_subset_closedBall.trans hsmall
  have hBB : ball x₀ (3 * a) ×ˢ ball s₀.2 (3 * a) ⊆ V :=
    (Set.prod_mono ball_subset_closedBall ball_subset_closedBall).trans hbox
  have hseg (x) (hx : x ∈ ball x₀ (3 * a)) (y) (hy : y ∈ ball x₀ (3 * a)) :
      ∀ η ∈ ball s₀.2 (3 * a), ∀ t ∈ Icc (0 : ℝ) 1,
        (y + t • (x - y), η) ∈ V :=
    fun η hη t ht ↦ hBB ⟨(convex_ball _ _).add_smul_sub_mem hy hx ht, hη⟩
  have hx₀ : x₀ ∈ ball x₀ (3 * a) := mem_ball_self (by positivity)
  have hd₀ (η) (hη : η ∈ ball s₀.2 (3 * σ)) :=
    C₀.hasFDerivAt_averagedPhaseGradient hp₀ hC₀' isOpen_ball
      (fun θ hθ t ht ↦ hCt₀.symm ▸ hseg x₀ hx₀ x₀ hx₀ θ hθ t ht) (hDR hη)
  have hg₀ (η) (hη : η ∈ ball s₀.2 (3 * σ)) :
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ₀ x₀ x₀) η) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 16 : ℝ) := by
    apply C₀.averagedDerivativeGap_for_conicBuffer hp₀ hC₀' isOpen_ball
      (fun θ hθ t ht ↦ hCt₀.symm ▸ hseg x₀ hx₀ x₀ hx₀ θ hθ t ht) A (hDR hη)
    intro t ht
    exact hgap₀ _ ⟨closedBall_subset_closedBall haa
      (ball_subset_closedBall ((convex_ball _ _).add_smul_sub_mem hx₀ hx₀ ht)),
      closedBall_subset_closedBall haa (ball_subset_closedBall (hDR hη))⟩
  have h₁D : ball s₀.2 (2 * σ) ⊆ ball s₀.2 (3 * σ) := ball_subset_ball (by linarith)
  obtain ⟨β, hβ, W, hW, hWc, hstable⟩ := common_buffered_inverse_domains
    (isCompact_closedBall s₀.2 σ) isOpen_ball
    (closedBall_subset_ball (by linarith : σ < 2 * σ)) h₁D (convex_ball _ _) A
    (fun η hη ↦ (hd₀ η hη).differentiableAt)
    (fun η hη ↦ (hg₀ η hη).trans (by norm_num))
  let F : (E × E) × (ℝ × U) → E := fun q ↦ Ξ₀ q.1.1 q.1.2 q.2
  have hcF : ContinuousOn F
      ((ball x₀ (3 * a) ×ˢ ball x₀ (3 * a)) ×ˢ ball s₀.2 (3 * a)) :=
    (C₀.contDiffOn_averagedPhaseGradient hp₀ hC₀' isOpen_ball (convex_ball _ _)
      isOpen_ball (hBB.trans (by rw [hCt₀]))).continuousOn
  have hnear : ∀ᶠ p : E × E in 𝓝 (x₀, x₀), ∀ η ∈ closedBall s₀.2 σ,
      ‖Ξ₀ p.1 p.2 η - Ξ₀ x₀ x₀ η‖ ≤ β / 2 := by
    apply (isCompact_closedBall s₀.2 σ).eventually_forall_of_forall_eventually
    intro η hη
    have hη' : η ∈ ball s₀.2 (3 * a) :=
      hsmall (closedBall_subset_closedBall (by linarith) hη)
    have hm : ((x₀, x₀), η) ∈
        ((ball x₀ (3 * a) ×ˢ ball x₀ (3 * a)) ×ˢ ball s₀.2 (3 * a)) :=
      ⟨⟨hx₀, hx₀⟩, hη'⟩
    have hc := hcF.continuousAt
      (((isOpen_ball.prod isOpen_ball).prod isOpen_ball).mem_nhds hm)
    have hproj : ContinuousAt (fun q : (E × E) × (ℝ × U) ↦ ((x₀, x₀), q.2))
        ((x₀, x₀), η) := continuousAt_const.prodMk continuousAt_snd
    have hn : ContinuousAt (fun q : (E × E) × (ℝ × U) ↦
        ‖F q - F ((x₀, x₀), q.2)‖) ((x₀, x₀), η) :=
      (hc.sub (hc.comp (g := F) (f := fun q : (E × E) × (ℝ × U) ↦
        ((x₀, x₀), q.2)) hproj)).norm
    exact (hn.eventually (gt_mem_nhds (show
      ‖F ((x₀, x₀), η) - F ((x₀, x₀), η)‖ < β / 2 by
        simpa using half_pos hβ))).mono (fun _ h ↦ h.le)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := min a ε / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρa : ρ ≤ a := by dsimp [ρ]; linarith [min_le_left a ε]
  have hρε : ρ ≤ ε := by dsimp [ρ]; linarith [min_le_right a ε]
  let N := ‖s₀.2‖ + σ + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let δ' := min δ (β / (2 * (K + 1) * N))
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hbox' : closedBall x₀ (3 * ρ) ×ˢ closedBall s₀.2 (3 * a) ⊆ V :=
    (Set.prod_mono (closedBall_subset_closedBall (by linarith))
      (closedBall_subset_closedBall (by linarith))).trans hbox
  refine ⟨Φ₀, C₀, A, r, b, ρ, σ, a, δ', K, β, V, W, hr, hb, hρ, hσ, ha, hδ', hK, hβ,
    hρa, hacap, hV, hVc, hW, hWc, hbox', hnormal, hCt₀, hp₀, hC₀, hA, ?_⟩
  intro H hDH hH hsmallH
  obtain ⟨Φ, C, ht, hp, hj, hx, hξ, hrange, hCt, hCs, hbuf, hadm, hC,
    hinner, houter, hpre, hclose, hgap⟩ :=
    hfamily H hDH hH (hsmallH.trans (min_le_left _ _))
  let Ξ : E → E → (ℝ × U) → E := fun x y η ↦
    averagedPhaseGradient (fun η x ↦ phase C.coordinates (x, η)) η x y
  have hC' : ContDiffOn ℝ ∞ C.coordinates C.target := hCt.symm ▸ hC
  have hρR : ball x₀ ρ ⊆ ball x₀ (3 * a) :=
    ball_subset_ball (hρa.trans (by linarith))
  refine ⟨Φ, C, ht, hp, hj, hx, hξ, hrange, hCt, hCs, hbuf, hadm, hC,
    hinner, houter, hpre, hclose, ?_, ?_, ?_⟩
  · intro z hz
    exact hgap z ⟨closedBall_subset_closedBall (by linarith) hz.1,
      closedBall_subset_closedBall haa hz.2⟩
  · exact C.contDiffOn_averagedPhaseGradient hξ hC' isOpen_ball (convex_ball _ _)
      isOpen_ball ((Set.prod_mono hρR hDR).trans (hBB.trans (by rw [hCt])))
  intro x hx y hy
  have hxR := hρR hx
  have hyR := hρR hy
  have hsegC : ∀ η ∈ ball s₀.2 (3 * a), ∀ t ∈ Icc (0 : ℝ) 1,
      (y + t • (x - y), η) ∈ C.target :=
    fun η hη t ht ↦ hCt.symm ▸ hseg x hxR y hyR η hη t ht
  have hsegC₀ : ∀ η ∈ ball s₀.2 (3 * a), ∀ t ∈ Icc (0 : ℝ) 1,
      (y + t • (x - y), η) ∈ C₀.target :=
    fun η hη t ht ↦ hCt₀.symm ▸ hseg x hxR y hyR η hη t ht
  have hd (η) (hη : η ∈ ball s₀.2 (3 * σ)) :=
    C.hasFDerivAt_averagedPhaseGradient hξ hC' isOpen_ball hsegC (hDR hη)
  have hg (η) (hη : η ∈ ball s₀.2 (3 * σ)) :
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
        ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ (1 / 8 : ℝ) := by
    apply C.averagedDerivativeGap_for_conicBuffer hξ hC' isOpen_ball hsegC A (hDR hη)
    intro t ht
    exact hgap _ ⟨closedBall_subset_closedBall haa
      (ball_subset_closedBall ((convex_ball _ _).add_smul_sub_mem hyR hxR ht)),
      closedBall_subset_closedBall haa (ball_subset_closedBall (hDR hη))⟩
  have hderiv (η) (hη : η ∈ ball s₀.2 (3 * σ)) :
      ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
        (fderiv ℝ (Ξ x y) η - fderiv ℝ (Ξ₀ x₀ x₀) η)‖ ≤ (1 / 4 : ℝ) := by
    have he : (A.symm : E →L[ℝ] (ℝ × U)).comp
        (fderiv ℝ (Ξ x y) η - fderiv ℝ (Ξ₀ x₀ x₀) η) =
        ((A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)) -
        ((A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ₀ x₀ x₀) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)) := by
      apply ContinuousLinearMap.ext
      intro v
      simp
    rw [he]
    calc
      _ ≤ ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)‖ +
          ‖(A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ₀ x₀ x₀) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)‖ :=
        norm_sub_le
          ((A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ x y) η) -
            ContinuousLinearMap.id ℝ (ℝ × U))
          ((A.symm : E →L[ℝ] (ℝ × U)).comp (fderiv ℝ (Ξ₀ x₀ x₀) η) -
            ContinuousLinearMap.id ℝ (ℝ × U))
      _ ≤ 1 / 4 := by linarith [hg η hη, hg₀ η hη]
  have hxy : (x, y) ∈ ball (x₀, x₀) ε := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hx).trans_le hρε, (mem_ball.mp hy).trans_le hρε⟩
  have hvalue (η) (hη : η ∈ closedBall s₀.2 σ) :
      ‖Ξ x y η - Ξ₀ x₀ x₀ η‖ ≤ β := by
    have hη' : η ∈ ball s₀.2 (3 * a) :=
      hsmall (closedBall_subset_closedBall (by linarith) hη)
    have hval := C.norm_averagedPhaseGradient_sub_le C₀ hξ hC' hp₀ hC₀'
      (hsegC η hη') (hsegC₀ η hη')
      (fun t ht ↦ hclose _ (hseg x hxR y hyR η hη' t ht))
    have hnorm : ‖η‖ ≤ N := by
      have hn' := norm_add_le (η - s₀.2) s₀.2
      rw [sub_add_cancel] at hn'
      have hd := mem_closedBall.mp hη
      rw [dist_eq_norm] at hd
      dsimp [N]
      linarith
    have hcn := CompositionBounds.cNorm_nonneg (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)
    have hbudget : (K * cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w)) * N ≤ β / 2 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2 * (K + 1) * N)).mp
        (hsmallH.trans (min_le_right _ _))
      have hn : 0 ≤ cNorm (closedBall z₀ R) 3 (fun w ↦ H.h w - H₀.h w) * N :=
        mul_nonneg hcn hN.le
      nlinarith
    have hval' : ‖Ξ x y η - Ξ₀ x y η‖ ≤ β / 2 :=
      hval.trans ((mul_le_mul_of_nonneg_left hnorm (mul_nonneg hK.le hcn)).trans hbudget)
    exact (norm_sub_le_norm_sub_add_norm_sub (Ξ x y η) (Ξ₀ x y η) (Ξ₀ x₀ x₀ η)).trans
      (by linarith [(hεsub hxy) η hη])
  obtain ⟨hinj, hlower, hcompact, hinner', houter'⟩ :=
    hstable (Ξ x y) (fun η hη ↦ (hd η hη).differentiableAt) hderiv hvalue
  refine ⟨fun η hη ↦ hsegC η (hDR hη), hd, hg, hinj, hlower, hcompact,
    hinner', houter', ?_⟩
  intro η hη
  obtain ⟨θ, hθ, heq⟩ := houter' hη.1
  exact (hinj (h₁D hθ) hη.2 heq) ▸ hθ


/-- Actual common positive conic Hamilton phases for the scalar-symbol family
of `app:lem:common-hamilton-phase`. The normalization, convex boxes, overlap
buffer and reference equivalence are chosen before the symbol. The mixed and
averaged gaps are instantiated from `exists_commonBufferedMixedGap` and the
normalization-compatible refinement of the family averaged-gradient construction;
no phase, flow-scaling, mixed gap or conic injectivity is assumed. The original
source and inverse-domain buffers are retained with their membership conditions.
Root uniqueness and Hamilton ODE uniqueness establish scaling for the actual
chosen family. The entire conic preimage of the common inverse buffer lies in
the middle canonical ball. The normalized physical/canonical box is chosen
inside `targetRadius r`, where `r` is the constructed source radius. This lets
`exists_commonTameContinuousConicHamiltonPhases` impose its inverse-uniqueness
buffer before the averaged inverse domain is chosen. -/
theorem exists_commonConicHamiltonPhases_with_targetRadius
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0)
    (hξ : (transverseSectionState j ν (s₀, τ₀)).2 ≠ 0)
    (targetRadius : ℝ → ℝ) (hTargetRadius : ∀ r > 0, 0 < targetRadius r) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (ℓ : (ℝ × U) →L[ℝ] ℝ) (A : (ℝ × U) ≃L[ℝ] E)
      (r b ρ σ a δ ε β : ℝ) (V : Set (E × (ℝ × U))) (W : Set E),
      let B := ball (j s₀.1) ρ
      let P := ball s₀.2 (3 * a)
      let Q := canonicalCone ℓ P
      let Ω := CharacteristicRoot.conicDomain ℓ (B ×ˢ P)
      0 < r ∧ 0 < b ∧ 0 < ρ ∧ 0 < σ ∧ 0 < a ∧ 0 < δ ∧ 0 < ε ∧ 0 < β ∧
      ℓ s₀.2 = 1 ∧ IsOpen V ∧ IsCompact (closure V) ∧
      IsOpen W ∧ IsCompact (closure W) ∧ Convex ℝ Ω ∧ Convex ℝ Q ∧
      closedBall (j s₀.1, s₀.2) ε ⊆ (B ×ˢ P) ∩ Ω ∧
      closedBall s₀.2 (3 * σ) ⊆ P ∩ Q ∧
      B ×ˢ P ⊆ V ∧ B ×ˢ P ⊆ ball (j s₀.1, s₀.2) (targetRadius r) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        H.ConicHomogeneous → cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          let Ξ := fun x y η ↦ averagedPhaseGradient
            (fun η x ↦ phase C.coordinates (x, η)) η x y
          let Ξc := fun x y η ↦ averagedPhaseGradient
            (fun η x ↦ C.conicPhase ℓ (x, η)) η x y
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
            (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) ∈ H.domain ∧
            H.h (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) = z.2.1 ∧
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
            (Ξc x y) ⁻¹' cthickening β (closure W) ∩ Q ⊆ ball s₀.2 (2 * σ) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  have hbase : z₀ ∈ H₀.domain := hDH₀ (hRD (mem_closedBall_self hR.le))
  obtain ⟨ℓ, hℓ⟩ := exists_canonicalNormalization
    (sectionCanonical_ne_zero H₀ j ν hbase henergy htrans hξ)
  obtain ⟨Φ₀, C₀, A, r, b, ρ, σ, a, δ, K, β, V, W,
    hr, hb, hρ, hσ, ha, hδ, hK, hβ, hρa, hacap, hV, hVc, hW, hWc, hbox, hnormal,
    hCt₀, hp₀, hC₀, hA, hfamily⟩ := exists_commonBufferedAveragedGradient_normalization
      H₀ hD hDH₀ hH₀ j ν horth hspan hR hRD henergy ℓ hℓ htrans targetRadius hTargetRadius
  let B := ball (j s₀.1) ρ
  let P := ball s₀.2 (3 * a)
  have hBP : B ×ˢ P ⊆ V := by
    exact (Set.prod_mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      ball_subset_closedBall).trans hbox
  obtain ⟨ε, hε, hbuf⟩ := exists_normalization_buffer ℓ isOpen_ball isOpen_ball
    (show (j s₀.1, s₀.2) ∈ B ×ˢ P from
      ⟨mem_ball_self hρ, mem_ball_self (by positivity)⟩) hℓ
  refine ⟨ℓ, A, r, b, ρ, σ, a, δ, ε, β, V, W,
    hr, hb, hρ, hσ, ha, hδ, hε, hβ, hℓ, hV, hVc, hW, hWc,
    convex_conicDomain_prod ℓ (convex_ball _ _) (convex_ball _ _),
    convex_canonicalCone ℓ (convex_ball _ _), hbuf, hnormal, hBP, ?_, ?_⟩
  · intro z hz
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hz.1).trans (by linarith), (mem_ball.mp hz.2).trans hacap⟩
  intro H hDH hH hconic hsmall
  obtain ⟨Φ, C, ht, hparams, hj, hx, hp, hrange, hCt, hCs, hsource,
    hadm, hC, hinner, houter, hpre, hclose, hgap, hΞsmooth, hΞ⟩ :=
      hfamily H hDH hH hsmall
  have hC' : ContDiffOn ℝ ∞ C.coordinates C.target := hCt.symm ▸ hC
  have hsub : B ×ˢ P ⊆ C.target := hBP.trans (by rw [hCt])
  have hcone : CharacteristicRoot.conicDomain ℓ (B ×ˢ P) ⊆
      CharacteristicRoot.conicDomain ℓ C.target := fun _ hz ↦ ⟨hz.1, hsub hz.2⟩
  have hν : ν ≠ 0 := by
    intro he
    apply htrans
    rw [he, inner_zero_right]
  have hstate : ∀ t ∈ Φ.time, ∀ s ∈ Φ.parameters,
      (Φ.position (t, s), Φ.momentum (t, s)) ∈ D :=
    fun t ht s hs ↦ hRD (hrange (t, s) ⟨ht, hs⟩)
  have hPsub : ball s₀ (3 * r) ⊆ Φ.parameters := by
    intro s hs
    apply (hadm (subset_closure (show (0, s) ∈ ball ((0 : ℝ), s₀) (3 * r) from ?_))).2
    simpa only [mem_ball, Prod.dist_eq, dist_self, max_lt_iff] using
      And.intro (by positivity : (0 : ℝ) < 3 * r) (mem_ball.mp hs)
  have hsourceP : ∀ q ∈ C.source, q.2 ∈ ball s₀ (3 * r) := by
    intro q hq
    have hb := (hCs ▸ hq).1
    exact (mem_ball.mp hb |> (show dist q.2 s₀ ≤ dist q (0, s₀) from
      by rw [Prod.dist_eq]; exact le_max_right _ _).trans_lt)
  have hscale : ∀ s ∈ ball s₀ (3 * r), ∀ t ∈ Φ.time, ∀ a : ℝ, 0 < a →
      scaleSectionData a s ∈ ball s₀ (3 * r) →
      (Φ.position (t, scaleSectionData a s), Φ.momentum (t, scaleSectionData a s)) =
        (Φ.position (t, s), a • Φ.momentum (t, s)) := by
    intro s hs t ht a ha has
    have hi := Φ.initial_momentum_smul_of_section hD hH (hstate 0 Φ.zero_mem_time)
      j ν hν hj horth hspan isOpen_ball (convex_ball _ _) hPsub hs ha has
    exact Φ.state_smul_on_symbolPatch hconic hD hstate
      (H.contDiffOn_vectorField_of_subset hD hDH (hH.of_le (by simp)))
      ha (hPsub hs) (hPsub has) hi ht
  have hchart : ∀ z ∈ C.target, ∀ a : ℝ, 0 < a →
      ((C.coordinates z).1, ((C.coordinates z).2, a • z.2)) ∈ C.source →
      C.coordinates (z.1, a • z.2) = C.coordinates z :=
    fun z hz a ha hs ↦ C.coordinates_smul_of_sectionData hD hDH hH hconic hstate
      j ν hν hj horth hspan isOpen_ball (convex_ball _ _) hPsub hsourceP hz ha hs
  refine ⟨Φ, C, hj, hx, hp, hrange, hCt, hCs, hsource, hadm, hC,
    hinner, houter, hpre, hscale, hchart, (C.contDiffOn_conicPhase ℓ hC').mono hcone,
    fun z a ha ↦ C.conicPhase_smul ℓ z ha, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hm := hbuf hz
    exact C.conicPhase_eq_of_mem_convex ℓ isOpen_ball (convex_ball _ _)
      (fun η hη ↦ hsub ⟨hm.1.1, hη⟩) hm.1.2 hm.2.1 hm.2.2.2
  · intro z hz
    obtain ⟨hmem, he⟩ := C.conicPhase_eikonal ℓ hconic (hcone hz)
    refine ⟨hmem, he, C.hasFDerivAt_conicPhase_canonical ℓ hC'
      isOpen_ball (convex_ball _ _) hsub hz, ?_⟩
    rw [C.fderiv_gradient_conicPhase_eq_normalized ℓ hp hC' isOpen_ball
      isOpen_ball (convex_ball _ _) hsub hz]
    exact hgap _ ⟨(ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith))) hz.2.1, ball_subset_closedBall hz.2.2⟩
  · intro u η hη hs
    simpa only [hj, LinearIsometry.coe_toContinuousLinearMap] using C.conicPhase_initial_value ℓ hη hs
  · intro x hx y hy
    obtain ⟨hseg, hd, hg, hinj, hlower, hcompact, hinner', houter', hpre'⟩ := hΞ x hx y hy
    have hgP : ∀ η ∈ P, ‖(A.symm : E →L[ℝ] (ℝ × U)).comp
        (fderiv ℝ (fun η ↦ averagedPhaseGradient
          (fun η x ↦ phase C.coordinates (x, η)) η x y) η) -
          ContinuousLinearMap.id ℝ (ℝ × U)‖ ≤ 1 / 8 := by
      intro η hη
      apply C.averagedDerivativeGap_for_conicBuffer hp hC' isOpen_ball
        (fun θ hθ t ht ↦ hsub ⟨(convex_ball _ _).add_smul_sub_mem hy hx ht, hθ⟩) A hη
      intro t ht
      exact hgap _ ⟨(ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith)))
          ((convex_ball _ _).add_smul_sub_mem hy hx ht), ball_subset_closedBall hη⟩
    have hinjP := injOn_of_normalized_derivative_gap (convex_ball s₀.2 (3 * a)) A
      (fun η hη ↦ (C.hasFDerivAt_averagedPhaseGradient hp hC' isOpen_ball
        (fun θ hθ t ht ↦ hsub ⟨(convex_ball _ _).add_smul_sub_mem hy hx ht, hθ⟩)
          hη).differentiableAt)
      (fun η hη ↦ (hgP η hη).trans (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2))
    have hpreP : (fun η ↦ averagedPhaseGradient
        (fun θ x ↦ phase C.coordinates (x, θ)) η x y) ⁻¹'
        cthickening β (closure W) ∩ P ⊆ ball s₀.2 (2 * σ) := by
      intro η hη
      obtain ⟨θ, hθ, he⟩ := houter' hη.1
      have hθP := (hnormal ((ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith))) hθ)).1
      exact (hinjP hθP hη.2 he) ▸ hθ
    obtain ⟨hinjc, hlowerc⟩ := C.conicAveragedGradient_injective ℓ hp hC'
      isOpen_ball (convex_ball _ _) isOpen_ball (convex_ball _ _) hsub hx hy A hgP
    have heq (η) (hη : η ∈ closedBall s₀.2 (3 * σ)) :
        averagedPhaseGradient (fun θ x ↦ C.conicPhase ℓ (x, θ)) η x y =
          averagedPhaseGradient (fun θ x ↦ phase C.coordinates (x, θ)) η x y :=
      C.conicAveragedGradient_eq_on_overlap ℓ isOpen_ball (convex_ball _ _)
        isOpen_ball (convex_ball _ _) hsub hx hy (hnormal hη)
    have hmid : ball s₀.2 (2 * σ) ⊆ closedBall s₀.2 (3 * σ) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
    refine ⟨fun η hη ↦ C.conicAveragedGradient_derivative_gap ℓ hp hC'
      isOpen_ball (convex_ball _ _) isOpen_ball (convex_ball _ _) hsub hx hy A hgP hη,
      hinjc, hlowerc, hinner', houter', hpreP, ?_, ?_, ?_⟩
    · have he : (fun η ↦ averagedPhaseGradient
          (fun θ x ↦ C.conicPhase ℓ (x, θ)) η x y) '' closedBall s₀.2 σ =
          (fun η ↦ averagedPhaseGradient
            (fun θ x ↦ phase C.coordinates (x, θ)) η x y) '' closedBall s₀.2 σ := by
        apply Set.image_congr
        intro η hη
        exact heq η (closedBall_subset_closedBall (by linarith) hη)
      rw [he]
      exact hinner'
    · intro v hv
      obtain ⟨η, hη, rfl⟩ := houter' hv
      exact ⟨η, hη, heq η (hmid hη)⟩
    · intro η hη
      obtain ⟨θ, hθ, heθ⟩ := houter' hη.1
      have he : θ = η := hinjc (hnormal (hmid hθ)).2 hη.2
        ((heq θ (hmid hθ)).trans heθ)
      exact he ▸ hθ

/-- Common conic phases and inverse buffers for `app:lem:common-hamilton-phase`.
This is the unrestricted specialization of the construction with a prescribed
normalized target radius. -/
theorem exists_commonConicHamiltonPhases
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
      (r b ρ σ a δ ε β : ℝ) (V : Set (E × (ℝ × U))) (W : Set E),
      let B := ball (j s₀.1) ρ
      let P := ball s₀.2 (3 * a)
      let Q := canonicalCone ℓ P
      let Ω := CharacteristicRoot.conicDomain ℓ (B ×ˢ P)
      0 < r ∧ 0 < b ∧ 0 < ρ ∧ 0 < σ ∧ 0 < a ∧ 0 < δ ∧ 0 < ε ∧ 0 < β ∧
      ℓ s₀.2 = 1 ∧ IsOpen V ∧ IsCompact (closure V) ∧
      IsOpen W ∧ IsCompact (closure W) ∧ Convex ℝ Ω ∧ Convex ℝ Q ∧
      closedBall (j s₀.1, s₀.2) ε ⊆ (B ×ˢ P) ∩ Ω ∧
      closedBall s₀.2 (3 * σ) ⊆ P ∩ Q ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        H.ConicHomogeneous → cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (Φ : HamiltonFlow H U) (C : ProjectionChart Φ),
          let Ξ := fun x y η ↦ averagedPhaseGradient
            (fun η x ↦ phase C.coordinates (x, η)) η x y
          let Ξc := fun x y η ↦ averagedPhaseGradient
            (fun η x ↦ C.conicPhase ℓ (x, η)) η x y
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
            (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) ∈ H.domain ∧
            H.h (z.1, gradient (fun x ↦ C.conicPhase ℓ (x, z.2)) z.1) = z.2.1 ∧
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
            (Ξc x y) ⁻¹' cthickening β (closure W) ∩ Q ⊆ ball s₀.2 (2 * σ) := by
  obtain ⟨ℓ, A, r, b, ρ, σ, a, δ, ε, β, V, W,
      hr, hb, hρ, hσ, ha, hδ, hε, hβ, hℓ, hV, hVc, hW, hWc,
      hΩ, hQ, hbuf, hnormal, _hBP, _hcap, hfamily⟩ :=
    exists_commonConicHamiltonPhases_with_targetRadius H₀ hD hDH₀ hH₀ j ν horth hspan
      hR hRD henergy htrans hξ (fun _ ↦ 1) (by intros; norm_num)
  exact ⟨ℓ, A, r, b, ρ, σ, a, δ, ε, β, V, W,
    hr, hb, hρ, hσ, ha, hδ, hε, hβ, hℓ, hV, hVc, hW, hWc,
    hΩ, hQ, hbuf, hnormal, hfamily⟩

end JanetCartan.HamiltonPhase
