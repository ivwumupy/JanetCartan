module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionRelation.Suspension
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PencilRoot
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol

/-!
# The direct root field of the retained normalized pencil

The differential step of `app:ch_regular:thm:no-return`, consumed by direct
complete-chain propagation in `app:ch_regular:lem:finite-chain`. The root equation
and transverse gap are the literal outputs of `exists_pencilRoot_domain`.
The coordinate pairing is an explicit geometric input: the sector owner must
prove it for its retained adapted coordinates. An arbitrary linear equivalence
applied identically to positions and covectors does not imply this identity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy
open RegularSector.Characteristic ActualCarriers HamiltonPhase

variable {n d : ℕ}

/-- Zero-energy root state in the original physical coordinates of the pencil
(`app:ch_regular:lem:finite-chain`). -/
def physicalPencilRootState (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (w : RootState (Euclidean d)) :
    Euclidean n × Euclidean n :=
  (e.symm (w.1, w.2.1), e.symm (h w, w.2.2))

/-- Pushforward of the actual suspended root velocity, with the original
position/covector convention (`app:ch_regular:thm:no-return`). -/
def physicalPencilRootVelocity (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (w : RootState (Euclidean d)) :
    Euclidean n × Euclidean n :=
  (e.symm (1, -rootMomentumGradient h w),
    e.symm (fderiv ℝ h w (1, (0, 0)), rootPositionGradient h w))

/-- The signed transverse speed of the SAME normalized determinant. Its sign
is not fixed by the root constructor (`app:ch_regular:thm:no-return`). -/
def pencilRootSpeed (Q : Euclidean n → Fin n → MetricTensor n)
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (w : RootState (Euclidean d)) : ℝ :=
  determinantNormalization (e.symm (h w, w.2.2)) *
    fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
      (e.symm (h w, w.2.2)) (e.symm (1, 0))

/-- Differentiate the common-root identity before taking a Hamilton field.
This is the scalar implicit-function calculation used by the physical field
comparison (`app:ch_regular:thm:no-return`). -/
theorem pencilRoot_differential
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Q : Euclidean n → Fin n → MetricTensor n}
    {h : RootState (Euclidean d) → ℝ} {w : RootState (Euclidean d)}
    (hh : DifferentiableAt ℝ h w)
    (hQ : DifferentiableAt ℝ (normalizedSymbol Q) (physicalPencilRootState e h w))
    (hroot : ∀ᶠ v in 𝓝 w,
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (h v, v.2.2)) = 0)
    (hne : e.symm (h w, w.2.2) ≠ 0)
    (v : RootState (Euclidean d)) (σ : ℝ) :
    fderiv ℝ (normalizedSymbol Q) (physicalPencilRootState e h w)
      (e.symm (v.1, v.2.1), e.symm (σ, v.2.2)) =
        pencilRootSpeed Q e h w * (σ - fderiv ℝ h w v) := by
  have hp := hroot.self_of_nhds
  have hzero : (fun v ↦ normalizedSymbol Q (physicalPencilRootState e h v))
      =ᶠ[𝓝 w] fun _ ↦ 0 := by
    filter_upwards [hroot] with v hv
    simp [physicalPencilRootState, normalizedSymbol, hv]
  have hg := (e.symm.hasFDerivAt.comp w
      ((hasFDerivAt_fst (p := w)).prodMk (hasFDerivAt_snd (p := w)).fst)).prodMk
    (e.symm.hasFDerivAt.comp w (hh.hasFDerivAt.prodMk (hasFDerivAt_snd (p := w)).snd))
  have hz := ((hQ.hasFDerivAt.comp w hg).congr_of_eventuallyEq hzero.symm).unique
    (hasFDerivAt_const (0 : ℝ) w)
  have hv := congrArg (fun L : RootState (Euclidean d) →L[ℝ] ℝ ↦ L v) hz
  change fderiv ℝ (normalizedSymbol Q) (physicalPencilRootState e h w)
    (e.symm (v.1, v.2.1), e.symm (fderiv ℝ h w v, v.2.2)) = 0 at hv
  have ht := (hQ.hasFDerivAt.comp_hasDerivAt (h w)
    ((hasDerivAt_const (h w) (e.symm (w.1, w.2.1))).prodMk
      (e.symm.hasFDerivAt.comp_hasDerivAt (h w)
        ((hasDerivAt_id (h w)).prodMk (hasDerivAt_const (h w) w.2.2)))))
  have hc := ht.unique (hasDerivAt_adaptedNormalizedPencil Q e
    (w.1, w.2.1) w.2.2 (h w) hne hp)
  change fderiv ℝ (normalizedSymbol Q) (physicalPencilRootState e h w)
    (0, e.symm (1, 0)) = pencilRootSpeed Q e h w at hc
  have hsplit : (e.symm (v.1, v.2.1), e.symm (σ, v.2.2)) =
      (e.symm (v.1, v.2.1), e.symm (fderiv ℝ h w v, v.2.2)) +
        (σ - fderiv ℝ h w v) • (0, e.symm (1, 0)) := by
    ext <;> simp [← map_smul, ← map_add]
  rw [hsplit, map_add, map_smul, hv, zero_add, hc, smul_eq_mul, mul_comm]

/-- The physical Hamilton field equals the signed transverse speed times the
direct zero-energy root field. Pairing is the precise remaining coordinate
obligation of the regular-sector producer; root invariance is not a premise
(`app:ch_regular:thm:no-return`). -/
theorem normalizedPencil_field_eq_root_velocity
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (hpair : ∀ u v : ℝ × Euclidean d,
      ⟪e.symm u, e.symm v⟫_ℝ = u.1 * v.1 + ⟪u.2, v.2⟫_ℝ)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {h : RootState (Euclidean d) → ℝ} {w : RootState (Euclidean d)}
    (hh : DifferentiableAt ℝ h w)
    (hx : e.symm (w.1, w.2.1) ∈ Ω) (hne : e.symm (h w, w.2.2) ≠ 0)
    (hroot : ∀ᶠ v in 𝓝 w,
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (h v, v.2.2)) = 0) :
    (normalizedHomogeneousSymbol hΩ Q hQ).vectorField (physicalPencilRootState e h w) =
      pencilRootSpeed Q e h w • physicalPencilRootVelocity e h w := by
  let H := normalizedHomogeneousSymbol hΩ Q hQ
  have hm : physicalPencilRootState e h w ∈ H.domain := ⟨hx, hne⟩
  have hd := H.hasFDerivAt_h _ hm
  have he := pencilRoot_differential e hh hd.differentiableAt hroot hne
  change HasFDerivAt (normalizedSymbol Q) _ _ at hd
  rw [hd.fderiv] at he
  apply Prod.ext
  · apply ext_inner_right ℝ
    intro q
    obtain ⟨u, rfl⟩ := e.symm.surjective q
    have hv := he (0, (0, u.2)) u.1
    simp [hamiltonDifferential_apply, ← Prod.zero_eq_mk] at hv
    simpa [HomogeneousSymbol.vectorField, physicalPencilRootVelocity,
      inner_smul_left, hpair, inner_rootMomentumGradient, H, sub_eq_add_neg] using hv
  · apply ext_inner_right ℝ
    intro q
    obtain ⟨u, rfl⟩ := e.symm.surjective q
    have hv := he (u.1, (u.2, 0)) 0
    rw [root_fderiv_split] at hv
    simp [hamiltonDifferential_apply, ← Prod.zero_eq_mk] at hv
    simp [HomogeneousSymbol.vectorField, physicalPencilRootVelocity,
      inner_smul_left, hpair]
    simp only [Prod.zero_eq_mk] at hv
    dsimp [H] at hv
    nlinarith [hv]

/-- Nonzero transverse determinant derivative gives nonzero speed. Either
orientation is allowed (`app:ch_regular:thm:no-return`). -/
theorem pencilRootSpeed_ne_zero
    (Q : Euclidean n → Fin n → MetricTensor n)
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (h : RootState (Euclidean d) → ℝ) (w : RootState (Euclidean d))
    (hne : e.symm (h w, w.2.2) ≠ 0)
    (hgap : fderiv ℝ (determinant (Q (e.symm (w.1, w.2.1))))
      (e.symm (h w, w.2.2)) (e.symm (1, 0)) ≠ 0) :
    pencilRootSpeed Q e h w ≠ 0 :=
  mul_ne_zero (determinantNormalization_pos hne).ne' hgap

/-- The coordinate lift of an actual root trajectory has the displayed
physical velocity. The changing temporal covector is differentiated, rather
than held fixed (`app:ch_regular:lem:finite-chain`). -/
theorem hasDerivAt_physicalPencilRootState
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {h : RootState (Euclidean d) → ℝ} {Z : ℝ → RootState (Euclidean d)}
    {t : ℝ} (hh : DifferentiableAt ℝ h (Z t))
    (hZ : HasDerivAt Z (rootHamiltonField h (Z t)) t) :
    HasDerivAt (fun u ↦ physicalPencilRootState e h (Z u))
      (physicalPencilRootVelocity e h (Z t)) t := by
  have ht := (ContinuousLinearMap.fst ℝ ℝ (Euclidean d × Euclidean d)).hasFDerivAt.comp_hasDerivAt t hZ
  have hy := ((ContinuousLinearMap.fst ℝ (Euclidean d) (Euclidean d)).comp
    (ContinuousLinearMap.snd ℝ ℝ (Euclidean d × Euclidean d))).hasFDerivAt.comp_hasDerivAt t hZ
  have hp := ((ContinuousLinearMap.snd ℝ (Euclidean d) (Euclidean d)).comp
    (ContinuousLinearMap.snd ℝ ℝ (Euclidean d × Euclidean d))).hasFDerivAt.comp_hasDerivAt t hZ
  have hd := (e.symm.hasFDerivAt.comp_hasDerivAt t (ht.prodMk hy)).prodMk
    (e.symm.hasFDerivAt.comp_hasDerivAt t ((hh.hasFDerivAt.comp_hasDerivAt t hZ).prodMk hp))
  change HasDerivAt (fun u ↦ physicalPencilRootState e h (Z u))
    (e.symm (1, -rootMomentumGradient h (Z t)),
      e.symm (fderiv ℝ h (Z t) (rootHamiltonField h (Z t)), rootPositionGradient h (Z t))) t at hd
  simpa only [root_fderiv_along_hamiltonField, physicalPencilRootVelocity] using hd

/-- The scalar speed is the time component of the physical pencil velocity.
This gives its continuity on each entire root segment from the SAME smooth
symbol (`app:ch_regular:thm:no-return`). -/
theorem pencilRootSpeed_eq_time_component
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (hpair : ∀ u v : ℝ × Euclidean d,
      ⟪e.symm u, e.symm v⟫_ℝ = u.1 * v.1 + ⟪u.2, v.2⟫_ℝ)
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    {Q : Euclidean n → Fin n → MetricTensor n} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {h : RootState (Euclidean d) → ℝ} {w : RootState (Euclidean d)}
    (hh : DifferentiableAt ℝ h w)
    (hx : e.symm (w.1, w.2.1) ∈ Ω) (hne : e.symm (h w, w.2.2) ≠ 0)
    (hroot : ∀ᶠ v in 𝓝 w,
      determinant (Q (e.symm (v.1, v.2.1))) (e.symm (h v, v.2.2)) = 0) :
    pencilRootSpeed Q e h w =
      (e ((normalizedHomogeneousSymbol hΩ Q hQ).hp (physicalPencilRootState e h w))).1 := by
  have he := congrArg (fun v : Euclidean n × Euclidean n ↦ (e v.1).1)
    (normalizedPencil_field_eq_root_velocity e hpair hΩ hQ hh hx hne hroot)
  simpa [HomogeneousSymbol.vectorField, physicalPencilRootVelocity] using he.symm

end JanetCartan.ArbitraryAccuracy
