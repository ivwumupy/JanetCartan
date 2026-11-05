module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.CompactRelations.Graph

/-!
# Annular bounds from primitive root-buffer estimates

For `app:ch_regular:lem:finite-chain`, the lower bound comes from the transverse
covector, and the upper bound from that covector and the original root value.
`coordinateSplit_inverse_pairing` supplies the physical Euclidean norm identity;
the product norm of the time/spatial split is not substituted for it.

The finite-family constants precede every varying root, flow, buffer and mask.
The current-family producer must establish the displayed primitive estimates
on the selected initial and whole-segment buffers. In `UniformGeometry/RootFlow`,
these follow from the fixed transverse ball, the lower section bound `1/2`, and
`|h w| ≤ ℓ w.2.2 * G`, for the SAME root and flow.
-/

@[expose] public noncomputable section

open Set
open scoped InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic

variable {d : ℕ}

/-- The physical covector norm is bounded below by its transverse norm and
above by the sum of the root value and transverse norm. This uses the actual
coordinate permutation's pairing identity (`app:ch_regular:lem:finite-chain`). -/
theorem coordinateSplit_covector_norm_bounds (i : Fin (d + 1))
    (τ : ℝ) (η : Euclidean d) :
    ‖η‖ ≤ ‖(coordinateSplit i).symm (τ, η)‖ ∧
      ‖(coordinateSplit i).symm (τ, η)‖ ≤ |τ| + ‖η‖ := by
  have hid := coordinateSplit_inverse_pairing i (τ, η) (τ, η)
  simp only [real_inner_self_eq_norm_sq] at hid
  constructor
  · nlinarith [norm_nonneg ((coordinateSplit i).symm (τ, η)), norm_nonneg η,
      sq_nonneg τ]
  · nlinarith [norm_nonneg ((coordinateSplit i).symm (τ, η)), norm_nonneg η,
      abs_nonneg τ, sq_abs τ, mul_nonneg (abs_nonneg τ) (norm_nonneg η)]

/-- Primitive root-buffer estimates imply physical covector bounds at each
zero-energy lifted point (`app:ch_regular:lem:finite-chain`). -/
theorem physicalPencilRootState_covector_bounds
    (i : Fin (d + 1)) (h : RootState (Euclidean d) → ℝ)
    (v : RootState (Euclidean d)) {c M B : ℝ}
    (hlower : c ≤ ‖v.2.2‖) (hupper : ‖v.2.2‖ ≤ M) (hroot : |h v| ≤ B) :
    c ≤ ‖(physicalPencilRootState (coordinateSplit i) h v).2‖ ∧
      ‖(physicalPencilRootState (coordinateSplit i) h v).2‖ ≤ B + M := by
  obtain ⟨hl, hu⟩ := coordinateSplit_covector_norm_bounds i (h v) v.2.2
  exact ⟨hlower.trans hl, hu.trans (add_le_add hroot hupper)⟩

/-- Both endpoints, in both orientations, obey the bounds on the initial and
whole-segment buffers. No annular output-image hypothesis is used
(`app:ch_regular:lem:finite-chain`). -/
theorem maskedZeroEnergyRelation_covector_bounds
    (i : Fin (d + 1))
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {U K : Set (RootState (Euclidean d))} {W : Set (Euclidean (d + 1))}
    {χsource χout : Euclidean (d + 1) → ℂ} {Δ c M B : ℝ}
    (hb : ∀ v ∈ U ∪ K, c ≤ ‖v.2.2‖ ∧ ‖v.2.2‖ ≤ M ∧ |h v| ≤ B)
    {backward : Bool} {a b : Euclidean (d + 1) × Euclidean (d + 1)}
    (hab : maskedZeroEnergyRelation (coordinateSplit i) h Φ U K W χsource χout Δ backward a b) :
    (c ≤ ‖(adaptedPhysicalPhaseState (coordinateSplit i) a).2‖ ∧
      ‖(adaptedPhysicalPhaseState (coordinateSplit i) a).2‖ ≤ B + M) ∧
    (c ≤ ‖(adaptedPhysicalPhaseState (coordinateSplit i) b).2‖ ∧
      ‖(adaptedPhysicalPhaseState (coordinateSplit i) b).2‖ ≤ B + M) := by
  obtain ⟨vr, hv, hs, ht⟩ := (maskedZeroEnergyRelation_iff_accepted _ _ _ _ _ _ _ _ _ _ _ _).1 hab
  have hsbound := hb vr.1 (Or.inl hv.1.1)
  have htbound := hb (Φ vr) (Or.inr (by
    simpa only [one_mul] using (hv.2.1 1 (by simp)).1))
  have hsource := physicalPencilRootState_covector_bounds i h vr.1
    hsbound.1 hsbound.2.1 hsbound.2.2
  have htarget := physicalPencilRootState_covector_bounds i h (Φ vr)
    htbound.1 htbound.2.1 htbound.2.2
  cases backward
  · change a = _ at hs
    change b = _ at ht
    simpa only [hs, ht, adaptedPhysicalPhaseState_rootSuspensionState] using ⟨hsource, htarget⟩
  · change b = _ at hs
    change a = _ at ht
    simpa only [hs, ht, adaptedPhysicalPhaseState_rootSuspensionState] using ⟨htarget, hsource⟩

/-- Common positive lower and finite positive upper bounds are chosen from
the finite list of primitive constants BEFORE any varying roots or flows.
The displayed buffer estimates are the entire remaining analytic input;
the conclusion covers both endpoints and orientations of the actual relation
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_physicalDirectRelation_covector_bounds
    {J : Type*} [Finite J] (c M B : J → ℝ) (hc : ∀ j, 0 < c j) :
    ∃ c₀ > (0 : ℝ), ∃ C₀ > (0 : ℝ),
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ),
        (∀ j v, v ∈ U j ∪ K j →
          c j ≤ ‖v.2.2‖ ∧ ‖v.2.2‖ ≤ M j ∧ |h j v| ≤ B j) →
        ∀ p q, physicalDirectRelation i h Φ U K W χsource χout Δ p q →
          (c₀ ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ C₀) ∧ (c₀ ≤ ‖q.2‖ ∧ ‖q.2‖ ≤ C₀) := by
  classical
  let := Fintype.ofFinite J
  let lower : Option J → ℝ := fun j ↦ j.elim 1 c
  let upper : Option J → ℝ := fun j ↦ j.elim 1 (fun j ↦ B j + M j)
  let c₀ := Finset.univ.inf' Finset.univ_nonempty lower
  let C₀ := Finset.univ.sup' Finset.univ_nonempty upper
  have hc₀ : 0 < c₀ := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro j _
    cases j with
    | none => exact zero_lt_one
    | some j => exact hc j
  have hC₀ : 0 < C₀ := lt_of_lt_of_le zero_lt_one
    (Finset.le_sup' upper (Finset.mem_univ (none : Option J)))
  refine ⟨c₀, hc₀, C₀, hC₀, ?_⟩
  intro i h Φ U K W χsource χout Δ hb p q hpq
  obtain ⟨j, backward, a, b, hab, rfl, rfl⟩ := hpq
  have hjlower : c₀ ≤ c j := Finset.inf'_le lower (Finset.mem_univ (some j))
  have hjupper : B j + M j ≤ C₀ := Finset.le_sup' upper (Finset.mem_univ (some j))
  obtain ⟨ha, hb'⟩ := maskedZeroEnergyRelation_covector_bounds (i j) (hb j) hab
  exact ⟨⟨hjlower.trans ha.1, ha.2.trans hjupper⟩,
    ⟨hjlower.trans hb'.1, hb'.2.trans hjupper⟩⟩

/-- The section bound and transverse ball appearing in
`UniformGeometry.exists_uniform_fieldRoot_twoTimeHamiltonPhase` supply explicit
primitive constants for `exists_uniform_physicalDirectRelation_covector_bounds`.
They depend only on the fixed section, center, radius and root bound, not on
the varying coefficient field (`app:ch_regular:lem:finite-chain`). -/
theorem rootBuffer_bounds_of_section_and_ball
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) {ε G : ℝ} (hG : 0 ≤ G)
    {h : RootState (Euclidean d) → ℝ} {v : RootState (Euclidean d)}
    (hball : v.2.2 ∈ Metric.closedBall η₀ ε)
    (hsection : (1 / 2 : ℝ) ≤ ℓ v.2.2) (hroot : |h v| ≤ ℓ v.2.2 * G) :
    0 < 1 / (2 * (‖ℓ‖ + 1)) ∧
      1 / (2 * (‖ℓ‖ + 1)) ≤ ‖v.2.2‖ ∧
      ‖v.2.2‖ ≤ ‖η₀‖ + ε ∧
      |h v| ≤ (‖ℓ‖ * (‖η₀‖ + ε)) * G := by
  have hn := norm_nonneg ℓ
  have hden : 0 < 2 * (‖ℓ‖ + 1) := by positivity
  have hlin : ℓ v.2.2 ≤ ‖ℓ‖ * ‖v.2.2‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using ℓ.le_opNorm v.2.2)
  have hu : ‖v.2.2‖ ≤ ‖η₀‖ + ε := by
    have hdist : ‖v.2.2 - η₀‖ ≤ ε := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hball
    have htri := norm_add_le (v.2.2 - η₀) η₀
    rw [sub_add_cancel] at htri
    linarith
  refine ⟨by positivity, (div_le_iff₀ hden).2 ?_, hu, ?_⟩
  · nlinarith [norm_nonneg v.2.2]
  · exact hroot.trans (mul_le_mul_of_nonneg_right
      (hlin.trans (mul_le_mul_of_nonneg_left hu hn)) hG)

/-- The fixed section, transverse ball and root-value bounds produced by
`UniformGeometry/Construction` give common annular endpoints before the
varying family is chosen. Only restriction of those SAME producer estimates
to the selected buffers remains with the parent
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_physicalDirectRelation_bounds_of_section
    {J : Type*} [Finite J] (ℓ : J → Euclidean d →L[ℝ] ℝ)
    (η₀ : J → Euclidean d) (ε G : J → ℝ) (hG : ∀ j, 0 ≤ G j) :
    ∃ c₀ > (0 : ℝ), ∃ C₀ > (0 : ℝ),
      ∀ (i : J → Fin (d + 1)) (h : J → RootState (Euclidean d) → ℝ)
        (Φ : J → RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (U K : J → Set (RootState (Euclidean d))) (W : Set (Euclidean (d + 1)))
        (χsource χout : J → Euclidean (d + 1) → ℂ) (Δ : ℝ),
        (∀ j v, v ∈ U j ∪ K j →
          v.2.2 ∈ Metric.closedBall (η₀ j) (ε j) ∧
          (1 / 2 : ℝ) ≤ ℓ j v.2.2 ∧ |h j v| ≤ ℓ j v.2.2 * G j) →
        ∀ p q, physicalDirectRelation i h Φ U K W χsource χout Δ p q →
          (c₀ ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ C₀) ∧ (c₀ ≤ ‖q.2‖ ∧ ‖q.2‖ ≤ C₀) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, hbounds⟩ :=
    exists_uniform_physicalDirectRelation_covector_bounds
      (fun j ↦ 1 / (2 * (‖ℓ j‖ + 1))) (fun j ↦ ‖η₀ j‖ + ε j)
      (fun j ↦ (‖ℓ j‖ * (‖η₀ j‖ + ε j)) * G j) (by intro j; positivity)
  refine ⟨c₀, hc₀, C₀, hC₀, ?_⟩
  intro i h Φ U K W χsource χout Δ hb
  apply hbounds i h Φ U K W χsource χout Δ
  intro j v hv
  obtain ⟨hball, hsection, hroot⟩ := hb j v hv
  exact (rootBuffer_bounds_of_section_and_ball (ℓ j) (η₀ j) (hG j)
    hball hsection hroot).2

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
