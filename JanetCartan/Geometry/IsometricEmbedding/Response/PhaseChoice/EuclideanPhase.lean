module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry

/-!
# The selected phase in Euclidean canonical coordinates

These are the literal phases consumed by the forward and reverse graph estimates
in `app:ch_response:thm:response-literal-transfer`. The fixed section equivalence
preserves the canonical pairing; its norm comparison is explicit in
`ConicGeometry.Coordinates`. No new Hamilton chart is chosen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual positive phase in the Euclidean canonical variables used by
the graph kernels (`app:ch_response:thm:response-compatible-choice`). -/
def euclideanSectionEnergyPhase (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (x η : Euclidean n) : ℝ :=
  T.conicSectionEnergyPhase ℓ Q x (T.sectionCanonicalEquiv.symm η)

/-- The exact conjugate partner in the same coordinates
(`app:ch_response:thm:response-compatible-choice`). -/
def euclideanConjugateSectionEnergyPhase (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (x η : Euclidean n) : ℝ :=
  -T.euclideanSectionEnergyPhase ℓ Q x (-η)

/-- The entire active cone, including all radial scales
(`app:ch_response:thm:response-literal-transfer`, complete complement). -/
def euclideanSectionEnergyCone (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ) :
    Set (Euclidean n) := T.sectionCanonicalEquiv '' T.sectionEnergyCone ℓ r

/-- The whole primary family in the graph's canonical coordinates
(`app:ch_response:thm:response-compatible-choice`). -/
def euclideanPrimaryCompact : Set (Euclidean n) :=
  T.sectionCanonicalEquiv '' T.primaryCanonicalCompact

/-- Membership in the active Euclidean cone is exactly membership in the
original canonical cone (`app:ch_response:thm:response-literal-transfer`). -/
theorem mem_euclideanSectionEnergyCone
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ) (η : Euclidean n) :
    η ∈ T.euclideanSectionEnergyCone ℓ r ↔
      T.sectionCanonicalEquiv.symm η ∈ T.sectionEnergyCone ℓ r := by
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    simpa using hζ
  · intro h
    exact ⟨_, h, T.sectionCanonicalEquiv.apply_symm_apply η⟩

/-- The entire active Euclidean cone is open and convex
(`app:ch_response:thm:response-literal-transfer`). -/
theorem euclideanSectionEnergyCone_open_convex
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ) :
    IsOpen (T.euclideanSectionEnergyCone ℓ r) ∧
      Convex ℝ (T.euclideanSectionEnergyCone ℓ r) := by
  exact ⟨T.sectionCanonicalEquiv.toHomeomorph.isOpenMap _
    (T.sectionEnergyCone_isOpen ℓ r),
    (T.sectionEnergyCone_convex ℓ r).linear_image T.sectionCanonicalEquiv.toLinearMap⟩

/-- Positive scaling preserves the full active cone
(`app:ch_response:thm:response-literal-transfer`). -/
theorem euclideanSectionEnergyCone_smul
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ)
    {η : Euclidean n} (hη : η ∈ T.euclideanSectionEnergyCone ℓ r)
    {ρ : ℝ} (hρ : 0 < ρ) : ρ • η ∈ T.euclideanSectionEnergyCone ℓ r := by
  rw [T.mem_euclideanSectionEnergyCone] at hη ⊢
  simpa only [map_smul] using T.sectionEnergyCone_smul ℓ r hη hρ

/-- Compactness and nonvanishing of the whole primary family in the exact
graph coordinates (`app:ch_response:thm:response-compatible-choice`). -/
theorem euclideanPrimaryCompact_compact_nonzero {c C : ℝ} (hP : P.IsValid c C) :
    IsCompact T.euclideanPrimaryCompact ∧
      ∀ ζ ∈ T.euclideanPrimaryCompact, ζ ≠ 0 := by
  refine ⟨(T.primaryCanonicalCompact_isCompact hP).image
    T.sectionCanonicalEquiv.continuous, ?_⟩
  rintro ζ ⟨η, hη, rfl⟩ he
  have hη0 : η = 0 := T.sectionCanonicalEquiv.injective (he.trans (map_zero _).symm)
  exact T.zero_notMem_sectionEnergyDomain (hη0 ▸ T.primaryCanonicalCompact_subset hP hη)

/-- Joint smoothness of the literal Euclidean phase on the entire cone
(`app:ch_response:thm:response-literal-transfer`). -/
theorem euclideanSectionEnergyPhase_smooth
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _) :
    ContDiffOn ℝ ∞ (Function.uncurry (T.euclideanSectionEnergyPhase ℓ Q))
      (ball 0 T.physicalRadius ×ˢ T.euclideanSectionEnergyCone ℓ r) := by
  exact (T.conicSectionEnergyPhase_smooth ℓ hr Q).comp
    (contDiffOn_fst.prodMk (T.sectionCanonicalEquiv.symm.contDiff.comp_contDiffOn
      contDiffOn_snd)) (fun q hq ↦ ⟨hq.1,
        (T.mem_euclideanSectionEnergyCone ℓ r q.2).mp hq.2⟩)

/-- The physical derivative exists at every point of the active cone
(`app:ch_response:thm:response-literal-transfer`). -/
theorem euclideanSectionEnergyPhase_differentiableAt
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _)
    {x η : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    (hη : η ∈ T.euclideanSectionEnergyCone ℓ r) :
    DifferentiableAt ℝ (fun y ↦ T.euclideanSectionEnergyPhase ℓ Q y η) x := by
  have hs := (T.euclideanSectionEnergyPhase_smooth ℓ hr Q).contDiffAt (x := (x, η))
    ((isOpen_ball.prod (T.euclideanSectionEnergyCone_open_convex ℓ r).1).mem_nhds ⟨hx, hη⟩)
  exact (hs.differentiableAt (by simp)).comp (f := fun y : Euclidean n ↦ (y, η)) x
    (differentiableAt_id.prodMk (differentiableAt_const η))

/-- Exact degree-one homogeneity with no change of Fourier normalization
(`app:ch_response:thm:response-literal-transfer`). -/
theorem euclideanSectionEnergyPhase_smul
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (Q : _)
    (x η : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ) :
    T.euclideanSectionEnergyPhase ℓ Q x (ρ • η) =
      ρ * T.euclideanSectionEnergyPhase ℓ Q x η := by
  simp only [euclideanSectionEnergyPhase, map_smul,
    T.conicSectionEnergyPhase_smul ℓ Q x _ hρ]

/-- The exact negative physical gradient under conjugation
(`app:ch_response:eq:response-exact-phase`). -/
theorem euclideanConjugateSectionEnergyPhase_gradient
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (Q : _) (x η : Euclidean n) :
    gradient (fun y ↦ T.euclideanConjugateSectionEnergyPhase ℓ Q y η) x =
      -gradient (fun y ↦ T.euclideanSectionEnergyPhase ℓ Q y (-η)) x := by
  change gradient (-(fun y ↦ T.euclideanSectionEnergyPhase ℓ Q y (-η))) x = _
  simp only [gradient, fderiv_neg, map_neg]

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
