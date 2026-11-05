module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.ConicGeometry.Normalization

/-!
# Conic continuation of the selected section-energy phase

The phases in `app:ch_response:thm:response-compatible-choice` use the literal
selected current chart. Agreement on the overlap follows from the canonical
differential, through `conicPhase_eq_of_mem_convex`. In particular no equality
with a separately chosen Hamilton family is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Positive conic continuation of the same phase used by the actual carriers
(`app:ch_response:thm:response-compatible-choice`). -/
def conicSectionEnergyPhase (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (x : Euclidean n) (η : ℝ × Euclidean (n - 1)) : ℝ :=
  (T.currentChart Q).conicPhase ℓ (x, η)

/-- The negative phase retains the exact sign convention of the primary
conjugate phase (`app:ch_response:thm:response-compatible-choice`). -/
def conjugateConicSectionEnergyPhase (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (x : Euclidean n) (η : ℝ × Euclidean (n - 1)) : ℝ :=
  -T.conicSectionEnergyPhase ℓ Q x (-η)

/-- The active cone over a strictly buffered ball in the actual canonical
product space (`app:ch_response:thm:response-compatible-choice`). -/
def sectionEnergyCone (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ) :
    Set (ℝ × Euclidean (n - 1)) :=
  canonicalCone ℓ (ball T.data.adapted.baseData.2 r)

/-- The active canonical cone is open
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergyCone_isOpen (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ) :
    IsOpen (T.sectionEnergyCone ℓ r) := by
  simpa only [sectionEnergyCone, canonicalCone, CharacteristicRoot.conicDomain,
    CharacteristicRoot.normalize, preimage_ofPred_eq, mem_prod, mem_univ, true_and, id_eq] using
    (CharacteristicRoot.isOpen_conicDomain (X := Euclidean n) ℓ
      (isOpen_univ.prod (isOpen_ball (x := T.data.adapted.baseData.2) (ε := r)))).preimage
        ((continuous_const (y := (0 : Euclidean n))).prodMk continuous_id)

/-- Convexity holds on the entire active cone, not just near a carrier
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergyCone_convex (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ) :
    Convex ℝ (T.sectionEnergyCone ℓ r) := convex_canonicalCone ℓ (convex_ball _ _)

/-- The active cone contains every positive multiple of each of its points
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergyCone_smul (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ)
    {η : ℝ × Euclidean (n - 1)} (hη : η ∈ T.sectionEnergyCone ℓ r)
    {a : ℝ} (ha : 0 < a) : a • η ∈ T.sectionEnergyCone ℓ r := by
  refine ⟨by simpa using mul_pos ha hη.1, ?_⟩
  simpa only [map_smul, smul_eq_mul, mul_inv_rev, smul_smul,
    mul_assoc, inv_mul_cancel₀ ha.ne', mul_one] using hη.2

/-- The open active cone avoids zero and its antipode
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergyCone_disjoint_antipode
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (r : ℝ) :
    Disjoint (T.sectionEnergyCone ℓ r) (Neg.neg ⁻¹' T.sectionEnergyCone ℓ r) := by
  apply disjoint_left.mpr
  intro η hη hnη
  have h := hnη.1
  rw [map_neg] at h
  linarith [hη.1]

/-- Smoothness on the full physical ball and active cone
(`app:ch_response:thm:response-compatible-choice`). -/
theorem conicSectionEnergyPhase_smooth
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (ℝ × Euclidean (n - 1)) ↦
      T.conicSectionEnergyPhase ℓ Q q.1 q.2)
      (ball 0 T.physicalRadius ×ˢ T.sectionEnergyCone ℓ r) := by
  apply ((T.currentChart Q).contDiffOn_conicPhase ℓ (T.current_coordinates_smooth Q)).mono
  rintro ⟨x, η⟩ ⟨hx, hη⟩
  exact ⟨hη.1, T.sectionEnergyDomain_subset_target Q hx (ball_subset_ball hr hη.2)⟩

/-- Degree one at every positive scale with the original physical covector
and Fourier convention (`app:ch_response:thm:response-compatible-choice`). -/
theorem conicSectionEnergyPhase_smul
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) (Q : _)
    (x : Euclidean n) (η : ℝ × Euclidean (n - 1)) {a : ℝ} (ha : 0 < a) :
    T.conicSectionEnergyPhase ℓ Q x (a • η) = a * T.conicSectionEnergyPhase ℓ Q x η :=
  (T.currentChart Q).conicPhase_smul ℓ (x, η) ha

/-- Exact agreement on the actual buffered overlap follows from the selected
chart's radial compatibility (`app:ch_response:eq:response-exact-phase`). -/
theorem conicSectionEnergyPhase_eq_on_overlap
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : η ∈ T.sectionEnergyDomain)
    (hcone : η ∈ T.sectionEnergyCone ℓ r) :
    T.conicSectionEnergyPhase ℓ Q x η = T.sectionEnergyPhase Q x η :=
  (T.currentChart Q).conicPhase_eq_of_mem_convex ℓ isOpen_ball (convex_ball _ _)
    (fun _ hθ ↦ T.sectionEnergyDomain_subset_target Q hx hθ)
    hη hcone.1 (ball_subset_ball hr hcone.2)

/-- Exact physical gradient agreement on the open overlap; this keeps the
carrier covector unchanged (`app:ch_response:eq:response-exact-phase`). -/
theorem conicSectionEnergyPhase_gradient_eq_on_overlap
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _)
    {x : Euclidean n} (hx : x ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : η ∈ T.sectionEnergyDomain)
    (hcone : η ∈ T.sectionEnergyCone ℓ r) :
    gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y η) x =
      gradient (fun y ↦ T.sectionEnergyPhase Q y η) x := by
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact T.conicSectionEnergyPhase_eq_on_overlap ℓ hr Q hy hη hcone

/-- The continued phase has the same positive Cauchy data on the whole cone
(`app:ch_response:eq:response-energy-Cauchy`). -/
theorem conicSectionEnergyPhase_section
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _)
    {u : Euclidean (n - 1)} (hu : T.reference.sectionEmbedding u ∈ ball 0 T.physicalRadius)
    {η : ℝ × Euclidean (n - 1)} (hη : η ∈ T.sectionEnergyCone ℓ r) :
    T.conicSectionEnergyPhase ℓ Q (T.reference.sectionEmbedding u) η = ⟪u, η.2⟫_ℝ := by
  have hh := (T.currentChart Q).conicPhase_initial_value ℓ hη.1
    (T.sectionEnergy_source Q hu (ball_subset_ball hr hη.2))
  rw [T.family.section_eq Q] at hh
  exact hh

/-- The reflected phase is smooth on the reflected full active cone
(`app:ch_response:thm:response-compatible-choice`). -/
theorem conjugateConicSectionEnergyPhase_smooth
    (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ) {r : ℝ}
    (hr : r ≤ min T.family.radius (3 * T.family.sourceRadius)) (Q : _) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (ℝ × Euclidean (n - 1)) ↦
      T.conjugateConicSectionEnergyPhase ℓ Q q.1 q.2)
      (ball 0 T.physicalRadius ×ˢ (Neg.neg ⁻¹' T.sectionEnergyCone ℓ r)) :=
  ((T.conicSectionEnergyPhase_smooth ℓ hr Q).comp
    (contDiffOn_fst.prodMk contDiffOn_snd.neg) (fun _ h ↦ h)).neg

/-- A fixed open convex active cone and a compact overlap neighborhood of the
entire primary family, with exact phase and gradient matching for every current
frame. No primary covectors are discarded
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_conicSectionEnergyPhase_primary {c C : ℝ} (hP : P.IsValid c C) :
    ∃ (r : ℝ) (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ)
      (V : Set (ℝ × Euclidean (n - 1))),
      0 < r ∧ r < min T.family.radius (3 * T.family.sourceRadius) ∧
      IsOpen V ∧ IsCompact (closure V) ∧ T.primaryCanonicalCompact ⊆ V ∧
      closure V ⊆ T.sectionEnergyDomain ∩ T.sectionEnergyCone ℓ r ∧
      IsOpen (T.sectionEnergyCone ℓ r) ∧ Convex ℝ (T.sectionEnergyCone ℓ r) ∧
      ∀ Q, ∀ x ∈ ball 0 T.physicalRadius,
        (∀ η ∈ closure V,
          T.conicSectionEnergyPhase ℓ Q x η = T.sectionEnergyPhase Q x η) ∧
        ∀ z ∈ parameterCube P.radius,
          T.conicSectionEnergyPhase ℓ Q x (T.primaryCanonical z) = T.carrier Q x z ∧
          gradient (fun y ↦ T.conicSectionEnergyPhase ℓ Q y (T.primaryCanonical z)) x =
            T.carrierGradient Q x z := by
  obtain ⟨r, ℓ, hr, hrR, hK⟩ := T.exists_primary_conic_normalization hP
  have hKD : T.primaryCanonicalCompact ⊆ T.sectionEnergyDomain ∩ T.sectionEnergyCone ℓ r :=
    fun η hη ↦ ⟨ball_subset_ball hrR.le (hK hη).1, (hK hη).2⟩
  obtain ⟨V, hV, hKV, hVD, hcV⟩ := exists_open_between_and_isCompact_closure
    (T.primaryCanonicalCompact_isCompact hP)
    (isOpen_ball.inter (T.sectionEnergyCone_isOpen ℓ r)) hKD
  refine ⟨r, ℓ, V, hr, hrR, hV, hcV, hKV, hVD,
    T.sectionEnergyCone_isOpen ℓ r, T.sectionEnergyCone_convex ℓ r, ?_⟩
  intro Q x hx
  refine ⟨fun η hη ↦ T.conicSectionEnergyPhase_eq_on_overlap ℓ hrR.le Q hx
    (hVD hη).1 (hVD hη).2, ?_⟩
  intro z hz
  have hmem := hKD ⟨z, hz, rfl⟩
  exact ⟨T.conicSectionEnergyPhase_eq_on_overlap ℓ hrR.le Q hx hmem.1 hmem.2,
    T.conicSectionEnergyPhase_gradient_eq_on_overlap ℓ hrR.le Q hx hmem.1 hmem.2⟩

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
