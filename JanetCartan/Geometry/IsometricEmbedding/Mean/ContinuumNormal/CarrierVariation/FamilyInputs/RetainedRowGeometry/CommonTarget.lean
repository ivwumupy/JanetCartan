module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.UniformConic.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.MaskBuffers

/-!
# Fixed comparison targets for the retained row's canonical masks

Use the doubled common output ball and the supported shell of the SAME
`UniformConic` construction. No mask is reduced here. In particular the
incidence root remains the center of the masks; it need not be the center of
the retained null-transport chart. These targets are consumed by
`exists_retained_conic_weighted_comparison` and
`SourceWeighted.exists_actual_source_weighted_comparison`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction.TransportSymbol
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison

variable {n : ℕ}

/-- Fixed compact output section of the canonical row's common ball. The
frequency radius is that used by its supported shell (`bg-Psi`, `bg-jacobian`). -/
def compactTarget (b : ℝ) (q₀ : Variables n × Euclidean 2) (τ : ℝ) :
    Set (Variables n × Euclidean 2) :=
  closedBall q₀ τ ∩ {q | ‖q.1.2.2‖ = b}

/-- Fixed open cone over the canonical doubled output ball. It contains the
entire punctured uncut support, not just its incidence center (`bg-Psi`). -/
def conicTarget (b : ℝ) (q₀ : Variables n × Euclidean 2) (τ : ℝ) :
    Set (Variables n × Euclidean 2) :=
  normalizedConicTarget b (ball q₀ (2 * τ))

/-- Compact and open comparison targets, with their radial law. These choices
precede every admitted frame (`app:ch_background:prop:bg-normalized`). -/
theorem target_geometry {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ)
    (q₀ : Variables n × Euclidean 2) :
    IsCompact (compactTarget b q₀ τ) ∧ IsOpen (conicTarget b q₀ τ) ∧
      compactTarget b q₀ τ ⊆ conicTarget b q₀ τ ∧
      (∀ q ∈ conicTarget b q₀ τ, q.1.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ q,
        (scaleFrequency t q.1, q.2) ∈ conicTarget b q₀ τ ↔
          q ∈ conicTarget b q₀ τ) := by
  refine ⟨(isCompact_closedBall _ _).inter_right
    (isClosed_eq continuous_fst.snd.snd.norm continuous_const),
    normalizedConicTarget_isOpen _ isOpen_ball, ?_, fun _ hq ↦ hq.1,
    fun _ ht q ↦ normalizedConicTarget_smul_iff _ _ q ht⟩
  intro q hq
  refine ⟨norm_pos_iff.mp (hq.2 ▸ hb), ?_⟩
  rw [normalizeOutputRadius_eq_self hb hq.2]
  exact closedBall_subset_ball (by linarith) hq.1

/-- Positive radial scaling preserves the original closed physical, carrier
and angular masks. No radial cutoff is introduced (`bg-T`, `bg-Psi`). -/
theorem maskSupport_scaleInput {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a t : ℝ} (ht : 0 < t) {p : InputVariables n}
    (hp : p ∈ conicMaskSupport zRoot ηb r a) :
    scaleInput t p ∈ conicMaskSupport zRoot ηb r a := by
  refine ⟨hp.1, hp.2.1, smul_ne_zero ht.ne' hp.2.2.1, ?_⟩
  simpa only [scaleInput, NormedSpace.normalize_smul_of_pos ht] using hp.2.2.2

/-- The supported-shell conclusion of `UniformConic` puts the normalized
image of EVERY original mask point in the fixed compact target. This does
not shrink the masks or assume any transformed support (`bg-Psi`). -/
theorem mask_image_mem_compactTarget
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b τ : ℝ}
    (hb : 0 < b) (q₀ : Variables n × Euclidean 2)
    (hne : ∀ p ∈ conicMaskSupport zRoot ηb r a,
      transportAveragedGradient Y p ≠ 0)
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = b → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient Y ''
        conicMaskSupport zRoot ηb r a) → (x, v) ∈ closedBall q₀ τ) :
    ∀ p ∈ conicMaskSupport zRoot ηb r a,
      normalizeOutputRadius b (augmentedTransportGradient Y p) ∈ compactTarget b q₀ τ := by
  intro p hp
  have ht : 0 < b / ‖transportAveragedGradient Y p‖ :=
    div_pos hb (norm_pos_iff.mpr (hne p hp))
  have hn : ‖(normalizeOutputRadius b (augmentedTransportGradient Y p)).1.2.2‖ = b := by
    change ‖(b / ‖transportAveragedGradient Y p‖) • transportAveragedGradient Y p‖ = b
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hne p hp))]
  refine ⟨hshell _ hn _ (subset_closure ?_), hn⟩
  exact ⟨scaleInput (b / ‖transportAveragedGradient Y p‖) p,
    maskSupport_scaleInput ht hp, augmentedTransportGradient_scaleInput ..⟩

/-- Punctured closure of the SAME unbounded transported mask lies in the
fixed open comparison cone, by the proved normalized compact range
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem mask_image_punctured_subset_conicTarget
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b τ : ℝ}
    (hb : 0 < b) (hτ : 0 < τ) (q₀ : Variables n × Euclidean 2)
    (hne : ∀ p ∈ conicMaskSupport zRoot ηb r a,
      transportAveragedGradient Y p ≠ 0)
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = b → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient Y ''
        conicMaskSupport zRoot ηb r a) → (x, v) ∈ closedBall q₀ τ) :
    closure (augmentedTransportGradient Y '' conicMaskSupport zRoot ηb r a) ∩
      {q | q.1.2.2 ≠ 0} ⊆ conicTarget b q₀ τ := by
  exact normalized_mask_image_punctured_buffer
    (target_geometry hb hτ q₀).1.isClosed
    (fun _ hq ↦ closedBall_subset_ball (by linarith : τ < 2 * τ) hq.1)
    (mask_image_mem_compactTarget hb q₀ hne hshell)

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The fixed comparison cone lies in each admitted row's actual conic
image. The premise is precisely its doubled common-ball conclusion;
positive homogeneity proves the full uncut range (`bg-Psi`). -/
theorem conicTarget_subset_symbolDomain {zRoot : Euclidean 3}
    {ηb : Euclidean (n - 1)} {r a b τ : ℝ} (hb : 0 < b)
    {q₀ : Variables n × Euclidean 2}
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T Q zRoot ηb r a) :
    conicTarget b q₀ τ ⊆ symbolDomain T Q zRoot ηb r a := by
  intro q hq
  exact (symbolDomain_smul_iff T Q
    (div_pos hb (norm_pos_iff.mpr hq.1)) q).mp
      (houtput (ball_subset_closedBall hq.2))

variable {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a β cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet zRoot a)
      (dataBox zRoot ηb r) (dataSet zRoot ηb (2 * r)) (dataBox zRoot ηb (2 * r)) V L β cJ G)
    (htrans : ∀ p ∈ physicalParameterSet zRoot a,
      ∀ u ∈ supportedCone zRoot (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hηb hr hInv htrans

/-- The row's literal zero-extended inverse is homogeneous on its entire
domain of definition, including outside the conic image. The image is
invariant under positive scaling, so the zero extension preserves both radial
laws required in the source comparison (`app:ch_background:eq:bg-Psi`). -/
theorem symbolInverse_scale_all (t : ℝ) (ht : 0 < t) (q : Variables n × Euclidean 2) :
    symbolInverse T Q zRoot ηb r a (scaleFrequency t q.1, q.2) =
      ((symbolInverse T Q zRoot ηb r a q).1, t • (symbolInverse T Q zRoot ηb r a q).2) := by
  by_cases hq : q ∈ symbolDomain T Q zRoot ηb r a
  · exact symbolInverse_smul T Q hηb hr hInv htrans hq ht
  · have hscaled : (scaleFrequency t q.1, q.2) ∉ symbolDomain T Q zRoot ηb r a :=
      fun h ↦ hq ((symbolDomain_smul_iff T Q ht q).mp h)
    have hz (w : Variables n × Euclidean 2)
        (hw : w ∉ symbolDomain T Q zRoot ηb r a) :
        symbolInverse T Q zRoot ηb r a w = 0 := by
      exact indicator_of_notMem
        (show symbolOutputCoordinates T w ∉ supportedOutput T Q zRoot ηb r a from hw) _
    rw [hz _ hscaled, hz _ hq]
    simp only [Prod.fst_zero, Prod.snd_zero, smul_zero, Prod.mk_zero_zero]

/-- Restrict the SAME row inverse to the fixed common cone. The compact
range, genuine right inverse and smoothness follow from the canonical
geometry; they are not new analytic premises (`bg-Psi`, `bg-normalized`). -/
theorem symbolInverse_on_common_target (hLV : L ⊆ V)
    {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ)
    {q₀ : Variables n × Euclidean 2} {Ki : Set (InputVariables n)}
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T Q zRoot ηb r a)
    (hrange : MapsTo (inverseCoordinates (symbolInverse T Q zRoot ηb r a))
      (closedBall q₀ (2 * τ)) Ki) :
    ContDiffOn ℝ ∞ (symbolInverse T Q zRoot ηb r a) (conicTarget b q₀ τ) ∧
    MapsTo (inverseCoordinates (symbolInverse T Q zRoot ηb r a))
      (compactTarget b q₀ τ) Ki ∧
    MapsTo (fun q ↦ inverseCoordinates (symbolInverse T Q zRoot ηb r a)
      (normalizeOutputRadius b q)) (conicTarget b q₀ τ) Ki ∧
    (∀ q ∈ conicTarget b q₀ τ,
      transportAveragedGradient (transportPosition T Q)
        (inverseCoordinates (symbolInverse T Q zRoot ηb r a) q) = q.1.2.2) ∧
    (∀ t : ℝ, 0 < t → ∀ q ∈ conicTarget b q₀ τ,
      symbolInverse T Q zRoot ηb r a (scaleFrequency t q.1, q.2) =
        ((symbolInverse T Q zRoot ηb r a q).1,
          t • (symbolInverse T Q zRoot ηb r a q).2)) := by
  have hsub := conicTarget_subset_symbolDomain T Q hb houtput
  exact ⟨(symbolInverse_smooth T Q hηb hr hInv htrans hLV).mono hsub,
    fun _ hq ↦ hrange ((closedBall_subset_closedBall (by linarith : τ ≤ 2 * τ)) hq.1),
    fun _ hq ↦ hrange (ball_subset_closedBall hq.2),
    fun _ hq ↦ transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans (hsub hq),
    fun _ ht _ hq ↦ symbolInverse_smul T Q hηb hr hInv htrans (hsub hq) ht⟩

/-- Any supplied inverse with its actual input range and right-inverse
identity agrees with the retained row inverse. This applies to the source
inverse after transport matching; no continuity or comparison bound on the
unknown inverse is assumed (`app:ch_background:eq:bg-Psi`). -/
theorem inverse_eq_symbolInverse {S : Set (Variables n × Euclidean 2)}
    {v : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    (hrange : MapsTo (inverseCoordinates v) S (symbolInputDomain zRoot ηb r a))
    (heq : ∀ q ∈ S,
      transportAveragedGradient (transportPosition T Q) (inverseCoordinates v q) = q.1.2.2) :
    EqOn v (symbolInverse T Q zRoot ηb r a) S := by
  intro q hq
  have hh := symbolInverse_augmentedTransportGradient T Q hηb hr hInv htrans (hrange hq)
  have hright : augmentedTransportGradient (transportPosition T Q) (inverseCoordinates v q) = q :=
    augmentedTransportGradient_inverseCoordinates _ _ heq hq
  rw [hright] at hh
  exact Prod.ext (congrArg (fun p : InputVariables n ↦ p.2.1.1) hh.symm)
    (congrArg (fun p : InputVariables n ↦ p.2.2) hh.symm)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
