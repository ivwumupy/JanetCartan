module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.Symbols
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase

/-!
# A supported smooth phase with the exact global diagonal

The conic phase is not smooth at zero. A closed carrier separated from zero
by the original radial cutoff admits a smooth auxiliary phase agreeing as a
joint germ on that carrier. Localizing the difference from `y · η` preserves
the diagonal everywhere, including outside the chart. This is the phase
input of `CompleteResidual.completeResidual_operators_of_graph_regularizations`;
it does not extend any amplitude or cancellation identity by assertion.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification
open ConicPhase
variable {d q : ℕ}
local notation "T" => TwoTimePoint (Euclidean d)
local notation "E" => Euclidean (d + 1)

/-- Recover the SAME flow's initial condition from the precise diagonal
and differential outputs exported by `exists_pencil_leading_amplitude`.
The covector derivative of the diagonal phase fixes the inverse footpoint;
the exported diagonal state then gives the initial flow value. Thus no
second existential flow or unexported initial-condition premise is needed.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem flow_initial_of_diagonal_outputs
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (I : Set ℝ) {U : Set (Euclidean d × Euclidean d)} (hU : IsOpen U)
    (hdiff : ∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p)
    (hdiag : ∀ w ∈ I ×ˢ U, (w.1, w) ∈ C.target ∧
      twoTimeState Φ (C.symm (w.1, w)) = w ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ)
    (w : RootState (Euclidean d)) (hw : w ∈ I ×ˢ U) : Φ (w, 0) = w := by
  have hd := hasFDerivAt_twoTimePhase_covector (hdiff _ (hdiag w hw).1)
  have he : (fun η ↦ twoTimePhase C (w.1, (w.1, (w.2.1, η)))) =ᶠ[𝓝 w.2.2]
      fun η ↦ ⟪w.2.1, η⟫_ℝ := by
    have hn : (fun η : Euclidean d ↦ (w.2.1, η)) ⁻¹' U ∈ 𝓝 w.2.2 :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hw.2)
    filter_upwards [hn] with η hη
    exact (hdiag (w.1, (w.2.1, η)) ⟨hw.1, hη⟩).2.2
  have hfoot : (C.symm (w.1, w)).2.2.1 = w.2.1 :=
    innerSL_inj.mp (hd.unique (((innerSL ℝ w.2.1).hasFDerivAt).congr_of_eventuallyEq he))
  obtain ⟨ht, hs, hη, _⟩ := twoTimeChart_inverse_coordinates hC (hdiag w hw).1
  have hinv : C.symm (w.1, w) = (w.1, w) := Prod.ext ht (Prod.ext hs (Prod.ext hfoot hη))
  simpa only [hinv, twoTimeState, sub_self] using (hdiag w hw).2.1

/-- The phase diagonal on the entire image of the transport source box
follows from the SAME flow's initial condition, including diagonal points
not initially presented in source coordinates. The initial condition is
proved by `flow_initial_of_diagonal_outputs` on these same witnesses.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem twoTimePhase_diagonal_on_image_box
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (I : Set ℝ) (U : Set (Euclidean d × Euclidean d))
    (hi : ∀ w ∈ I ×ˢ U, Φ (w, 0) = w)
    (t : ℝ) (y η : Euclidean d)
    (hp : (t, (t, (y, η))) ∈ C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))) :
    twoTimePhase C (t, (t, (y, η))) = inner ℝ y η := by
  obtain ⟨ht, hs, _, hy⟩ := twoTimeChart_inverse_coordinates hC hp.1
  have hinit := hi (C.symm (t, (t, (y, η)))).2 hp.2.2
  have hstate : twoTimeState Φ (C.symm (t, (t, (y, η)))) =
      (C.symm (t, (t, (y, η)))).2 := by
    simp only [twoTimeState, ht, hs, sub_self, hinit]
  rw [hstate] at hy
  simp only [twoTimePhase, hy]

/-- Extend the difference from the canonical diagonal phase across a closed
buffer. The buffer can be unbounded in frequency. The diagonal hypothesis is
only on the original open chart, where the actual phase producer proves it.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_smooth_diagonalPhase_extension
    (Ψ : T → ℝ) {K O : Set T} (hK : IsClosed K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hΨ : ContDiffOn ℝ ∞ Ψ O)
    (hdiag : ∀ t y η, (t, (t, (y, η))) ∈ O → Ψ (t, (t, (y, η))) = ⟪y, η⟫_ℝ) :
    ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
      (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
      ∀ p ∈ K, G =ᶠ[𝓝 p] Ψ := by
  obtain ⟨U, hU, hKU, hUO⟩ := normal_exists_closure_subset hK hO hKO
  obtain ⟨V, hV, hUV, hVO⟩ := normal_exists_closure_subset isClosed_closure hO hUO
  obtain ⟨χ, hχ, _, hsχ, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hUV
  have hs : tsupport χ ⊆ O := by simpa only [tsupport, hsχ] using hVO
  let L : T → ℝ := fun p ↦ ⟪p.2.2.1, p.2.2.2⟫_ℝ
  have hL : ContDiff ℝ ∞ L := contDiff_snd.snd.fst.inner ℝ contDiff_snd.snd.snd
  have hF : ContDiff ℝ ∞ (fun p ↦ χ p * (Ψ p - L p)) := by
    apply Localization.contDiff_of_contDiffOn_support_neighborhood hO
    · exact hχ.contDiffOn.mul (hΨ.sub hL.contDiffOn)
    · exact tsupport_mul_subset_left.trans hs
  refine ⟨fun p ↦ L p + χ p * (Ψ p - L p), hL.add hF, ?_, ?_⟩
  · intro t y η
    by_cases hp : (t, (t, (y, η))) ∈ O
    · simp [L, hdiag t y η hp]
    · have hz : χ (t, (t, (y, η))) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hs h))
      simp [L, hz]
  · intro p hp
    filter_upwards [hU.mem_nhds (hKU hp)] with z hz
    rw [(hχone z).mp (subset_closure hz)]
    ring

/-- The same auxiliary phase has exactly the smoothness convention of the
complete residual consumer. Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_curried_diagonalPhase {G : T → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      G (p.1.1, (p.1.2, (p.2.1, p.2.2)))) :=
  hG.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk
    (contDiff_snd.fst.prodMk contDiff_snd.snd)))

/-- The radial cutoff removes the cone vertex from the closed angular
carrier. This uses the original smaller angular patch and its proved margin,
not global regularity of a homogeneous phase.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem closed_radialAngularCarrier_subset
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (ε ρ : ℝ) (hρ : 0 < ρ)
    (hmargin : closure (angularCone ℓ η₀ (ε / 2)) \ {0} ⊆ angularCone ℓ η₀ ε) :
    IsClosed ({η : Euclidean d | ρ ≤ ‖η‖} ∩ closure (angularCone ℓ η₀ (ε / 2))) ∧
      {η : Euclidean d | ρ ≤ ‖η‖} ∩ closure (angularCone ℓ η₀ (ε / 2)) ⊆
        angularCone ℓ η₀ ε := by
  refine ⟨(isClosed_le continuous_const continuous_norm).inter isClosed_closure, ?_⟩
  intro η hη
  apply hmargin ⟨hη.2, ?_⟩
  intro hz
  have : η = 0 := hz
  simpa [this] using hρ.trans_le hη.1

/-- Construct the phase required by the residual from the SAME conic chart,
using the original radial and angular supports and physical output mask.
`hbuffer`, `hs`, `hdiag` and `hmargin` are outputs of
`BufferedKernel.exists_buffered_physical_pencil_kernel` and
`ConicPhase.exists_buffered_conicPhase`. The support assumptions are the
actual mask geometry; no global phase or cancellation is an input.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_smooth_supported_conicPhase
    (ℓ : Euclidean d →L[ℝ] ℝ)
    (C : OpenPartialHomeomorph T T) {z : RootState (Euclidean d)} {ε δ ρ : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) (hρ : 0 < ρ)
    (hbuffer : Metric.closedBall (z.1, z) (2 * ε) ⊆ C.target)
    (hs : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiag : ∀ w ∈ Metric.ball z.1 δ ×ˢ Metric.ball z.2 δ,
      twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ)
    (hmargin : closure (angularCone ℓ z.2.2 (ε / 2)) \ {0} ⊆ angularCone ℓ z.2.2 ε)
    (χout : E → ℂ) (hχ : tsupport χout ⊆ elapsedPhysicalBox z ε) :
    ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
      (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
      ∀ r ∈ Icc 0 ε, ∀ x ∈ tsupport χout, ∀ η : Euclidean d,
        ρ ≤ ‖η‖ → η ∈ closure (angularCone ℓ z.2.2 (ε / 2)) →
          G =ᶠ[𝓝 (x 0, (x 0 - r, (spatialPart x, η)))] ConicPhase.phase ℓ C := by
  let F := {η : Euclidean d | ρ ≤ ‖η‖} ∩ closure (angularCone ℓ z.2.2 (ε / 2))
  obtain ⟨hF, hFD⟩ := closed_radialAngularCarrier_subset ℓ z.2.2 ε ρ hρ hmargin
  let X : T → E := fun p ↦ timeSpacePoint p.1 p.2.2.1
  have hX : Continuous X := continuous_timeSpacePoint.comp (continuous_fst.prodMk continuous_snd.snd.fst)
  let K : Set T := {p | X p ∈ tsupport χout ∧ p.1 - p.2.1 ∈ Icc 0 ε ∧ p.2.2.2 ∈ F}
  have hK : IsClosed K := (isClosed_tsupport χout).preimage hX |>.inter
    ((isClosed_Icc.preimage (continuous_fst.sub continuous_snd.fst)).inter
      (hF.preimage continuous_snd.snd.snd))
  let O := ConicPhase.domain ℓ C.target ∩
    {p : T | X p ∈ elapsedPhysicalBox z ε ∧ p.2.2.2 ∈ angularCone ℓ z.2.2 ε}
  have hO : IsOpen O := (ConicPhase.isOpen_domain ℓ C.open_target).inter
    (((isOpen_elapsedPhysicalBox z ε).preimage hX).inter
      ((isOpen_angularCone ℓ z.2.2 ε).preimage continuous_snd.snd.snd))
  have hKO : K ⊆ O := by
    intro p hp
    have hx := hχ hp.1
    have hη := hFD hp.2.2
    refine ⟨?_, hx, hη⟩
    have hm := ConicPhase.elapsed_mem_domain_closedBuffer ℓ hε hp.2.1 hx hη
    have he : (X p 0, (X p 0 - (p.1 - p.2.1), (spatialPart (X p), p.2.2.2))) = p := by
      simp [X]
    rw [he] at hm
    exact ⟨hm.1, hbuffer hm.2⟩
  obtain ⟨G, hG, hGdiag, he⟩ := exists_smooth_diagonalPhase_extension (ConicPhase.phase ℓ C)
    hK hO hKO ((ConicPhase.contDiffOn_phase ℓ hs).mono inter_subset_left)
    (fun t y η hp ↦ ConicPhase.phase_diagonal_on_buffer ℓ C hεδ hdiag
      (x := timeSpacePoint t y) hp.2.1 hp.2.2)
  refine ⟨G, hG, hGdiag, ?_⟩
  intro r hr x hx η hη hangle
  apply he
  change X _ ∈ tsupport χout ∧ _ ∈ Icc 0 ε ∧ _ ∈ F
  have hpoint : timeSpacePoint (x 0) (spatialPart x) = x :=
    timeSpaceMeasurableEquiv.symm_apply_apply x
  simpa [X, F, hpoint] using And.intro hx (And.intro hr (And.intro hη hangle))

/-- The smooth diagonal auxiliary gives the very same elapsed operator,
including both physical masks and the original right multiplier. Its literal
Hilbert adjoint is consequently unchanged as well. `he` is the conclusion of
`exists_smooth_supported_conicPhase`, for the same `ℓ,C,χout,ρ,ε`.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem elapsedGraph_eq_of_supported_diagonalPhase
    (ℓ : Euclidean d →L[ℝ] ℝ) (C : OpenPartialHomeomorph T T)
    (η₀ : Euclidean d) (ε ρ : ℝ) (G : T → ℝ)
    (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (he : ∀ r ∈ Icc 0 ε, ∀ x ∈ tsupport χout, ∀ η : Euclidean d,
      ρ ≤ ‖η‖ → η ∈ closure (angularCone ℓ η₀ (ε / 2)) →
        G =ᶠ[𝓝 (x 0, (x 0 - r, (spatialPart x, η)))] ConicPhase.phase ℓ C)
    (hβ : ∀ ξ, β ξ ≠ 0 → ρ ≤ ‖spatialPart ξ‖ ∧
      spatialPart ξ ∈ angularCone ℓ η₀ (ε / 2))
    {r : ℝ} (hr : r ∈ Icc 0 ε) :
    elapsedGraph (fun t s y η ↦ G (t, (s, (y, η)))) b χout χsource β r =
      elapsedGraph (curriedPhase ℓ C) b χout χsource β r := by
  apply FourierIntegral.FullLowBounds.fullGraphOperator_phase_congr
  intro x z ξ hA
  have hx : χout x ≠ 0 := fun hx ↦ hA
    (elapsedAmplitude_eq_zero_of_mask b χout χsource β r x z ξ (Or.inl hx))
  have hξ : β ξ ≠ 0 := fun hξ ↦ hA
    (elapsedAmplitude_eq_zero_of_mask b χout χsource β r x z ξ (Or.inr (Or.inr hξ)))
  have hg := (he r hr x (subset_tsupport χout hx) (spatialPart ξ)
    (hβ ξ hξ).1 (subset_closure (hβ ξ hξ).2)).eq_of_nhds
  exact congrArg (fun a ↦ (x 0 - r) * ξ 0 + a) hg

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
