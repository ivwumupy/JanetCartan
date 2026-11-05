module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.ConicColumns
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.ExtensionGerms

/-!
# Global cancellation for the actual supported conic kernel

The actual column outputs, their transported compact support and the original
flow initial condition produce one globally smooth phase with the exact
global diagonal. The continued, supported matrices cancel for EVERY source
time and covector on the auxiliary output-time plateau. Outside their joint
support the proof uses zero germs; on it the proof applies the published
conic column identity. No global cancellation premise is introduced.

Inputs are retained from `exists_pencil_leading_amplitude` and
`exists_twoTime_transport_box`. The same flow's initial condition is
derived by `flow_initial_of_diagonal_outputs`; no second flow is chosen.
The compact source and time masks and the frequency plateau are chosen on those same witnesses. The latter is produced
by `exists_conicFrequency_plateau` from the original radial/angular carrier.
Consumer: `CompleteResidual.completeResidual_operators_of_graph_regularizations`.
Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)

/-- Construct the global phase and discharge the consumer's all-source,
all-frequency column cancellation for the literal supported conic matrices.
The phase-diagonal and column assumptions are precise local outputs of
the named original producers. This does not assert the off-root PDO identity
or any operator bound. Source: `app:ch_regular_base:eq:two-term-null-identity`. -/
theorem exists_smooth_supported_conic_cancellation
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (h : RootState (Euclidean d) → ℝ)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin (d + 1)) (σ : RootState (Euclidean d) → ℝ)
    {I : Set ℝ} {U : Set (Euclidean d × Euclidean d)}
    (hI : IsOpen I) (hU : IsOpen U) (hbox : I ×ˢ (I ×ˢ U) ⊆ C.source)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκI : tsupport κ ⊆ I) (hcσ : HasCompactSupport σ) (hσI : tsupport σ ⊆ I ×ˢ U)
    (ρ : Euclidean d → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (hphase : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p)
    (hclock : ∀ p ∈ C.target, (twoTimeState Φ (C.symm p)).1 = p.1)
    (hdiagonal : ∀ w ∈ I ×ˢ U, (w.1, w) ∈ C.target ∧
      twoTimeState Φ (C.symm (w.1, w)) = w ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ)
    (hcols : ∀ j, ContDiffOn ℝ ∞ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))) ∧
      ContDiffOn ℝ ∞ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
        (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))))
    (hnull : ∀ p ∈ C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U)), ∀ j,
      rootPencil (coordinateSplit i) Q h (twoTimeState Φ (C.symm p)) *ᵥ
        pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j p = 0)
    (hcorr : ∀ p ∈ C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U)), ∀ j,
      rootPencil (coordinateSplit i) Q h (twoTimeState Φ (C.symm p)) *ᵥ
        pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j p =
      adaptedPencilApply (coordinateSplit i) Q B
        (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j) p) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
    let F₀ := fun p : T ↦ bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2
    let F₁ := fun p : T ↦ bufferedAmplitude V κ (correction i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2
    let W₀ := curryCharacteristicMatrix (supportedConicMatrix ℓ 0 ρ F₀)
    let W₁ := curryCharacteristicMatrix (supportedConicMatrix ℓ 1 ρ F₁)
    ContDiff ℝ ∞ (supportedConicMatrix ℓ 0 ρ F₀) ∧
    ContDiff ℝ ∞ (supportedConicMatrix ℓ 1 ρ F₁) ∧
    ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
      (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
      (∀ p ∈ tsupport (supportedConicMatrix ℓ 0 ρ F₀) ∪
        tsupport (supportedConicMatrix ℓ 1 ρ F₁), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
      ∀ x : E, κ =ᶠ[𝓝 (x 0)] (fun _ ↦ 1) → ∀ s η j,
        WKB.firstOrderApply (fun y a ↦ ((coefficient i Q y a).map Complex.ofReal).mulVecLin)
          (fun y ↦ ((zeroth i B y).map Complex.ofReal).mulVecLin)
          (fun y ↦ Complex.exp (Complex.I * (G (y 0, (s, (spatialPart y, η))) : ℂ)) •
            (fun k ↦ (W₀ + W₁) (y 0) s (spatialPart y) η k j)) x =
          Complex.exp (Complex.I * (G (x 0, (s, (spatialPart x, η))) : ℂ)) •
            (fun k ↦ twoTimePhysicalApply (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
              (fun y ↦ (zeroth i B y).map Complex.ofReal) W₁ (x 0) s (spatialPart x) η k j) := by
  dsimp only
  have hi := flow_initial_of_diagonal_outputs h Φ C hC I hU hdiff hdiagonal
  let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ U))
  let F₀ := fun p : T ↦ bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
    p.1 p.2.1 p.2.2.1 p.2.2.2
  let F₁ := fun p : T ↦ bufferedAmplitude V κ (correction i Q B h Φ C r c σ)
    p.1 p.2.1 p.2.2.1 p.2.2.2
  let J₀ := supportedConicMatrix ℓ 0 ρ F₀
  let J₁ := supportedConicMatrix ℓ 1 ρ F₁
  let K := tsupport J₀ ∪ tsupport J₁
  have hV : IsOpen V := C.symm.continuousOn.isOpen_inter_preimage
    C.open_target (hI.prod (hI.prod hU))
  obtain ⟨hs₀, hs₁⟩ := buffered_pencil_matrices_support i Q B h Φ C hC r c σ
    hI hU hbox κ hκ hcκ hκI hcσ hσI hcols
  have hKO : K ⊆ ConicPhase.domain ℓ V := union_subset
    (tsupport_supportedConicMatrix_subset ℓ 0 ρ hsρ F₀ hs₀)
    (tsupport_supportedConicMatrix_subset ℓ 1 ρ hsρ F₁ hs₁)
  obtain ⟨hF₀, hF₁⟩ := contDiff_buffered_pencil_matrices i Q B h Φ C hC r c σ
    hI hU hbox κ hκ hcκ hκI hcσ hσI hcols
  have hp : ContDiff ℝ ∞ (fun p : T ↦ ((p.1, p.2.1), (p.2.2.1, p.2.2.2))) :=
    (contDiff_fst.prodMk contDiff_snd.fst).prodMk
      (contDiff_snd.snd.fst.prodMk contDiff_snd.snd.snd)
  have hJ₀ : ContDiff ℝ ∞ J₀ := contDiff_supportedConicMatrix ℓ 0 ρ hρ hsρ F₀ (hF₀.comp hp)
  have hJ₁ : ContDiff ℝ ∞ J₁ := contDiff_supportedConicMatrix ℓ 1 ρ hρ hsρ F₁ (hF₁.comp hp)
  have hphaseV : ContDiffOn ℝ ∞ (ConicPhase.phase ℓ C) (ConicPhase.domain ℓ V) :=
    ConicPhase.contDiffOn_extend ℓ hV (hphase.mono inter_subset_left)
  obtain ⟨G, hG, hdiag, he⟩ := exists_smooth_diagonalPhase_extension (ConicPhase.phase ℓ C)
    ((isClosed_tsupport J₀).union (isClosed_tsupport J₁)) (ConicPhase.isOpen_domain ℓ hV)
    hKO hphaseV (fun t y η hp ↦ ConicPhase.phase_diagonal ℓ C hp.1.ne'
      (twoTimePhase_diagonal_on_image_box Φ C hC I U hi t y ((ℓ η)⁻¹ • η) hp.2))
  refine ⟨hJ₀, hJ₁, G, hG, hdiag, he, ?_⟩
  intro x hκx s η j
  let p : T := (x 0, (s, (spatialPart x, η)))
  have hsl : ContinuousAt (fun y : E ↦ (y 0, (s, (spatialPart y, η)))) x :=
    (contDiff_physicalSlice (coordinateSplit (0 : Fin (d + 1))) s η).continuous.continuousAt
  by_cases hpK : p ∈ K
  · have hpO := hKO hpK
    have hpV := hpO.2
    have hid := conic_column_cancellation ℓ i Q B h Φ C r c σ s η x hpO.1
      (hdiff _ hpV.1) (hclock _ hpV.1)
      (twoTimeChart_inverse_coordinates hC hpV.1).2.2.2
      (fun k ↦ ((hcols k).1.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp))
      (fun k ↦ ((hcols k).2.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp))
      (hnull _ hpV) (hcorr _ hpV) j
    refine column_cancellation_of_scaled_germs
      (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth i B y).map Complex.ofReal)
      (fun t s y η ↦ ConicPhase.phase ℓ C (t, (s, (y, η))))
      (fun t s y η ↦ G (t, (s, (y, η)))) _ _ _ _ (ρ η : ℂ) s η x j
      ((he p hpK).comp_tendsto hsl)
      ?_ ?_ hid
    · exact supportedConic_buffered_slice_germ ℓ 0 ρ hV κ (leading i Q B h Φ C r c σ)
        s η x hpO.1.ne' hpV hκx
    · exact supportedConic_buffered_slice_germ ℓ 1 ρ hV κ (correction i Q B h Φ C r c σ)
        s η x hpO.1.ne' hpV hκx
  · have hn₀ : p ∉ tsupport J₀ := fun hp ↦ hpK (Or.inl hp)
    have hn₁ : p ∉ tsupport J₁ := fun hp ↦ hpK (Or.inr hp)
    exact column_cancellation_of_zero_germs
      (fun y a ↦ (coefficient i Q y a).map Complex.ofReal)
      (fun y ↦ (zeroth i B y).map Complex.ofReal)
      (fun t s y η ↦ G (t, (s, (y, η)))) _ _ s η x j
      ((notMem_tsupport_iff_eventuallyEq.mp hn₀).comp_tendsto hsl)
      ((notMem_tsupport_iff_eventuallyEq.mp hn₁).comp_tendsto hsl)

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
