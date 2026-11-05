module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.CoefficientLocalization
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.OriginalKernels
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.PhysicalPairing
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.TimePlateau

/-!
# The complete residual for one literal selected physical chart

Apply the uncut residual theorem to the actual supported conic columns and
selected-minor complement. Global coefficients are constructed internally and
removed from every masked kernel and tested equation. No cancellation,
leading-endpoint or complement equation is an input.

The precise remaining inputs and their producers are:

* `hphase`, `hdiff`, `hclock`, `hdiagonal`, `hcols`, `hinit`, `hnull`,
  `hcorr`: the SAME `exists_pencil_leading_amplitude` witnesses, restricted
  to the source box from `exists_twoTime_transport_box`. These are local
  geometric and transport outputs, not global cancellation premises.
* `hXF`: `exists_common_complement_neighborhood` for the SAME root and minor;
  the parent selects the original source and right-multiplier supports there.
* `hchart`: `normalized_elapsed_mem_transport_buffer`, using the closed
  buffer from `exists_buffered_physical_pencil_kernel`, the physical output
  box and original angular carrier. No identity is extended outside it.
* `κ`, `hκ`, `hcκ`, `hκI`, `hκout`: `exists_outputTime_plateau` from the
  original compact output carrier inside `I`. `ρ`, `hρ`, `hsρ`, `hρβ`:
  `exists_conicFrequency_plateau` from the original closed angular/radial
  carrier. The lower source-time buffer `hbuffer` is retained exactly.

Both the regularizations and final operators use the ORIGINAL conic phase,
conic columns, multiplier and physical masks. Auxiliary phase, amplitude
and coefficient extensions occur only inside the proof. The equation is
restricted to the measurement plateau only after invoking the complete
residual consumer, whose finite identity retains the output commutator.
Primitive graph regularizations come from
`FullLowBounds.exists_fullGraphFamily_of_primitive_inputs` and its whole-image
phase specialization; `KernelIdentification` consumes them for the retarded
realization. PDO regularizations come from `PdoRealization.directPDOSymbols_regularizations`.
Uniform budgets, common finite-family selection and output H1 regularity
remain the regular-sector parent's obligations.

Source: `app:ch_regular_base:eq:two-term-null-identity` and
`app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Set Filter Matrix MeasureTheory
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ResidualCoordinates
open EvolutionIntegral EvolutionIntegral.KernelIdentification AmplitudeBounds
open JanetCartan.CharacteristicTransport.CompleteResidual
open FourierIntegral FourierIntegral.FullLowBounds FourierIntegral.LowBounds.FrequencyCutoff
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "T" => TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d + 1)
local notation "C2" => SpacetimeL2 d (d + 1)

private theorem principal_add_residual_defect (P R : C2 →L[ℂ] C2) :
    P + R = ContinuousLinearMap.id ℂ C2 + ((P - ContinuousLinearMap.id ℂ C2) + R) := by
  abel

private theorem physicalWeakApply_eq_at_coefficients
    (A A' : E → Fin (d + 1) → Mat) (B B' : E → Mat)
    (u : E → Fin (d + 1) → ℂ) (du : E → E →L[ℝ] (Fin (d + 1) → ℂ))
    {x : E} (hA : A x = A' x) (hB : B x = B' x) :
    physicalWeakApply A B u du x = physicalWeakApply A' B' u du x := by
  funext j
  simp only [physicalWeakApply, hA, hB]

/-- The original physical chart, masks and local column producers give the
complete uncut tested residual, with the literal retarded adjoints and the
physical `S+cSc` pairing. All three residual terms and `Op(α)-I` remain explicit. Coefficient and phase extensions
are constructed, and the final equation uses the ORIGINAL coefficients.
The only analytic operator inputs are the named primitive regularizations.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem completeResidual_of_selected_physical_chart
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    {Ω : Set E} (hΩ : IsOpen Ω) (Q : E → Fin (d + 1) → Mat) (B : E → Mat)
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    (h : RootState (Euclidean d) → ℝ) (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω)
    (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
    (C : OpenPartialHomeomorph T T) (hC : (C : T → T) = twoTimeProjection Φ)
    (r c : Fin (d + 1))
    (hroot : ∀ w ∈ D, (rootPencil (coordinateSplit i) Q h w).det = 0)
    {X F : Set E} (hXF : X ×ˢ F ⊆ complementDomain i Q h r c D)
    (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ)
    {I : Set ℝ} {Z : Set (Euclidean d × Euclidean d)}
    (hI : IsOpen I) (hZ : IsOpen Z) (hbox : I ×ˢ (I ×ˢ Z) ⊆ C.source)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκI : tsupport κ ⊆ I) (hcσ : HasCompactSupport σ) (hσI : tsupport σ ⊆ I ×ˢ Z)
    (hσX : ∀ w ∈ tsupport σ, timeSpacePoint w.1 w.2.1 ∈ X)
    (ρ : Euclidean d → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (hphase : ContDiffOn ℝ ∞ (twoTimePhase C) C.target)
    (hdiff : ∀ p ∈ C.target, HasFDerivAt (twoTimePhase C) (twoTimePhaseDifferential h Φ C p) p)
    (hclock : ∀ p ∈ C.target, (twoTimeState Φ (C.symm p)).1 = p.1)
    (hdiagonal : ∀ w ∈ I ×ˢ Z, (w.1, w) ∈ C.target ∧
      twoTimeState Φ (C.symm (w.1, w)) = w ∧ twoTimePhase C (w.1, w) = ⟪w.2.1, w.2.2⟫_ℝ)
    (hcols : ∀ j, ContDiffOn ℝ ∞ (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j)
      (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ Z))) ∧
      ContDiffOn ℝ ∞ (pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j)
        (C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ Z))))
    (hinit : ∀ w ∈ I ×ˢ Z, ∀ j,
      pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j (w.1, w) =
      (σ w * minorLeftNullvector (rootPencil (coordinateSplit i) Q h w)
        (rootTimeCoefficient (coordinateSplit i) Q w) r c j) •
          minorRightNullvector (rootPencil (coordinateSplit i) Q h w) r c)
    (hnull : ∀ p ∈ C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ Z)), ∀ j,
      rootPencil (coordinateSplit i) Q h (twoTimeState Φ (C.symm p)) *ᵥ
        pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j p = 0)
    (hcorr : ∀ p ∈ C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ Z)), ∀ j,
      rootPencil (coordinateSplit i) Q h (twoTimeState Φ (C.symm p)) *ᵥ
        pencilCorrectionColumn (coordinateSplit i) Q B h Φ C r c σ j p =
      adaptedPencilApply (coordinateSplit i) Q B
        (pencilLeadingColumn (coordinateSplit i) Q B h Φ C r c σ j) p)
    (β χout χsource : E → ℂ) (hβ : ContDiff ℝ ∞ β)
    (hβF : ∀ ξ ∈ tsupport β, normalizeCovector ℓ ξ ∈ F)
    (hρβ : ∀ ξ, β ξ ≠ 0 → ρ (spatialPart ξ) = 1)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (hχΩ : ∀ x ∈ tsupport χout, physicalCoordinates i x ∈ Ω)
    {U : Set E} (hU : IsOpen U) (hUX : U ⊆ X)
    (hplateau : ∀ x ∈ U, χout =ᶠ[𝓝 x] fun _ ↦ (1 : ℂ))
    (hκout : ∀ x ∈ tsupport χout, κ =ᶠ[𝓝 (x 0)] fun _ ↦ 1)
    (θ : ℕ → E → ℂ) (hθ : ∀ k, ContDiff ℝ ∞ (θ k))
    (hθcs : ∀ k, HasCompactSupport (θ k)) (a Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hbuffer : tsupport σ ⊆ {w | a < w.1})
    (hchart : ∀ τ ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ, β ξ ≠ 0 →
      ConicPhase.normalize ℓ (x 0, (x 0 - τ, (spatialPart x, spatialPart ξ))) ∈
        C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ Z))) :
    let V := C.target ∩ C.symm ⁻¹' (I ×ˢ (I ×ˢ Z))
    let F₀ : T → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun p : T ↦ bufferedAmplitude V κ (leading i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2
    let F₁ : T → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun p : T ↦ bufferedAmplitude V κ (correction i Q B h Φ C r c σ)
      p.1 p.2.1 p.2.2.1 p.2.2.2
    let W₀orig := curryCharacteristicMatrix (ConicAmplitude.extend ℓ 0
      (pencilLeadingComplexMatrix (coordinateSplit i) Q B h Φ C r c σ))
    let W₁orig := curryCharacteristicMatrix (ConicAmplitude.extend ℓ 1
      (pencilCorrectionComplexMatrix (coordinateSplit i) Q B h Φ C r c σ))
    let A : E → Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun x j ↦ (coefficient i Q x j).map Complex.ofReal
    let B₀ : E → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun x ↦ (zeroth i B x).map Complex.ofReal
    let b : Bool → TwoTimeAmplitude d (d + 1) := directRetardedAmplitudes A B₀ W₀orig W₁orig
    let sym : Fin 4 → E → E → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := directPDOSymbols A B₀ W₁orig (conicBminus ℓ i Q h r c)
      (fun x η ↦ sourceSymbol σ x ((ℓ η)⁻¹ • η)) β
    let P : Fin 4 → C2 →L[ℂ] C2 := fun k ↦ maskedPhysicalPDO χout χsource (sym k)
    ∃ G : T → ℝ, ContDiff ℝ ∞ G ∧
      (∀ t y η, G (t, (t, (y, η))) = ⟪y, η⟫_ℝ) ∧
      (∀ p ∈ tsupport (supportedConicMatrix ℓ 0 ρ F₀) ∪
        tsupport (supportedConicMatrix ℓ 1 ρ F₁), G =ᶠ[𝓝 p] ConicPhase.phase ℓ C) ∧
    let Ψ : TwoTimePhase d := fun t s y η ↦ ConicPhase.phase ℓ C (t, (s, (y, η)))
    ∀ (Treg : Bool → ℕ → ℝ → C2 →L[ℂ] C2) (Cbound : Bool → ℝ),
      (∀ k j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) (d + 1),
        Treg k j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (θ j) (elapsedAmplitude (b k) χout χsource β r)) u) →
      (∀ k j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) (d + 1),
        (Treg k j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
          (reverseGraphOperator (elapsedPhase Ψ r)
            (frequencyCutFullAmplitude (fun ξ ↦ star (θ j ξ))
              (fun x z ξ ↦ (elapsedAmplitude (b k) χout χsource β r x z ξ).conjTranspose))
            (fun x ↦ (u.val x).ofLp) z)) →
      (∀ k j r, r ∈ Icc 0 Δ → ‖Treg k j r‖ ≤ Cbound k) →
      (∀ k r, r ∈ Icc 0 Δ → ∀ u, Tendsto (fun j ↦ Treg k j r u) atTop
        (𝓝 (elapsedGraph Ψ (b k) χout χsource β r u))) →
      (∀ k r, r ∈ Icc 0 Δ → ∀ u, Tendsto (fun j ↦ (Treg k j r).adjoint u) atTop
        (𝓝 ((elapsedGraph Ψ (b k) χout χsource β r).adjoint u))) →
    ∀ Preg : Fin 4 → ℕ → C2 →L[ℂ] C2,
      (∀ k j u, Preg k j (graphTestToLp u) =ᵐ[volume] graphTestOutput
        (fun x ξ ↦ inner ℝ x ξ)
        (frequencyCutFullAmplitude (θ j) (fun x z ξ ↦ (χout x * χsource z) • sym k x ξ)) u) →
      (∀ k u, Tendsto (fun j ↦ Preg k j u) atTop (𝓝 (P k u))) →
    ∃ Rgraph : Bool → C2 →L[ℂ] C2,
      (∀ k, ‖Rgraph k‖ ≤ Δ * Cbound k) ∧
      (∀ k u, Rgraph k u = elapsedGraphIntegral Δ Ψ (b k) χout χsource β u) ∧
      (∀ k u, (Rgraph k).adjoint u =
        ∫ r in Icc 0 Δ, (elapsedGraph Ψ (b k) χout χsource β r).adjoint u) ∧
      let S : C2 →L[ℂ] C2 := Rgraph false + (1 / Complex.I) • P 0
      let R : C2 →L[ℂ] C2 := P 2 + Rgraph true + (1 / Complex.I) • P 3
      S.adjoint = (Rgraph false).adjoint + star (1 / Complex.I) • (P 0).adjoint ∧
      (∀ f φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
        physicalTestAction (coefficient i Q) (zeroth i B) (fun x ↦ (S f x).ofLp) φ j =
          ∫ x, φ x • ((P 1 + R) f) x j) ∧
      (∀ f du, Mollification.HasWeakFDerivOn volume (fun x ↦ (S f x).ofLp) du U →
        physicalWeakApply (coefficient i Q) (zeroth i B) (fun x ↦ (S f x).ofLp) du =ᵐ[volume.restrict U]
          fun x ↦ (((P 1 + R) f) x).ofLp) ∧
      (∀ f φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ j,
        physicalTestAction (coefficient i Q) (zeroth i B)
          (fun x ↦ (physicalPairedSectorSum {()} (fun _ : Unit ↦ S) f x).ofLp) φ j =
          ∫ x, φ x • ((physicalPairedSectorSum {()} (fun _ : Unit ↦ P 1) +
            physicalPairedSectorSum {()} (fun _ : Unit ↦ R)) f) x j) ∧
      P 1 + R = ContinuousLinearMap.id ℂ C2 + ((P 1 - ContinuousLinearMap.id ℂ C2) + R) := by
  intro V F₀ F₁ W₀orig W₁orig A B₀ b sym P
  let W₀ := curryCharacteristicMatrix (supportedConicMatrix ℓ 0 ρ F₀)
  let W₁ := curryCharacteristicMatrix (supportedConicMatrix ℓ 1 ρ F₁)
  have hExt := @exists_smooth_coordinate_coefficients d i Ω hΩ Q B hQ hB (tsupport χout)
    (isClosed_tsupport χout) hχΩ
  let Ae : E → Fin (d + 1) → Mat := hExt.choose
  let Be : E → Mat := hExt.choose_spec.choose
  have hAe : ContDiff ℝ ∞ Ae := hExt.choose_spec.choose_spec.1
  have hBe : ContDiff ℝ ∞ Be := hExt.choose_spec.choose_spec.2.1
  have he : ∀ x ∈ tsupport χout, Ae =ᶠ[𝓝 x] coefficient i Q ∧ Be =ᶠ[𝓝 x] zeroth i B :=
    hExt.choose_spec.choose_spec.2.2
  let bm := conicBminus ℓ i Q h r c
  let sig := conicSourceSymbol ℓ ρ σ
  have hcan := @exists_smooth_supported_conic_cancellation d ℓ i Q B h Φ C hC r c σ I Z hI hZ hbox
      κ hκ hcκ hκI hcσ hσI ρ hρ hsρ hphase hdiff hclock hdiagonal hcols hnull hcorr
  obtain ⟨hW₀, hW₁, G, hG, hdiag, hGerm, hcancel⟩ := hcan
  refine ⟨G, hG, hdiag, hGerm, ?_⟩
  intro Ψ
  let Ψext : TwoTimePhase d := fun t s y η ↦ G (t, (s, (y, η)))
  intro Treg Cbound ht htAdj htbound htlim htlimAdj Preg hp hplim
  let Ac : E → Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun x j ↦ (Ae x j).map Complex.ofReal
  let Bc : E → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun x ↦ (Be x).map Complex.ofReal
  have hAe' (a j k) : ContDiff ℝ ∞ (fun x ↦ Ae x a j k) :=
    (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp
      ((contDiff_pi.mp hAe) a)
  have hBe' (j k) : ContDiff ℝ ∞ (fun x ↦ Be x j k) :=
    (Matrix.entryLinearMap ℝ ℝ j k).toContinuousLinearMap.contDiff.comp hBe
  have hUχ (x) (hx : x ∈ U) : x ∈ tsupport χout :=
    subset_tsupport χout (by
      change χout x ≠ 0
      rw [(hplateau x hx).eq_of_nhds]
      exact one_ne_zero)
  have hκplateau (x) (hx : x ∈ U) := hκout x (hUχ x hx)
  have hV : IsOpen V := C.symm.continuousOn.isOpen_inter_preimage
    C.open_target (hI.prod (hI.prod hZ))
  have hAeq (x) (hx : x ∈ tsupport χout) : Ac x = A x := by
    have hx' : Ae x = coefficient i Q x := (he x hx).1.eq_of_nhds
    change (fun j ↦ (Ae x j).map Complex.ofReal) = _
    rw [hx']
  have hBeq (x) (hx : x ∈ tsupport χout) : Bc x = B₀ x :=
    congrArg (fun M : Mat ↦ M.map Complex.ofReal) (he x hx).2.eq_of_nhds
  have hc := contDiff_conicAlgebraicSymbol ℓ i hQ hD hh hmap r c hXF
    ρ hρ hsρ σ hσ hσX β hβ hβF
  have hsig := contDiff_conicSourceSymbol ℓ ρ hρ hsρ σ hσ
  have hregroup : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      (p.1.1, (p.1.2, (p.2.1, p.2.2)))) :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd))
  have hsmooth₀ := hW₀.comp hregroup
  have hsmooth₁ := hW₁.comp hregroup
  have hinitFlow := flow_initial_of_diagonal_outputs h Φ C hC I hZ hdiff hdiagonal
  have hlead' (x) (hx : x ∈ U) (η) :
      Ac x 0 * W₀ (x 0) (x 0) (spatialPart x) η =
        sig x η • projector i Q h r c x ((ℓ η)⁻¹ • η) := by
    rw [hAeq x (hUχ x hx)]
    exact supported_leading_endpoint ℓ i Q B h Φ C hC r c σ I Z hbox hinitFlow
      hσI κ ρ hinit x (hκplateau x hx).eq_of_nhds η
  have hcomp' (x) (hx : x ∈ U) (ξ) (hξ : β ξ ≠ 0) :
      (∑ j, (ξ j : ℂ) • Ac x j) * bm x ξ =
        1 - projector i Q h r c x ((ℓ (spatialPart ξ))⁻¹ • spatialPart ξ) := by
    rw [hAeq x (hUχ x hx)]
    exact conicBminus_identity_on_common_support ℓ i Q h r c hroot hXF β hβF (hUX hx) ξ hξ
  have hcancel' (x) (hx : x ∈ U) (s) (η) (j) :
      WKB.firstOrderApply (fun y a ↦ (Ac y a).mulVecLin) (fun y ↦ (Bc y).mulVecLin)
        (fun y ↦ Complex.exp (Complex.I * (Ψext (y 0) s (spatialPart y) η : ℂ)) •
          (fun k ↦ (W₀ + W₁) (y 0) s (spatialPart y) η k j)) x =
      Complex.exp (Complex.I * (Ψext (x 0) s (spatialPart x) η : ℂ)) •
        (fun k ↦ twoTimePhysicalApply Ac Bc W₁ (x 0) s (spatialPart x) η k j) := by
    rw [firstOrderApply_eq_of_coefficients Ac A Bc B₀ _ (hAeq x (hUχ x hx)) (hBeq x (hUχ x hx)),
      twoTimePhysicalApply_eq_of_coefficients Ac A Bc B₀ W₁ (hAeq x (hUχ x hx)) (hBeq x (hUχ x hx))]
    exact hcancel x (hκplateau x hx) s η j
  have hzero := buffered_pencil_matrices_lower_buffer i Q B h Φ C hC r c σ a hbuffer
    (V := V) inter_subset_left κ
  have hz₀ (p : T) (hp : p.2.1 ≤ a) : F₀ p = 0 := (hzero _ _ _ _ hp).1
  have hz₁ (p : T) (hp : p.2.1 ≤ a) : F₁ p = 0 := (hzero _ _ _ _ hp).2.1
  have hzero₀ t s y η hs := (supportedConicMatrix_lower_buffer ℓ 0 ρ F₀ Ac Bc a hz₀ t s y η hs).1
  have hzero₁ t s y η hs := (supportedConicMatrix_lower_buffer ℓ 1 ρ F₁ Ac Bc a hz₁ t s y η hs).1
  have hbmask (k : Bool) (τ : ℝ) (hτ : τ ∈ Icc 0 Δ) :
      elapsedAmplitude (directRetardedAmplitudes Ac Bc W₀ W₁ k) χout χsource β τ =
        elapsedAmplitude (b k) χout χsource β τ := by
    exact (elapsedDirectAmplitude_eq_of_coefficients Ac A Bc B₀ W₀ W₁
      χout χsource β hAeq hBeq k τ).trans
        (elapsedDirectAmplitude_eq_of_auxiliary_masks ℓ ρ hV κ A B₀
          (leading i Q B h Φ C r c σ) (correction i Q B h Φ C r c σ)
          χout χsource β τ (hchart τ hτ) hκout hρβ k)
  have hpmask (k : Fin 4) :
      (fun x z ξ ↦ (χout x * χsource z) • directPDOSymbols Ac Bc W₁ bm sig β k x ξ) =
        fun x z ξ ↦ (χout x * χsource z) • sym k x ξ := by
    exact (maskedDirectPDOAmplitude_eq_of_coefficients Ac A Bc B₀ W₁ bm sig
      χout χsource β hAeq hBeq k).trans
        (maskedDirectPDOAmplitude_eq_of_auxiliary_masks ℓ ρ hV κ A B₀
          (correction i Q B h Φ C r c σ) bm σ χout χsource β
          (by simpa only [sub_zero] using hchart 0 ⟨le_rfl, hΔ⟩) hκout hρβ k)
  have hphaseGraph (k : Bool) (τ : ℝ) :
      elapsedGraph Ψext (directRetardedAmplitudes Ac Bc W₀ W₁ k) χout χsource β τ =
        elapsedGraph Ψ (directRetardedAmplitudes Ac Bc W₀ W₁ k) χout χsource β τ := by
    have he := elapsedGraphs_eq_of_supported_phase Ac Bc
      (supportedConicMatrix ℓ 0 ρ F₀) (supportedConicMatrix ℓ 1 ρ F₁)
      (ConicPhase.phase ℓ C) G hGerm χout χsource β τ
    cases k
    · exact he.1
    · exact he.2
  have hgraph (k) (τ) (hτ : τ ∈ Icc 0 Δ) :
      elapsedGraph Ψext (directRetardedAmplitudes Ac Bc W₀ W₁ k) χout χsource β τ =
        elapsedGraph Ψ (b k) χout χsource β τ := by
    rw [hphaseGraph]
    unfold elapsedGraph
    rw [hbmask k τ hτ]
  have hpdo (k) : maskedPhysicalPDO χout χsource (directPDOSymbols Ac Bc W₁ bm sig β k) = P k := by
    unfold maskedPhysicalPDO
    rw [hpmask]
    rfl
  have hregphase (k : Bool) (j : ℕ) (τ : ℝ) :=
    directRetarded_regularizations_eq_of_supported_phase Ac Bc
      (supportedConicMatrix ℓ 0 ρ F₀) (supportedConicMatrix ℓ 1 ρ F₁)
      (ConicPhase.phase ℓ C) G hGerm χout χsource β (θ j) τ k
  dsimp only [Ac, Bc] at hbmask hpmask hgraph hpdo hregphase
  have hres := completeResidual_operators_of_graph_regularizations Ae Be hAe' hBe'
    Ψext W₀ W₁ bm sig (fun x η ↦ projector i Q h r c x ((ℓ η)⁻¹ • η))
    β χout θ a Δ hΔ (contDiff_curried_diagonalPhase hG) hsmooth₀ hsmooth₁ hc hβ ho hθ hθcs
    hU (fun x _ ↦ hsig.continuous.comp (continuous_const.prodMk continuous_id))
    hplateau hdiag hlead' hcomp' hcancel' χsource hs hocs hscs hout hzero₀ hzero₁
  have hresult := hres Treg Cbound
    (by
      intro k j τ hτ u
      rw [(hregphase k j τ).1, hbmask k τ hτ]
      exact ht k j τ hτ u)
    (by
      intro k j τ hτ u
      rw [(hregphase k j τ).2 (fun x ↦ (u.val x).ofLp), hbmask k τ hτ]
      exact htAdj k j τ hτ u)
    htbound
    (by
      intro k τ hτ u
      rw [hgraph k τ hτ]
      exact htlim k τ hτ u)
    (by
      intro k τ hτ u
      rw [hgraph k τ hτ]
      exact htlimAdj k τ hτ u)
    Preg (by simpa only [hpmask] using hp) (by simpa only [hpdo] using hplim)
  obtain ⟨Rgraph, hrbound, hrg, hradj, hSadj, htest, hae⟩ := hresult
  have htestOriginal (f : C2) (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hcφ : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (j : Fin (d + 1)) :
      physicalTestAction (coefficient i Q) (zeroth i B)
        (fun x ↦ ((Rgraph false + (1 / Complex.I) • P 0) f x).ofLp) φ j =
          ∫ x, φ x • ((P 1 + (P 2 + Rgraph true + (1 / Complex.I) • P 3)) f) x j := by
    rw [← physicalTestAction_eq_of_coefficients_on_support Ae (coefficient i Q) Be (zeroth i B)
      _ φ (fun x hx ↦ (he x (hUχ x (hφU hx))).1.eq_of_nhds)
        (fun x hx ↦ (he x (hUχ x (hφU hx))).2.eq_of_nhds)]
    simpa only [hpdo] using htest f φ hφ hcφ hφU j
  refine ⟨Rgraph, hrbound, ?_, ?_, ?_, htestOriginal, ?_, ?_, ?_⟩
  · intro k u
    refine (hrg k u).trans ?_
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact congrArg (fun L : C2 →L[ℂ] C2 ↦ L u) (hgraph k τ hτ)
  · intro k u
    refine (hradj k u).trans ?_
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact congrArg (fun L : C2 →L[ℂ] C2 ↦ L.adjoint u) (hgraph k τ hτ)
  · simpa only [hpdo] using hSadj
  · intro f du hdu
    have heq : physicalWeakApply Ae Be
        (fun x ↦ ((Rgraph false + (1 / Complex.I) • P 0) f x).ofLp) du =ᵐ[volume.restrict U]
        fun x ↦ (((P 1 + (P 2 + Rgraph true + (1 / Complex.I) • P 3)) f) x).ofLp := by
      simpa only [hpdo] using hae f du (by simpa only [hpdo] using hdu)
    filter_upwards [heq, ae_restrict_mem hU.measurableSet] with x hx hxU
    exact (physicalWeakApply_eq_at_coefficients Ae (coefficient i Q) Be (zeroth i B)
      _ du (he x (hUχ x hxU)).1.eq_of_nhds (he x (hUχ x hxU)).2.eq_of_nhds).symm.trans hx

  · exact physicalPair_test_of_coordinate_residual i hΩ Q B hQ hB
      (fun x hx ↦ hχΩ x (hUχ x hx))
      (Rgraph false + (1 / Complex.I) • P 0) (P 1) (P 2) (Rgraph true) (P 3) htestOriginal
  · exact principal_add_residual_defect _ _

end JanetCartan.RegularSector.Characteristic.ResidualCoordinates
