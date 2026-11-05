module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Domains
public import JanetCartan.Iteration.PhysicalInverseContinuity.Row
public import JanetCartan.Iteration.PhysicalInverseContinuity.Image
public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood

/-!
# Original selected finite physical row: strong adjoint neighborhood

Take the same fixed continuum menu, retained flow/label buffers, original
positive scalar at fixed contraction, actual measured carrier actions, original
image arrays, and the fixed exterior. The common physical finite-jet radius is
chosen before the current immersion, chart, or realization. Immersion/rank,
metric and normal gaps, low derivative caps, column membership, original-kernel
continuity and the finite menu intersection are all produced here. The sole
order-one current budget is the actual augmented adjoint regularity estimate,
not a strong adjoint difference assumption. Consumer: the moving-row term of
`app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 6000
open Set Metric Filter MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumNormal ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase
open ContinuumRow CanonicalCarrier CanonicalConic CarrierSobolev CommonMeasurement
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude HamiltonPhase
open ContinuumNormalReduction TransportSymbol AmplitudeBound GeometricProfile
open ProjectedStressFrame

variable {n : ℕ} {ι : Type} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : ι) → PatchQuantitativeFamily (P i) U hU)
    {Ω K : ι → Set (Euclidean n × Euclidean 3)}
    {z₀ : ι → Euclidean 3} {Rc B τ : ι → ℝ} {row col : ι → Fin n}

variable
  (hdomain : ∀ i, ∀ z ∈ (T i).data.localReference.stateDomain, z.1 ∈ U)
  (hgeometry : ∀ i, ∃ (R : ℝ)
    (A : (ℝ × InitialData (Euclidean (n - 1))) ≃L[ℝ]
      (Euclidean n × (ℝ × Euclidean (n - 1)))),
    0 < R ∧ R < (T i).data.localReference.stateRadius ∧
    (∀ Q, ∀ q ∈ ball ((0 : ℝ), (T i).data.adapted.baseData) (3 * (T i).family.sourceRadius),
      ‖(A.symm : _ →L[ℝ] _).comp (fderiv ℝ ((T i).family.flow Q).augmentedProjection q) -
        ContinuousLinearMap.id ℝ _‖ ≤ 1 / 2) ∧
    (∀ Q, ∀ q ∈ ((T i).family.flow Q).time ×ˢ ((T i).family.flow Q).parameters,
      (((T i).family.flow Q).position q, ((T i).family.flow Q).momentum q) ∈
        closedBall (0, (T i).data.center) R) ∧
    (∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T i).family.threshold},
      ∀ z ∈ closedBall (0, (T i).data.center) R,
      ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp z, (T i).data.adapted.normal⟫_ℝ ≠ 0))

include hdomain hgeometry

/-- Actual strong fixed-vector continuity of the entire selected physical
augmented row on an order-eight immersion neighborhood. The reference/current
full-level inputs are exactly the uncut adjoint bounds from the same selected
inverse continuation; in particular they contain no continuity assertion. -/
theorem exists_retained_augmented_adjoint_tolerance
    {c₁ C : ι → ℝ}
    (hP : ∀ i : ι, (P i).IsValid (c₁ i) (C i))
    (hΩ : ∀ i : ι, IsOpen (Ω i))
    (hK : ∀ i : ι, IsCompact (K i))
    (hKΩ : ∀ i : ι, (K i) ⊆ (Ω i))
    (hRc : ∀ i : ι, 0 < (Rc i))
    (hB : ∀ i : ι, 0 ≤ (B i))
    (hτ : ∀ i : ι, 0 < (τ i))
    (hbuffer : ∀ i : ι, MapsTo (coordinates (adaptedCoordinates (T i).data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), (z₀ i))) (Rc i)) (K i))
    (hτeq : ∀ i : ι, (τ i) = existenceTime (Rc i) (liftedLowBound (T i) (B i)) / 4)
    (hKFU : ∀ i : ι, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ U)
    (hKU : ∀ i : ι, (K i) ⊆ CoefficientBounds.inputDomain (T i))
    (hx : ∀ i : ι, MapsTo Prod.fst (K i) (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius))
    {zRoot : ι → Euclidean 3}
    {ηb : ι → Euclidean (n - 1)}
    (hηb : ∀ i : ι, (ηb i) ≠ 0)
    (D : ι → CoefficientNormCharts n)
    (hSflow : ∀ i : ι, MapsTo (densityCoordinates (T i)) (D i).field.region
      (outputCylinder ((0 : Euclidean (n - 1)), (z₀ i)) (Rc i) (τ i)))
    (reference : FlatReference n)
    (c₀ : ∀ i : ι, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), (z₀ i)) (Rc i) (B i) (τ i) (row i) (col i) reference.map)
    {Rwork : ℝ} (hRwork : 0 < Rwork) (hworkChart : Rwork < reference.domain.chartRadius)
    (hUwork : U ⊆ ball 0 Rwork)
    {R : ι → ℝ}
    (hR : ∀ i : ι, 0 < (R i))
    {σ : ℝ} (hσ : 0 < σ)
    {Mc : ι → ℝ} (hMc : ∀ i, 0 < Mc i)
    (hforward₀ : ∀ i, cNorm (Icc (-(τ i)) (τ i) ×ˢ
      closedBall ((0 : Euclidean (n - 1)), z₀ i) (Rc i / 8)) 1 (c₀ i).forward ≤ Mc i)
    (hlabels : ∀ i p, p ∈ (D i).field.region → (densityCoordinates (T i) p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 64))
    (htime : ∀ i p, p ∈ (D i).field.region → |(densityCoordinates (T i) p).1| < R i / (64 * Mc i))
    (hDV : ∀ i : ι, (D i).field.region ⊆ ball (0 : Euclidean n) (T i).family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * (P i).radius / 2)))
    {r rAngular : ι → ℝ}
    (hr : ∀ i : ι, 0 < (r i))
    (hcell : ∀ i : ι, 4 * (r i) < 1 / 2)
    (hrAngular : ∀ i : ι, 0 < (rAngular i))
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (hr i) 1) ×ˢ
      carrierSupport (zRoot i) (r := r i) ⊆ (D i).field.carrier)
    {rCoeff RCoeff : ℝ} (hrCoeff : 0 < rCoeff) (hrR : rCoeff < RCoeff)
    (hRchart : RCoeff < reference.domain.chartRadius)
    (χcoeff : Euclidean n → ℝ)
    (hsCoeff : tsupport χcoeff ⊆ ball 0 rCoeff)
    (hχrange : ∀ x, χcoeff x ∈ Icc (0 : ℝ) 1)
    (coeff₀ : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hcoeff₀ : ∀ j x, coeff₀ j x = χcoeff (centeredTorusRepresentative x) *
      geometricReducedCoefficients reference.map (centeredTorusRepresentative x) j)
    (χ χsrc ψ : C(Torus n, ℝ)) :
    let angular := fun i ↦ angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (hr i)
      (angularWidth_spec (hηb i) (hrAngular i)).1
    let e₀ := fun i ↦ data (T i) (c₀ i).Q reference.map (row i) (col i) (c₀ i).forward
      (c₀ i).inverse (fun _ ↦ σ) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
    let image₀ := imageChannel coeff₀ χ χsrc
    ∀ V₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i w, (V₀ i).adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral (e₀ i) w) →
    let A₀ := augmentedRow image₀ (fun i ↦ restrictCarrier χ (V₀ i)) ψ
    ∀ w : OutputL2 n, A₀.adjoint w ∈ (augmentedInputSobolevScale n ι).level 1 →
    ∀ Braw : ℝ, 0 ≤ Braw → ∀ ε : ℝ, 0 < ε → ∃ δ > 0,
    ∀ (F : Euclidean n → Euclidean (embeddingDimension n)), ContDiff ℝ ∞ F →
      cNorm (closedBall 0 (max ((Rwork + reference.domain.chartRadius) / 2) RCoeff)) 8
        (F - reference.map) < δ →
    ∀ current : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
      (Rc i) (B i) (τ i) (row i) (col i) F,
    (∀ i, cNorm (Icc (-(τ i)) (τ i) ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀ i)
      (Rc i / 8)) 1 (current i).forward ≤ Mc i) →
    ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ a x, c a x = χcoeff (centeredTorusRepresentative x) *
        geometricReducedCoefficients F (centeredTorusRepresentative x) a) →
    let e := fun i ↦ data (T i) (current i).Q F (row i) (col i) (current i).forward
      (current i).inverse (fun _ ↦ σ) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
    ∀ V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i y, (V i).adjoint y =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) y) →
    let A := augmentedRow (imageChannel c χ χsrc) (fun i ↦ restrictCarrier χ (V i)) ψ
    A.adjoint w ∈ (augmentedInputSobolevScale n ι).level 1 →
    (augmentedInputSobolevScale n ι).gradeNorm 1 (A.adjoint w) ≤ Braw →
    ‖(A.adjoint - A₀.adjoint) w‖ ≤ ε := by
  classical
  intro angular e₀ image₀ V₀ hV₀ A₀ w hw₀ Braw hBraw ε hε
  let X := augmentedInputSobolevScale n ι
  let wc := complexMultiplier χ (l2ComplexInclusion volume w)
  let Bslot := max (X.gradeNorm 1 (A₀.adjoint w)) Braw
  have hBslot : 0 ≤ Bslot := hBraw.trans (le_max_right _ _)
  let dcount := 1 + 2 * (Fintype.card ι : ℝ)
  have hcount : 0 < dcount := by dsimp only [dcount]; positivity
  let η := ε / dcount
  have hη : 0 < η := div_pos hε hcount
  let Rbig := (Rwork + reference.domain.chartRadius) / 2
  let Rall := max Rbig RCoeff
  have hworkBig : Rwork < Rbig := by dsimp only [Rbig]; linarith
  have hbigChart : Rbig < reference.domain.chartRadius := by dsimp only [Rbig]; linarith
  obtain ⟨δg, hδg, Cg, _, κg, hκg, hgeo⟩ := CurrentGeometricNeighborhood.exists_geometric_neighborhood
    reference hRwork hworkBig hbigChart (by norm_num : (0 : ℝ) < 1)
  have hUbig : U ⊆ ball 0 Rbig := hUwork.trans (ball_subset_ball hworkBig.le)
  have hsub (i : ι) : closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall 0 Rwork := ((hKFU i).trans hUwork).trans ball_subset_closedBall
  have hnorm (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiff ℝ ∞ F) (i : ι) :
      cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 4 F ≤
      cNorm (closedBall (0 : Euclidean n) Rwork) 4 F :=
    cNorm_mono_set_of_contDiffAt (hsub i) (isCompact_closedBall _ _)
      (fun _ _ ↦ hF.contDiffAt.of_le (by simp))
  have hG := hgeo univ reference.map isOpen_univ (subset_univ _) reference.contDiff.contDiffOn
    (by simpa only [sub_self, cNorm_zero] using hδg)
  have hiRef : IsImmersionOn reference.map U := fun x hx ↦ hG.1 x (hUbig hx)
  have hrankRef : HasFullNormalRankOn reference.map U := fun x hx ↦ hG.2.1 x (hUbig hx)
  have hτRc (i : ι) : τ i ≤ Rc i / 16 := by
    have ht := (existenceTime_le (hRc i) (liftedLowBound_nonneg (T i) (hB i))).1
    rw [hτeq i]
    linarith
  have hdom (i : ι) (F : Euclidean n → Euclidean (embeddingDimension n))
      (c : Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i) (Rc i) (B i) (τ i)
        (row i) (col i) F)
      (hf : cNorm (Icc (-(τ i)) (τ i) ×ˢ closedBall ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i / 8)) 1 c.forward ≤ Mc i) :=
    retained_region_input_and_footpoint (T i) (hRc i) (hτ i) (hτRc i) (hR i) (hMc i)
      (hbuffer i) (D i) (hSflow i) (hlabels i) (htime i) c hf
  have hslot₀ (i : ι) : MemRawSobolev 1 ((V₀ i).adjoint wc) ∧
      rawSobolevNorm 1 ((V₀ i).adjoint wc) ≤ Bslot := by
    have h := raw_complex_slot_of_augmented_adjoint image₀ V₀ χ ψ w 1 hw₀ i
    exact ⟨h.1, h.2.trans ((half_le_self (X.gradeNorm_nonneg 1 (A₀.adjoint w))).trans (le_max_left _ _))⟩
  have hang (i : ι) (z θ) : |angular i z θ| ≤ 1 := by
    rw [abs_of_nonneg (angularMask_mem_Icc (zRoot i) (NormedSpace.normalize (ηb i)) (hr i)
      (angularWidth_spec (hηb i) (hrAngular i)).1 z θ).1]
    exact (angularMask_mem_Icc ..).2
  have hcomp (i : ι) := exists_retained_uncut_adjoint_sub_tolerance (T i) (hdomain i) (hgeometry i)
    (hP i) (hΩ i) (hK i) (hKΩ i) (hRc i) (hB i) (hτ i) (hbuffer i) (hτeq i)
    (hKFU i) (hKU i) (hx i) (D i) (hdom i reference.map (c₀ i) (hforward₀ i)).1
    (hSflow i) (hDV i) (c₀ i) reference.contDiff.contDiffOn hiRef hrankRef
    (M := Cg) (κmet := 1 / 4) (κnormal := κg) (by norm_num) hκg
    ((hnorm _ reference.contDiff i).trans hG.2.2.1)
    (fun x hx ↦ hG.2.2.2.1 x (hUbig (hKFU i hx)))
    (fun x hx ↦ hG.2.2.2.2.1 x (hUbig (hKFU i hx))) (hR i) (fun _ ↦ σ)
    contDiffOn_const (fun _ _ ↦ hσ) (hdom i reference.map (c₀ i) (hforward₀ i)).2
    (hr i) (hcell i) (angular i) (hang i) (angularMask_smooth ..)
    (carrierSupport_compact (zRoot i))
    (fun _ hz θ ↦ angularMask_zero_outside (zRoot i) (NormedSpace.normalize (ηb i)) (hr i)
      (angularWidth_spec (hηb i) (hrAngular i)).1 hz θ) (hsupportD i)
    (V₀ i) (hV₀ i) wc (hslot₀ i).1 hBslot (hslot₀ i).2 hη
  choose δc hδc hcarrier using hcomp
  obtain ⟨δall, hδall, hδi⟩ := Pi.exists_forall_pos_add_lt hδc
  obtain ⟨δI, hδI, himage⟩ := exists_retained_image_adjoint_tolerance reference hrCoeff hrR hRchart
    hsCoeff hχrange coeff₀ hcoeff₀ χ χsrc w hη
  refine ⟨min δg (min δI δall), lt_min hδg (lt_min hδI hδall), ?_⟩
  intro F hF hsmall current hforward c hc e V hV A hw hbudget
  have hjet {E : Set (Euclidean n)} (hE : E ⊆ closedBall 0 Rall) :
      cNorm E 8 (F - reference.map) ≤ cNorm (closedBall 0 Rall) 8 (F - reference.map) :=
    cNorm_mono_set_of_contDiffAt hE (isCompact_closedBall _ _)
      (fun _ _ ↦ (hF.sub reference.contDiff).contDiffAt.of_le (by simp))
  have hnow := hgeo univ F isOpen_univ (subset_univ _) hF.contDiffOn
    ((hjet (closedBall_subset_closedBall (le_max_left _ _))).trans_lt
      (hsmall.trans_le (min_le_left _ _)))
  have him : IsImmersionOn F U := fun x hx ↦ hnow.1 x (hUbig hx)
  have hrank : HasFullNormalRankOn F U := fun x hx ↦ hnow.2.1 x (hUbig hx)
  have hslot (i : ι) : ‖(V i).adjoint wc - (V₀ i).adjoint wc‖ ≤ η := by
    have h := raw_complex_slot_of_augmented_adjoint (imageChannel c χ χsrc) V χ ψ w 1 hw i
    have hb : rawSobolevNorm 1 ((V i).adjoint wc) ≤ Bslot := h.2.trans
      ((half_le_self (X.gradeNorm_nonneg 1 (A.adjoint w))).trans (hbudget.trans (le_max_right _ _)))
    have hclose : cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 8
        (F - reference.map) < δc i := by
      apply (hjet ((hsub i).trans (closedBall_subset_closedBall (hworkBig.le.trans (le_max_left _ _))))).trans_lt
      exact (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))).trans (by simpa only [zero_add] using hδi i)
    exact hcarrier i F (current i) hF.contDiffOn him hrank ((hnorm _ hF i).trans hnow.2.2.1)
      (fun x hx ↦ hnow.2.2.2.1 x (hUbig (hKFU i hx)))
      (fun x hx ↦ hnow.2.2.2.2.1 x (hUbig (hKFU i hx)))
      (hdom i F (current i) (hforward i)).2 hclose (V i) (hV i) h.1 hb
  have hi := himage F hF ((hjet (closedBall_subset_closedBall (le_max_right _ _))).trans_lt
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))) c hc
  have hrow := norm_augmented_restricted_adjoint_sub_le (imageChannel c χ χsrc) image₀ V V₀ χ ψ w
  change ‖A.adjoint w - A₀.adjoint w‖ ≤ ε
  calc
    _ ≤ _ := hrow
    _ ≤ η + 2 * ∑ _i : ι, η := add_le_add hi (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ ↦ hslot i)) (by norm_num))
    _ = η * dcount := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, dcount]; ring
    _ = ε := div_mul_cancel₀ _ hcount.ne'

end JanetCartan.PhysicalInverseContinuity
