module

public import JanetCartan.Iteration.PhysicalInverseContinuity.Finite
public import JanetCartan.Iteration.PhysicalInverseContinuity.Reserve
public import JanetCartan.Iteration.PhysicalNormalInverse.PrescribedSource

/-!
# Fixed-contraction prescribed-source strong adjoint from actual regularity

This uses the same static source parameters as the prescribed history
coercivity producer, with only the subset needed for the adjoint action. The
original prescribed positive scalar, all cutoffs, and the unperturbed reference
row are unchanged. The order-one raw tail budget is **derived** from the
native current augmented adjoint estimate and the actual retained coefficient
profile on its two original balls. The physical jet order is fixed at
`1 + canonicalCarrierLowOrder n`, independent of the requested accuracy.
Consumer: `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
open Set Metric Filter MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInverseContinuity
open ContinuumNormal
open ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection NormalizedCarrierProfiles
open CarrierVariation.FamilyInputs PositiveReference PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude HamiltonPhase RetainedRowGeometry
open NormalizedBackground.SourceGeometry
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open Pseudodifferential AmplitudeBound PeriodicLocalL2 RetainedFrozen
open LeadingWave LeadingWave.JointReconstruction AmbientResponse GeometricProfile
open ProjectedStressFrame WideDensity ImageGeometry ImageGeometry.Periodization

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

open CarrierSobolev ContinuumCommutator CommonMeasurement

include hdomain hgeometry

/-- The same prescribed positive source contracts to a finite physical
jet neighborhood for its full measured row adjoint, with order-one tail
control obtained from the current inverse's true full adjoint estimate. -/
theorem exists_prescribed_source_adjoint_tolerance
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
    (hΩpatch : ∀ i, Ω i ⊆ (U ∩ ball (0 : Euclidean n) (T i).physicalRadius) ×ˢ
      parameterInterior (3 * (P i).radius / 2))
    (hx : ∀ i : ι, MapsTo Prod.fst (K i) (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius))
    {zRoot : ι → Euclidean 3}
    {ηb : ι → Euclidean (n - 1)}
    {rOuter aOuter : ι → ℝ}
    (hηb : ∀ i : ι, (ηb i) ≠ 0)
    (D : ι → CoefficientNormCharts n)
    (H : FlatReference n) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1)
    (cSource : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
      (Rc i) (B i) (τ i) (row i) (col i) (sourceDilation H.map σ))
    {Rwork : ℝ} (hRwork : 0 < Rwork) (hworkChart : Rwork < H.domain.chartRadius)
    (hUwork : U ⊆ ball 0 Rwork)
    {R : ι → ℝ}
    (hR : ∀ i : ι, 0 < (R i))
    {Mc : ι → ℝ} (hMc : ∀ i, 0 < Mc i)
    (hforward : ∀ i (F : Euclidean n → Euclidean (embeddingDimension n))
      (current : Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
        (Rc i) (B i) (τ i) (row i) (col i) F),
      cNorm (Icc (-(τ i)) (τ i) ×ˢ
        closedBall ((0 : Euclidean (n - 1)), z₀ i) (Rc i / 8)) 1 current.forward ≤ Mc i)
    {r rAngular : ι → ℝ}
    (hr : ∀ i : ι, 0 < (r i))
    (hcell : ∀ i : ι, 4 * (r i) < 1 / 2)
    (hrAngular : ∀ i : ι, 0 < (rAngular i))
    {Rphysical : ι → ℝ} {V : ι → Set CarrierParameter}
    (hVP : ∀ i, V i ⊆ parameter ⁻¹' parameterInterior (3 * (P i).radius / 2))
    (hRtime : ∀ i, Rphysical i ≤ R i / (64 * Mc i))

    (hflow : ∀ i, MapsTo (densityCoordinates (T i)) (ball (0 : Euclidean n) (Rphysical i) ×ˢ V i)
      (outputCylinder ((0 : Euclidean (n - 1)), z₀ i) (Rc i) (τ i)))
    (hlabelProduct : ∀ i p, p ∈ ball (0 : Euclidean n) (Rphysical i) ×ˢ V i →
      (densityCoordinates (T i) p).2 ∈ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 64))
    (haR : ∀ i, 6 * aOuter i < (T i).family.radius)
    (hDregion : ∀ i, (D i).field.region ⊆
      (ball (0 : Euclidean n) (Rphysical i) ×ˢ V i) ∩
        coefficientDomain (zRoot i) (rOuter i) (6 * aOuter i))
    (hsupportD : ∀ i, tsupport (FixedCutoffs.physical (n := n) (hr i) 1) ×ˢ
      carrierSupport (zRoot i) (r := r i) ⊆ (D i).field.carrier)
    {μ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2)
    {rInner : ℝ} (hrInner : 0 < rInner) (hInnerCell : rInner < 1 / 2)
    (hRchart : 6 * μ < H.domain.chartRadius)
    (χcoeff : Euclidean n → ℝ)
    (hsCoeff : tsupport χcoeff ⊆ ball 0 (5 * μ))
    (hχrange : ∀ x, χcoeff x ∈ Icc (0 : ℝ) 1)
    (coeff₀ : ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hcoeff₀ : ∀ j x, coeff₀ j x = χcoeff (centeredTorusRepresentative x) *
      geometricReducedCoefficients (sourceDilation H.map σ) (centeredTorusRepresentative x) j)
    :
    let χ := FixedCutoffs.periodic (n := n) hμ hμcell 1
    let χsrc := FixedCutoffs.periodic (n := n) hμ hμcell 2
    let ψ := innerCutoff (n := n) hrInner hInnerCell
    let angular := fun i ↦ angularMask (zRoot i) (NormedSpace.normalize (ηb i)) (hr i)
      (angularWidth_spec (hηb i) (hrAngular i)).1
    let F₀ := sourceDilation H.map σ
    let Kbig := closedBall (0 : Euclidean n) (max ((Rwork + H.domain.chartRadius) / 2) (6 * μ))
    let J := 1 + canonicalCarrierLowOrder n
    let Kin := fun i ↦ closedBall ((0 : Euclidean (n - 1)), z₀ i) (R i / 8)
    let initial := fun (_ : ι) (_ : Euclidean (n - 1) × Euclidean 3) ↦ σ
    let e₀ := fun i ↦ data (T i) (cSource i).Q F₀ (row i) (col i) (cSource i).forward
      (cSource i).inverse (initial i) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
    let image₀ := imageChannel coeff₀ χ χsrc
    ∀ V₀ : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i y, (V₀ i).adjoint y =ᵐ[carrierMeasure n] carrierAdjointIntegral (e₀ i) y) →
    let A₀ := augmentedRow image₀ (fun i ↦ restrictCarrier χ (V₀ i)) ψ
    let S := periodicSobolevScale n (Euclidean n)
    let X := augmentedInputSobolevScale n ι
    ∀ w : OutputL2 n, w ∈ S.level 1 → A₀.adjoint w ∈ X.level 1 →
    ∀ Cadj : ℝ, 0 ≤ Cadj → ∀ ε : ℝ, 0 < ε → ∃ δ > 0,
    ∀ (F : Euclidean n → Euclidean (embeddingDimension n)), ContDiff ℝ ∞ F →
      cNorm Kbig J (F - F₀) < δ →
    ∀ current : ∀ i, Chart (T i) (Ω i) (K i) ((0 : Euclidean (n - 1)), z₀ i)
      (Rc i) (B i) (τ i) (row i) (col i) F,
    ∀ c : ReducedCoefficientIndex n → C(Torus n, ℝ),
      (∀ a x, c a x = χcoeff (centeredTorusRepresentative x) *
        geometricReducedCoefficients F (centeredTorusRepresentative x) a) →
    let e := fun i ↦ data (T i) (current i).Q F (row i) (col i) (current i).forward
      (current i).inverse (initial i) (hr i) (hcell i) (angular i) FixedCutoffs.highFrequency
    ∀ Vop : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ i y, (Vop i).adjoint y =ᵐ[carrierMeasure n] carrierAdjointIntegral (e i) y) →
    let A := augmentedRow (imageChannel c χ χsrc) (fun i ↦ restrictCarrier χ (Vop i)) ψ
    ∀ bRadius : ℝ, bRadius ≤ Rwork →
    (∀ y : OutputL2 n, y ∈ S.level 1 → A.adjoint y ∈ X.level 1 ∧
      X.gradeNorm 1 (A.adjoint y) ≤ Cadj * (S.gradeNorm 1 y +
        (1 + retainedCoefficientProfile (closedBall 0 bRadius) (closedBall 0 (6 * μ))
          Kin F initial J) * ‖y‖)) → ‖(A.adjoint - A₀.adjoint) w‖ ≤ ε := by
  classical
  intro χ χsrc ψ angular F₀ Kbig J Kin initial e₀ image₀ V₀ hV₀ A₀ S X w hw hw₀ Cadj hCadj ε hε
  let reference := sourceDilationReference H hσ hσone
  have hKU (i : ι) : K i ⊆ CoefficientBounds.inputDomain (T i) := by
    intro p hp
    obtain ⟨hx, hz⟩ := hΩpatch i (hKΩ i hp)
    exact ⟨hx, fun j ↦ (hz j).trans_le (by linarith only [(hP i).1])⟩
  have hD (i : ι) : (D i).field.region ⊆
      ball (0 : Euclidean n) (Rphysical i) ×ˢ V i :=
    (hDregion i).trans inter_subset_left
  have hDouter (i : ι) : (D i).field.region ⊆
      coefficientDomain (zRoot i) (rOuter i) (6 * aOuter i) :=
    (hDregion i).trans inter_subset_right
  have hcyl (i : ι) := (hflow i).mono_left (hD i)
  have hlabels (i : ι) (p) (hp : p ∈ (D i).field.region) :=
    hlabelProduct i p (hD i hp)
  have htime (i : ι) (p : Euclidean n × CarrierParameter)
      (hp : p ∈ (D i).field.region) :
      |(densityCoordinates (T i) p).1| < R i / (64 * Mc i) := by
    have ht := abs_real_inner_le_norm (T i).data.adapted.normal p.1
    rw [(T i).data.adapted.normal_unit, one_mul] at ht
    change |(adaptedCoordinates (T i).data.adapted p.1).1| < R i / (64 * Mc i)
    rw [adaptedCoordinates_apply]
    exact (ht.trans_lt (mem_ball_zero_iff.mp (hD i hp).1)).trans_le (hRtime i)
  have hDV (i : ι) : (D i).field.region ⊆
      ball (0 : Euclidean n) (T i).family.radius ×ˢ
        (parameter ⁻¹' parameterInterior (3 * (P i).radius / 2)) := by
    intro p hp
    exact ⟨ball_subset_ball (haR i).le (hDouter i hp).1, hVP i (hD i hp).2⟩
  let Bcoef := 2 * (1 + cNorm Kbig J F₀) + ∑ i, cNorm (Kin i) J (initial i)
  have hBcoef : 0 ≤ Bcoef := add_nonneg (mul_nonneg (by norm_num) (add_nonneg zero_le_one
    (cNorm_nonneg ..))) (Finset.sum_nonneg (fun _ _ ↦ cNorm_nonneg ..))
  let Braw := Cadj * (S.gradeNorm 1 w + (1 + Bcoef) * ‖w‖)
  have hBraw : 0 ≤ Braw := mul_nonneg hCadj (add_nonneg (S.gradeNorm_nonneg ..)
    (mul_nonneg (add_nonneg zero_le_one hBcoef) (norm_nonneg _)))
  have hstrong := exists_retained_augmented_adjoint_tolerance T hdomain hgeometry hP hΩ hK hKΩ
    hRc hB hτ hbuffer hτeq hKFU hKU hx hηb D hcyl reference cSource hRwork hworkChart hUwork
    hR hσ hMc (fun i ↦ hforward i _ (cSource i)) hlabels htime hDV hr hcell hrAngular
    hsupportD (rCoeff := 5 * μ) (RCoeff := 6 * μ) (by positivity) (by linarith only [hμ])
    hRchart χcoeff hsCoeff hχrange coeff₀ hcoeff₀ χ χsrc ψ
  obtain ⟨δ, hδ, hclose⟩ := hstrong V₀ hV₀ w hw₀ Braw hBraw ε hε
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro F hF hsmall current c hc e Vop hV A bRadius hb hreg
  have h8 : 8 ≤ J := by dsimp only [J, canonicalCarrierLowOrder]; omega
  have hnear₈ : cNorm Kbig 8 (F - F₀) < δ :=
    (cNorm_mono_order h8).trans_lt (hsmall.trans_le (min_le_right _ _))
  have hnear : cNorm Kbig J (F - F₀) ≤ 1 := (hsmall.trans_le (min_le_left _ _)).le
  have hworkBig : Rwork ≤ (Rwork + H.domain.chartRadius) / 2 := by linarith
  have hbset : closedBall (0 : Euclidean n) bRadius ⊆ Kbig :=
    closedBall_subset_closedBall ((hb.trans hworkBig).trans (le_max_left _ _))
  have hμset : closedBall (0 : Euclidean n) (6 * μ) ⊆ Kbig := closedBall_subset_closedBall (le_max_right _ _)
  have hprof : retainedCoefficientProfile (closedBall 0 bRadius) (closedBall 0 (6 * μ))
      Kin F initial J ≤ Bcoef := retainedCoefficientProfile_le_of_physical_jet_near
    (isCompact_closedBall _ _) hbset hμset Kin initial hF reference.contDiff le_rfl hnear
  obtain ⟨hwm, hwBound⟩ := hreg w hw
  have hcap : X.gradeNorm 1 (A.adjoint w) ≤ Braw := hwBound.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (add_le_add le_rfl hprof) (norm_nonneg w))) hCadj)
  exact hclose F hF hnear₈ current (fun i ↦ hforward i F (current i)) c hc Vop hV hwm hcap

end JanetCartan.PhysicalInverseContinuity
