module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MatrixRepresentation
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds

/-!
# Actual finite raw family with the retained WKB grades

Apply the corrected-family constructor once and discharge every leading,
correction and working-ball input of the amplitude-grade deduction on those
same witnesses. The constants precede the immersion, scalar, frequency and
history scale. The original derivative reserve is fourteen, with the stated
additional parameter allowance. The raw integrals and their representation
use these same flows and scalar.

This closes the actual coefficient-budget instantiation in
`app:ch_waves:eq:individual-grading`. The original immersion and initial-scalar
profiles are still primitive inputs; their common initialized-history
production and the actual slice normal geometry remain to be instantiated.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open AmplitudeGrades LeadingWave LeadingWave.FullModulation ProjectedStressFrame RawInputPartition

private theorem raw_cNorm_eq_of_eqOn
    {n N : ℕ} {X Q : Set (Euclidean n)} (hX : IsOpen X) (hQ : Q ⊆ X)
    {f g : Euclidean n → Matrix (Fin N) (Fin n) ℂ}
    (hfg : EqOn f g X) (m : ℕ) : cNorm Q m f = cNorm Q m g := by
  unfold cNorm
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Set.image_congr
  intro x hx
  have he : f =ᶠ[𝓝 x] g := by
    filter_upwards [hX.mem_nhds (hQ hx)] with y hy using hfg hy
  rw [(he.iteratedFDeriv (𝕜 := ℝ) (n := k)).eq_of_nhds]

/-- Construct one finite raw family and prove its literal ambient WKB grades,
including the stronger joint profiles needed by the sharp slice estimate and
the physical bound for arbitrary compact Fourier densities and wide Hilbert data.
The geometry, real leading budget, correction budget and both covector grades
are conclusions of the actual producers, on the SAME centers and flows.
Original immersion/scalar profiles are retained as inputs with reserve
`14 + (rpar + 2)`. This is the graded-family component of
`app:ch_waves:thm:individual`, not the initialized-history theorem. -/
theorem exists_finite_actual_graded_raw_family {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M Mᵣ κmet κnormal m : ℝ} (hM : 0 ≤ M) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hm : 0 < m)
    (AF Ar : ℕ → ℝ) (hAF : ∀ k, 0 ≤ AF k) (hAr : ∀ k, 0 ≤ Ar k) :
    ∃ η ε : ℝ, ∃ Γ : ℕ → ℝ,
      0 < η ∧ 0 < ε ∧ (∀ k, 0 < Γ k) ∧
      ∃ centers : Finset (parameterCube P.radius),
      ∃ row col : centers → Fin n, ∃ R σ : centers → ℝ,
        (∀ j, 0 < R j ∧ 0 < σ j) ∧
        ∃ V₀ : Set (Euclidean 3 × Euclidean (n - 1)),
          IsOpen V₀ ∧ (∀ z ∈ parameterCube P.radius, (z, T.reference.spatialPatch z) ∈ V₀) ∧
          (ball (0 : Euclidean n) ε ×ˢ V₀ ⊆
            ⋃ j : centers, closedBall ((0 : Euclidean n),
              (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) ∧
      ∃ C Pξ Pζ : centers → ℕ → ℝ,
        (∀ j k, 0 < C j k) ∧ (∀ j k, 0 < Pξ j k) ∧ (∀ j k, 0 < Pζ j k) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ j : centers,
        let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
          (0, (j.1.1, T.reference.spatialPatch j.1.1))
        ∃ Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
          IsOpen Ω ∧ closedBall a (2 * σ j) ⊆ Ω ∧
          (∀ w ∈ Ω, w.1 ∈ U) ∧ Ω ⊆ domain T ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), j.1.1) (R j / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8)) 14 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), j.1.1) (R j / 8), m ≤ r p) →
          ContDiffOn ℝ ∞ (scalarAmplitude T Q F (row j) (col j) Φ Y r) Ω ∧
          (∀ w ∈ Ω, nullvector T Q (col j) w ≠ 0 ∧ conullvector T Q (row j) w ≠ 0) ∧
          (∀ w ∈ Ω, conullvector T Q (row j) w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ fullLeadingCovector T Q F (row j) (col j) Φ Y r (x, w.2)) w.1 = 0) ∧
          (∀ τ, ContDiffOn ℝ ∞
            (fun w ↦ fullPrimaryAtom T Q F (row j) (col j) Φ Y τ r w.2.1 (w.1, w.2.2)) Ω) ∧
          (∀ k, cNorm (closedBall a (σ j)) k
            (fullCorrectionCovector T Q F (row j) (col j) Φ Y r) ≤
              Γ k * (1 + cNorm K (k + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8)) (k + 14) r)) ∧
          (∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
            14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
            HasDerivativeProfile K F RF L AF →
            HasDerivativeProfile
              (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8)) r Rr L Ar →
            ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
            (let J := closedBall a (σ j)
            let D := fullDisplacementAmplitude T Q F (row j) (col j) Φ Y r τ
            let A := fullDerivativeAmplitude T Q F (row j) (col j) Φ Y r τ
            let R := fun w ↦ A w - fullLeadingPrincipalMatrix T Q F (row j) (col j) Φ Y r w
            let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
              phaseGradient T Q w.1 w.2.2
            let ζ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
              fderiv ℝ (phase T Q w.1) w.2.2
            ContDiffOn ℝ ∞ D (ball a (2 * σ j)) ∧ ContDiffOn ℝ ∞ A (ball a (2 * σ j)) ∧
            (∀ k, ∀ w ∈ J,
              ‖iteratedFDeriv ℝ k D w‖ ≤ τ * C j k * L ^ (k - (rpar + 1)) ∧
              ‖iteratedFDeriv ℝ k A w‖ ≤ C j k * L ^ (k - rpar) ∧
              ‖iteratedFDeriv ℝ k R w‖ ≤ τ * C j k * L ^ (k - rpar)) ∧
            (∀ s k : ℕ, k ≤ rpar → ∀ w ∈ J,
              ‖iteratedFDeriv ℝ (s + k) D w‖ ≤ τ * C j (s + k) * L ^ s ∧
              ‖iteratedFDeriv ℝ (s + k) A w‖ ≤ C j (s + k) * L ^ s ∧
              ‖iteratedFDeriv ℝ (s + k) R w‖ ≤ τ * C j (s + k) * L ^ s) ∧
            (∀ s : ℕ, ∀ w ∈ J,
              ‖iteratedFDeriv ℝ s (fun x ↦ D (x, w.2)) w.1‖ ≤ τ * C j s * L ^ s ∧
              ‖iteratedFDeriv ℝ s (fun x ↦ A (x, w.2)) w.1‖ ≤ C j s * L ^ s ∧
              ‖iteratedFDeriv ℝ s (fun x ↦ R (x, w.2)) w.1‖ ≤ τ * C j s * L ^ s) ∧
            HasDerivativeProfile J D (rpar + 1) L (fun k ↦ τ * ∑ i ∈ Finset.range (k + 1), C j i) ∧
            HasDerivativeProfile J A rpar L (fun k ↦ ∑ i ∈ Finset.range (k + 1), C j i) ∧
            HasDerivativeProfile J R rpar L (fun k ↦ τ * ∑ i ∈ Finset.range (k + 1), C j i) ∧
            HasDerivativeProfile J ξ (rpar + 3) L (Pξ j) ∧
            (∀ k, ∀ w ∈ J, ‖iteratedFDeriv ℝ k ζ w‖ ≤ Pζ j k * L ^ (k - 1 - (rpar + 2))) ∧
            (∀ s k : ℕ, 1 ≤ s → k ≤ rpar → ∀ w ∈ J,
              ‖iteratedFDeriv ℝ (s + k) ξ w‖ ≤ Pξ j (s + k) * L ^ (s - 1) ∧
              ‖iteratedFDeriv ℝ (s + k) ζ w‖ ≤ Pζ j (s + k) * L ^ (s - 1)) ∧
            (∀ s : ℕ, 1 ≤ s → ∀ w ∈ J,
              ‖iteratedFDeriv ℝ s (fun x ↦ fderiv ℝ (phase T Q x) w.2.2) w.1‖ ≤
                Pζ j s * L ^ (s - 1))) ∧
            ∀ (X Qx : Set (Euclidean n)) (V : Set (Euclidean (n - 1))) (z : Euclidean 3),
              IsOpen X → IsOpen V → Qx ⊆ X → T.reference.spatialPatch z ∈ V →
              (∀ p ∈ X ×ˢ V, (p.1, (z, p.2)) ∈ closedBall a (σ j)) →
              (∀ (c Kf : ℝ), 0 ≤ c → 1 ≤ Kf →
                (∀ η ∈ closedBall 0 (c * Kf), ∀ t ∈ Icc (0 : ℝ) 1,
                  T.reference.spatialPatch z + (t * τ) • η ∈ V) →
                ∀ (f : Euclidean (n - 1) → ℂ), Integrable f →
                (∀ᵐ η ∂volume, η ∉ closedBall 0 (c * Kf) → f η = 0) →
                ∀ q : ℕ, cNorm Qx q
                  (rawPrimaryDemodulatedIntegral (fun x ξ ↦ phase T Q x ξ)
                    (fun x ξ ↦ fullDerivativeAmplitude T Q F (row j) (col j) Φ Y r τ (x, (z, ξ)))
                    (T.reference.spatialPatch z) τ volume f) ≤
                  rawPhysicalConstant c (C j) (Pζ j) q * (Kf + L) ^ q * ∫ η, ‖f η‖) ∧
              (∀ Kf : ℝ, 1 ≤ Kf →
                (∀ η ∈ closedBall 0 (4 * Kf), ∀ t ∈ Icc (0 : ℝ) 1,
                  T.reference.spatialPatch z + (t * τ) • η ∈ V) →
                ∀ (d : Euclidean (n - 1) → ℂ) (Md : ℝ),
                  Measurable d → 0 ≤ Md → (∀ η, ‖d η‖ ≤ Md) →
                ∀ (v : WideInput n (cutoffCount Kf)),
                  (∀ x ∈ X,
                    Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) •
                      AmplitudeGrades.Polynomial.differentialMatrix n (embeddingDimension n)
                        (fderiv ℝ (fullPrimaryWave T Q F (row j) (col j) Φ Y τ r z d v) x) =
                      rawPrimaryDemodulatedIntegral (fun x ξ ↦ phase T Q x ξ)
                        (fun x ξ ↦ fullDerivativeAmplitude T Q F (row j) (col j) Φ Y r τ (x, (z, ξ)))
                        (T.reference.spatialPatch z) τ volume (weightedWideDensity d v) x) ∧
                  ∀ q : ℕ, cNorm Qx q (fun x ↦
                    Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) •
                      AmplitudeGrades.Polynomial.differentialMatrix n (embeddingDimension n)
                        (fderiv ℝ (fullPrimaryWave T Q F (row j) (col j) Φ Y τ r z d v) x)) ≤
                    (rawPhysicalConstant 4 (C j) (Pζ j) q *
                      (refinedFourierConstant n Md * 4 ^ ((n : ℝ) / 2))) *
                      (Kf + L) ^ q * Kf ^ ((n : ℝ) / 2) * ‖v‖)) ∧
          ∀ (J : ℕ) (τ : ℝ) (z : Euclidean 3)
            (X : Set (Euclidean n)) (V : Set (Euclidean (n - 1))),
            IsOpen X → IsOpen V → closedBall 0 ((2 : ℝ) ^ J) ⊆ V →
            (∀ p ∈ X ×ˢ V, (p.1, (z, T.reference.spatialPatch z + τ • p.2)) ∈
              closedBall a (2 * σ j)) →
            ∀ (d : Euclidean (n - 1) → ℂ) (Md : ℝ),
              Measurable d → 0 ≤ Md → (∀ ξ, ‖d ξ‖ ≤ Md) →
              ∀ v : WideInput n J,
                ContDiffOn ℝ ∞ (fullPrimaryWave T Q F (row j) (col j) Φ Y τ r z d v) X ∧
                (τ ≠ 0 → ∀ x ∈ X, ∀ e : Euclidean n,
                  Complex.exp (-Complex.I * (T.carrier Q x z / τ : ℝ)) •
                      fderiv ℝ (fullPrimaryWave T Q F (row j) (col j) Φ Y τ r z d v) x e =
                    rawPrimaryDemodulatedIntegral (fun y ξ ↦ phase T Q y ξ)
                      (fun y ξ ↦ waveFirstAmplitude τ⁻¹ (fun t ↦ phase T Q t ξ)
                        (fun t ↦ fullDisplacementAmplitude T Q F (row j) (col j) Φ Y r τ
                          (t, (z, ξ))) y e)
                      (T.reference.spatialPatch z) τ volume (weightedWideDensity d v) x) := by
  obtain ⟨η, ε, c, E, Γ, hη, hε, _hc, hE, hΓ, centers, row, col, ρ, R, τ, Rc, τc, Mc,
    rcomp, δcomp, σ, d, δ, A, H, B, hpos, hstatic, V₀, hV₀, hgraph, hcover, hfamily⟩ :=
    exists_finite_actual_corrected_family hn hP T hK hKU hball hM hMᵣ hκmet hκnormal hm
  classical
  have hbud (j : centers) := by
    obtain ⟨_, _, _, _, hphase, hspace, _, _, hsmall⟩ := hstatic j
    have hσ : 0 < σ j := (hpos j).2.2.2.2.2.2.2.2.1
    have hρ : 0 < ρ j := (hpos j).1
    have hsmall' := hsmall.trans (closedBall_subset_closedBall (show ρ j ≤ 2 * ρ j by linarith))
    obtain ⟨hx, hp⟩ := correctedFamily_workingBall_geometry T
      ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) hσ hsmall' hphase hspace
    exact exists_fullAmplitude_grades_of_corrected_family_outputs
      (N := embeddingDimension n) T
      ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) hσ hK hKU hball hx hp
      (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8))
      hκmet hκnormal AF Ar E Γ hAF hAr hE hΓ
  choose C Pξ Pζ hC hPξ hPζ hgrades using hbud
  refine ⟨η, ε, Γ, hη, hε, hΓ, centers, row, col, R, σ, ?_, V₀, hV₀,
    hgraph, hcover, C, Pξ, Pζ, hC, hPξ, hPζ, ?_⟩
  · intro j
    exact ⟨(hpos j).2.1, (hpos j).2.2.2.2.2.2.2.2.1⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, hfamilyF⟩ := hfamily F hF hi hrank hFM hmet hnormal hclose
  refine ⟨hlow, ?_⟩
  dsimp only
  intro j
  obtain ⟨hdom, hx, _hden, _hminor, Dc, φ, y, _hDc, _hcoverc, _hbigc, _hφDc, _hyL, _hφ₀,
    _hyφ, _hφy, _hvelocityc, _hφbuffer, _hflowcLow, D, Φ, Y, hD, _hcoverD, _hbig,
    hphys, hballD, _hphaseInitial, _hΦ, _hY, _hΦD, _hYL, _hΦ₀, _hYΦ, _hΦY, _hΦz,
    _hYz, _hvelocity, _hΦbuffer, _hYbuffer, _hflow, _hgaps, _hcoeff, _hcompat, hsolution⟩ :=
      hfamilyF j
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let coord := coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)
  let Ω := coord ⁻¹' D
  have hΩ : IsOpen Ω := hD.preimage coord.continuous
  have hspace : ∀ w ∈ Ω, w.1 ∈ U :=
    fun w hw ↦ hKU (interior_subset (hx (ball_subset_closedBall (hphys hw))).2.2)
  have hphase : Ω ⊆ domain T := fun _ hw ↦ hdom (ball_subset_closedBall (hphys hw))
  refine ⟨Ω, Φ, Y, hΩ, hballD, hspace, hphase, ?_⟩
  intro r hr hrM hrmin
  obtain ⟨hα, hb₀, _hinit, hpositive, _hpde, _hsymbol, hreduce, _habound, _hidentity,
    _hαLow, _hαJ, hjoint, hcorr, _hcancel, _hresidual, hbound, _hgrades⟩ :=
      hsolution r hr hrM hrmin
  have hnonzero : ∀ w ∈ Ω, nullvector T Q (col j) w ≠ 0 ∧
      conullvector T Q (row j) w ≠ 0 :=
    fun w hw ↦ ⟨(hpositive w hw).2.2.1, (hpositive w hw).2.2.2.1⟩
  refine ⟨hα, hnonzero, hreduce, fun t ↦ contDiffOn_fullPrimaryAtom_of_leading_outputs
    T Q F (row j) (col j) Φ Y r t hΩ hspace (fun _ hw ↦ hphase hw)
      hF hi hrank hα hnonzero, hbound, ?_, ?_⟩
  · intro RF Rr rpar L hL hRF hRr hpF hpr t ht ht1
    have hg := hgrades j F hF hi hrank hmet hnormal hlow (row j) (col j) Φ Y r Ω
      hΩ hballD hb₀ hcorr hjoint hbound RF Rr rpar L hL hRF hRr hpF hpr t ht ht1
    refine ⟨hg, ?_⟩
    obtain ⟨_hD, hA, _hjoint, _hmixed, hphysical, _hpD, _hpA, _hpR, _hpξ,
      _hjζ, _hmζ, hxζ⟩ := hg
    intro X Qx V z hX hV hQx hζ hproduct
    have hσ : 0 < σ j := (hpos j).2.2.2.2.2.2.2.2.1
    have hsmall : closedBall ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (σ j) ⊆
        ball ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (2 * σ j) :=
      closedBall_subset_ball (by linarith)
    have hmap : ContDiffOn ℝ ∞
        (fun p : Euclidean n × Euclidean (n - 1) ↦ (p.1, (z, p.2))) (X ×ˢ V) :=
      contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd)
    have hS : ContDiffOn ℝ ∞ (Function.uncurry (fun x ξ ↦ phase T Q x ξ)) (X ×ˢ V) :=
      (contDiffOn_fullPhase T Q (fun _ hw ↦ hphase hw)).comp
        hmap
        (fun p hp ↦ hballD (ball_subset_closedBall (hsmall (hproduct p hp))))
    have hA' : ContDiffOn ℝ ∞ (Function.uncurry
        (fun x ξ ↦ fullDerivativeAmplitude T Q F (row j) (col j) Φ Y r t (x, (z, ξ))))
        (X ×ˢ V) :=
      hA.comp hmap
        (fun p hp ↦ hsmall (hproduct p hp))
    constructor
    · intro c Kf hc hKf hsegment f hf hfT q
      let : IsFiniteMeasure (volume.restrict (closedBall (0 : Euclidean (n - 1)) (c * Kf))) :=
        isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_lt_top.ne
      exact cNorm_rawPrimaryDemodulatedIntegral_le hX hV hQx hS hA' (ne_of_gt ht) hζ
        hc hKf hL hsegment hf hfT (fun k _ ↦ (hC j k).le)
        (fun k _ _ ↦ (hPζ j k).le)
        (fun k _ x hx ξ hξ ↦ (hphysical k (x, (z, ξ)) (hproduct (x, ξ) ⟨hx, hξ⟩)).2.1)
        (fun k hk _ x hx ξ hξ ↦ hxζ k hk (x, (z, ξ)) (hproduct (x, ξ) ⟨hx, hξ⟩))
    · intro Kf hKf hsegment d Md hd hMd hdb v
      have hsmallΩ : ball ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (2 * σ j) ⊆ Ω :=
        ball_subset_closedBall.trans hballD
      have hshiftCeil : ∀ η ∈ closedBall 0 ((2 : ℝ) ^ cutoffCount Kf),
          T.reference.spatialPatch z + t • η ∈ V := by
        intro η hη
        simpa using hsegment η (closedBall_subset_closedBall (cutoffCount_ceiling hKf) hη)
          1 (by simp)
      have heq := fun x (hx : x ∈ X) ↦ fullPrimaryWave_differentialMatrix_representation
        T Q F (row j) (col j) Φ Y r isOpen_ball
        (fun w hw ↦ hspace w (hsmallΩ hw)) (fun _ hw ↦ hphase (hsmallΩ hw))
        hF hi hrank (hα.mono hsmallΩ) (fun w hw ↦ hnonzero w (hsmallΩ hw))
        (ne_of_gt ht) hA z hX hV hζ (fun p hp ↦ hsmall (hproduct p hp))
        hshiftCeil hd hMd hdb v hx
      refine ⟨heq, ?_⟩
      intro q
      rw [raw_cNorm_eq_of_eqOn hX hQx heq q]
      exact cNorm_rawPrimaryDemodulatedIntegral_weightedWideDensity_le (by omega : 1 ≤ n)
        hX hV hQx hS hA' (ne_of_gt ht) hζ hKf hL hsegment hd hMd hdb v
        (fun k _ ↦ (hC j k).le) (fun k _ _ ↦ (hPζ j k).le)
        (fun k _ x hx ξ hξ ↦ (hphysical k (x, (z, ξ)) (hproduct (x, ξ) ⟨hx, hξ⟩)).2.1)
        (fun k hk _ x hx ξ hξ ↦ hxζ k hk (x, (z, ξ)) (hproduct (x, ξ) ⟨hx, hξ⟩))
  intro J t z X V hX hV hceil hshift d Md hd hMd hdb v
  have hshiftΩ : ∀ p ∈ X ×ˢ V,
      (p.1, (z, T.reference.spatialPatch z + t • p.2)) ∈ Ω :=
    fun p hp ↦ hballD (hshift p hp)
  refine ⟨contDiffOn_fullPrimaryWave T Q F (row j) (col j) Φ Y r
    hΩ hspace (fun _ hw ↦ hphase hw) hF hi hrank hα hnonzero
      t z hshiftΩ hX hV hceil hd hMd hdb v, ?_⟩
  intro ht x hx e
  exact fullPrimaryWave_derivative_representation T Q F (row j) (col j) Φ Y r
    hΩ hspace (fun _ hw ↦ hphase hw) hF hi hrank hα hnonzero
      t z hshiftΩ hX hV hceil hd hMd hdb ht v hx e

end JanetCartan.RawPrimary
