module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.FamilyInputs.Denominator
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.MinorBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.JointDomains
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.JointReconstruction

/-!
# Quantitative correction inputs on the actual local leading wave

Retain the denominator and scalar working-set inclusion from the actual
construction. The smaller ball is chosen before the immersion and initial datum,
after applying `RawPrimary.exists_fullPhase_minor_neighborhood` to the same
selected row and column. The actual scalar has a fixed `C¹` budget and its
reserve-thirteen bound on that ball. All original leading identities and carrier
compatibility are retained for the parent's correction assembly
(`app:ch_waves:thm:leading`, `app:ch_waves:eq:primary-algebraic-correction`,
`app:ch_waves:eq:WKB-grading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open ProjectedStressFrame AmbientResponse ResponseTransfer CarrierCompatibility

/-- The complete local leading construction on independent full modulation
parameters, retaining the original carrier restriction, both positive gaps,
exact half-strain, both complex quadratures, and the joint reserve-fourteen
estimate (`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`).
The denominator and selected-minor gaps, scalar working-set containment,
and scalar estimates are retained for the finite correction-family assembly. -/
theorem exists_actual_joint_leading_wave_with_correction_inputs {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M Mᵣ κmet κnormal m : ℝ} (hM : 0 ≤ M) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hm : 0 < m)
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterCube P.radius) :
    ∃ row col : Fin n, ∃ ρ R η τ g b cν Rc τc Mc rcomp δcomp σ d δ : ℝ, ∃ A H B E : ℕ → ℝ,
      0 < ρ ∧ 0 < R ∧ 0 < η ∧ 0 < τ ∧ 0 < g ∧ 0 < b ∧ 0 < cν ∧
      0 < Rc ∧ 0 < τc ∧ 0 < Mc ∧ 0 < rcomp ∧ 0 < δcomp ∧ 0 < σ ∧ 0 < d ∧ 0 < δ ∧
      (∀ j, 0 < A j) ∧ (∀ j, 0 < H j) ∧ (∀ j, 0 < B j) ∧ (∀ j, 0 < E j) ∧ τ ≤ R / 16 ∧
      let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
        (0, (z₀, T.reference.spatialPatch z₀))
      let Ω := ball a (2 * ρ)
      closedBall a (2 * ρ) ⊆ domain T ∧
      MapsTo Prod.fst (closedBall a (2 * ρ))
        (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
          (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
      MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
        (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
          (z₀, T.reference.spatialPatch z₀))) R) (closedBall a ρ) ∧
      closedBall a (2 * σ) ⊆
        (coordinates (adaptedCoordinates T.data.adapted)).symm ''
          (Icc (-τ / 2) (τ / 2) ×ˢ closedBall
            ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀)) (R / 64)) ∧
      closedBall a (2 * σ) ⊆ closedBall a ρ ∧
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
        (∀ w ∈ closedBall a (2 * ρ), d ≤ |adaptedDenominator T Q row col w|) ∧
        (∀ w ∈ closedBall a (2 * σ),
          δ ≤ |(reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col| ∧
          |((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col)⁻¹| ≤ δ⁻¹) ∧
        let e := adaptedCoordinates T.data.adapted
        let Cc := coordinates (Z := Euclidean 3) e
        let pc := ((0 : Euclidean (n - 1)), z₀)
        ∃ Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen Dc ∧ Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ Dc ∧
          Dc ⊆ Ioo (-τc) τc ×ˢ ball pc (Rc / 4) ∧
          MapsTo (fun q ↦ (q.1, φ q)) (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) Dc ∧
          MapsTo (fun q ↦ (q.1, y q)) Dc (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) ∧
          (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, y (t, φ (t, p)) = p) ∧
          (∀ q ∈ Dc, φ (q.1, y q) = q.2) ∧
          (∀ p ∈ ball pc (Rc / 8), ∀ t ∈ Ioo (-τc) τc, HasDerivAt (fun s ↦ φ (s, p))
            ((e (carrierTransportDirection T Q row col (Cc.symm (t, φ (t, p))))).2, 0) t) ∧
          ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) ∧
          cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc ∧
      let p₀ := ((0 : Euclidean (n - 1)), (z₀, T.reference.spatialPatch z₀))
      let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1))
        (adaptedCoordinates T.data.adapted)
      let Bρ := closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) ρ
      let I := Ioo (-τ) τ
      let L := ball p₀ (R / 8)
      let J := Icc (-τ) τ ×ˢ closedBall p₀ (R / 8)
      let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ closedBall p₀ (R / 64))
      ∃ D : Set (ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))),
      ∃ Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)),
        IsOpen D ∧ I ×ˢ ball p₀ (R / 32) ⊆ D ∧ D ⊆ I ×ˢ ball p₀ (R / 4) ∧
        C ⁻¹' D ⊆ Ω ∧
        closedBall a (2 * σ) ⊆ C ⁻¹' D ∧
        (∀ (y : Euclidean (n - 1)) (z : Euclidean 3) (ζ : Euclidean (n - 1)),
          (T.data.adapted.embedding y, (z, ζ)) ∈ closedBall a (2 * σ) →
          phase T Q (T.data.adapted.embedding y) ζ = inner ℝ y ζ) ∧
        ContDiffOn ℝ ∞ Φ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y D ∧
        MapsTo (fun q ↦ (q.1, Φ q)) (I ×ˢ L) D ∧
        MapsTo (fun q ↦ (q.1, Y q)) D (I ×ˢ L) ∧
        (∀ p ∈ L, Φ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y (t, Φ (t, p)) = p) ∧
        (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, (Φ (t, p)).2.1 = p.2.1 ∧ (Φ (t, p)).2.2 = p.2.2) ∧
        (∀ q ∈ D, (Y q).2.1 = q.2.2.1 ∧ (Y q).2.2 = q.2.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ (s, p))
          ((adaptedCoordinates T.data.adapted
            (transportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
        ContDiffOn ℝ ∞ Φ (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        ContDiffOn ℝ ∞ Y (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball p₀ (R / 4)) ∧
        (∀ j, cNorm J j Φ + cNorm J j Y ≤ H j * (1 + cNorm K (j + 5) F)) ∧
        (∀ w ∈ C ⁻¹' D,
          b ≤ ‖nullvector T Q col w‖ ∧ b ≤ ‖phaseGradient T Q w.1 w.2.2‖ ∧
          reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
            (fun i ↦ nullvector T Q col w i) = 0 ∧
          conullvector T Q row w ᵥ*
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0) ∧
        (∀ j, cNorm Bρ j (nullvector T Q col) +
          cNorm Bρ j (conullvector T Q row) +
          cNorm Bρ j (adaptedDenominator T Q row col) +
          cNorm Bρ j (fun w ↦ (adaptedDenominator T Q row col w)⁻¹) +
          cNorm Bρ j (transportDirection T Q row col) +
          cNorm Bρ j (transportPotential T Q F row col) ≤ A j * (1 + cNorm K (j + 5) F)) ∧
        (∀ q ∈ Ioo (-δcomp) δcomp ×ˢ ball pc rcomp,
          q ∈ Dc ∧ (q.1, carrierLabel T q.2) ∈ D ∧
          (∀ t ∈ Ioo (-δcomp) δcomp,
            Φ (t, carrierLabel T (y q)) = carrierLabel T (φ (t, y q))) ∧
          Y (q.1, carrierLabel T q.2) = carrierLabel T (y q) ∧
          ∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
            let w := Cc.symm q
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w ∧
            scalarAmplitude T Q F row col Φ Y initial
                (w.1, (w.2, T.reference.spatialPatch w.2)) •
                nullvector T Q col (w.1, (w.2, T.reference.spatialPatch w.2)) =
              carrierScalarAmplitude T Q F row col φ y initial w • carrierNullvector T Q col w) ∧
        ∀ r : Euclidean (n - 1) × Euclidean 3 → ℝ,
          ContDiffOn ℝ ∞ r (ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) →
          cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r ≤ Mᵣ →
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m ≤ r p) →
          let α := scalarAmplitude T Q F row col Φ Y r
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • nullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ L, α (T.data.adapted.embedding p.1, p.2) = r (p.1, p.2.1)) ∧
          (∀ w ∈ C ⁻¹' D, g ≤ α w ∧ 0 < α w ∧
            nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 ∧
            α w • nullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (transportDirection T Q row col w) +
              transportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) *ᵥ
              (fun j ↦ (α w • nullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1 = 0) ∧
          (∀ j, cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
              (∀ w ∈ C ⁻¹' D,
                cν ≤ ‖principalNormal (canonicalNormalCompletion F w.1)
                  (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ∧
                determinant (Q.1 w.1) (phaseGradient T Q w.1 w.2.2) = 0 ∧
                (1 / 2 : ℝ) • linearizedMetric F
                    (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2))) w.1 =
                  stressProjection F w.1 (symmCovariantDeriv F (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1) ∧
                (∀ τ' : ℝ, τ' ≠ 0 →
                  completedVariationComplex F
                    (fun x ↦ (τ' : ℂ) ^ 2 •
                      Complex.exp (Complex.I * (phase T Q x w.2.2 : ℂ) / (τ' : ℂ)) •
                        euclideanComplexInclusion (α (x, w.2) • nullvector T Q col (x, w.2))) 0 w.1 =
                    Complex.exp (Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ' : ℂ)) •
                      ((Complex.I * (τ' : ℂ)) • euclideanComplexInclusion
                        (principalNormal (canonicalNormalCompletion F w.1)
                          (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)) +
                      (τ' : ℂ) ^ 2 • euclideanComplexInclusion
                        (reconstruction F (canonicalNormalCompletion F) (fun x ↦ α (x, w.2) • nullvector T Q col (x, w.2)) w.1))) ∧
                hermitianTensor ((principalMatrix
                    (principalNormal (canonicalNormalCompletion F w.1)
                      (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w))
                    (phaseGradient T Q w.1 w.2.2)).map Complex.ofReal) =
                  fun i j ↦ ‖principalNormal (canonicalNormalCompletion F w.1)
                    (phaseGradient T Q w.1 w.2.2) (α w • nullvector T Q col w)‖ ^ 2 *
                      phaseGradient T Q w.1 w.2.2 i * phaseGradient T Q w.1 w.2.2 j) ∧
          cNorm (closedBall a σ) 1 α ≤ B 1 * (1 + M + Mᵣ) ∧
          (∀ j, cNorm (closedBall a σ) j α ≤
            B j * (1 + cNorm K (j + 13) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r)) ∧
          let J₀ := closedBall a σ
          let b₀ := fun w ↦ α w • nullvector T Q col w
          let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q w.1 w.2.2
          let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
          let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
          ∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) := by
  obtain ⟨row, col, ρ, R, η, τ, g, bGap, cν, Rc, τc, Mc, rcomp, δcomp, d, A, Hflow, B,
    hρ, hR, hη, hτ, hg, hbGap, hcν, hRc, hτc, hMc, hrcomp, hδcomp, hd,
    hA, hHflow, hBamp, hτR, hdom, hx, hbuffer, hactual⟩ :=
    exists_actual_positive_amplitude_with_denominator hn hP T hK hKU hball hM hMᵣ hκmet hκnormal hm z₀ hz₀
  obtain ⟨σ₀, hσ₀, hJW₀, hJcoeff₀, hJsource₀⟩ :=
    exists_full_joint_working_ball hP T z₀ hz₀ hρ hR hτ
  obtain ⟨ηminor, ρminor, Lminor, δ, hηminor, hρminor, _hLminor, hδ, _hρminor,
    hminor⟩ := RawPrimary.exists_fullPhase_minor_neighborhood T (by omega : 2 ≤ n)
      ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) (by positivity : 0 < 2 * ρ)
      (fun w hw ↦ ball_subset_closedBall (hx hw).1) (hball.trans hKU) hdom row col hd
  let σ := min σ₀ ρminor
  have hσ : 0 < σ := lt_min hσ₀ hρminor
  have hσσ₀ : closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) (2 * σ) ⊆
      closedBall ((0 : Euclidean n), (z₀, T.reference.spatialPatch z₀)) (2 * σ₀) :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  have hJW := hσσ₀.trans hJW₀
  have hJcoeff := hσσ₀.trans hJcoeff₀
  have hJsource := fun w hw ↦ hJsource₀ w (hσσ₀ hw)
  let z := (z₀, T.reference.spatialPatch z₀)
  let J := closedBall ((0 : Euclidean n), z) σ
  have hJ2 : J ⊆ closedBall ((0 : Euclidean n), z) (2 * σ) :=
    closedBall_subset_closedBall (by linarith)
  have hJgeom : closedBall ((0 : Euclidean n), z) (2 * σ) ⊆
      closedBall ((0 : Euclidean n), z) (2 * ρ) :=
    hJcoeff.trans (closedBall_subset_closedBall (by linarith))
  have hphaseInitial (Q : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold}) (y₀ : Euclidean (n - 1)) (z₁ : Euclidean 3) (ζ : Euclidean (n - 1))
      (hp : (T.data.adapted.embedding y₀, (z₁, ζ)) ∈ closedBall ((0 : Euclidean n), z) (2 * σ)) :
      phase T Q (T.data.adapted.embedding y₀) ζ = inner ℝ y₀ ζ := by
    have hy₀ : ‖y₀‖ < T.physicalRadius := by
      have hh := (hx (hJgeom hp)).2.1
      simpa only [mem_ball, dist_zero_right, LinearIsometry.norm_map] using hh
    have hζ := hJsource (T.data.adapted.embedding y₀, (z₁, ζ)) hp
    exact phase_initial_value T Q (y := y₀) (ζ := ζ) hy₀ hζ
  have hJphase : J ⊆ domain T := hJ2.trans (hJgeom.trans hdom)
  obtain ⟨H, hH, hξbound⟩ := exists_phaseGradient_projected_sharp_bound
    (N := embeddingDimension n) T (isCompact_closedBall _ _) hJphase hK hKU hball M hκmet hκnormal
  obtain ⟨S, hS, hSbound⟩ := exists_phase_joint_projected_sharp_bound
    (N := embeddingDimension n) T (isCompact_closedBall _ _) hJphase hK hKU hball M hκmet hκnormal
  let Bcov := B 1 * (1 + M + Mᵣ) + H 1 * (1 + M)
  obtain ⟨E, hE, hrec⟩ := JointReconstruction.exists_cNorm_joint_reconstruction_le_of_primitive_bounds
    (N := embeddingDimension n) ((0 : Euclidean n), z) hσ
      (by linarith : 0 < 1 + M) hκmet hκnormal Bcov
  let Efinal := fun j ↦ S j + B j + E j * (1 + B (j + 1) + H j)
  have hEfinal (j) : 0 < Efinal j := by
    dsimp [Efinal]
    have := hS j
    have := hBamp j
    have := hBamp (j + 1)
    have := hH j
    have := hE j
    positivity
  refine ⟨row, col, ρ, R, min η ηminor, τ, g, bGap, cν, Rc, τc, Mc, rcomp, δcomp, σ, d, δ, A, Hflow, B, Efinal,
    hρ, hR, lt_min hη hηminor, hτ, hg, hbGap, hcν, hRc, hτc, hMc, hrcomp, hδcomp, hσ, hd, hδ,
    hA, hHflow, hBamp, hEfinal, hτR, hdom, hx, hbuffer, hJW, hJcoeff, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  have hF12 : cNorm K 12 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hF4 : cNorm K 4 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  obtain ⟨hlow, hden, Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, hsolution⟩ :=
    hactual F hF hi hrank hF12 hmet hnormal (hclose.trans_le (min_le_left _ _))
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hframe := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hcloseMinor : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < ηminor := by
    apply (cNorm_mono_set_of_contDiffAt hball hK _).trans_lt
      (hclose.trans_le (min_le_right _ _))
    intro x hxK
    exact ((hframe.contDiffAt (hU.mem_nhds (hKU hxK))).sub contDiffAt_const).of_le (by simp)
  have hminorBall := (hminor Q hcloseMinor
    (hden _ (mem_closedBall_self (by positivity)))).2
  have hselected (w) (hw : w ∈ closedBall ((0 : Euclidean n), z) (2 * σ)) :=
    hminorBall w (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_left (min_le_right σ₀ ρminor) (by norm_num)) hw)
  let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)
  let W := C.symm '' (Icc (-τ / 2) (τ / 2) ×ˢ
    closedBall ((0 : Euclidean (n - 1)), z) (R / 64))
  have hW : IsCompact W := (isCompact_Icc.prod (isCompact_closedBall _ _)).image C.symm.continuous
  have hWD : W ⊆ C ⁻¹' D := by
    rintro w ⟨⟨t, p⟩, ⟨ht, hp⟩, rfl⟩
    simp only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
    exact hcover ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      closedBall_subset_ball (by linarith) hp⟩
  have hballD := hJW.trans hWD
  refine ⟨hlow, hden, hselected, Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial Q,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, ?_⟩
  intro r hr hrM hrmin
  have hr5 : cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 5 r ≤ Mᵣ :=
    (cNorm_mono_order (by omega)).trans hrM
  obtain ⟨hα, hb, hinit, hpos, hpde, hsymbol, hreduce, habound, hidentity⟩ :=
    hsolution r hr hr5 hrmin
  have hαJ (j) : cNorm (closedBall ((0 : Euclidean n), z) σ) j
      (scalarAmplitude T Q F row col Φ Y r) ≤
      B j * (1 + cNorm K (j + 13) F +
        cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r) := by
    apply (cNorm_mono_set_of_contDiffAt (hJ2.trans hJW) hW
      (fun w hw ↦ (hα.contDiffAt
        ((hD.preimage C.continuous).mem_nhds (hWD hw))).of_le (by simp))).trans
    have hh := habound j
    linarith [cNorm_nonneg W j (fun w ↦
      scalarAmplitude T Q F row col Φ Y r w • nullvector T Q col w)]
  have hαLow : cNorm (closedBall ((0 : Euclidean n), z) σ) 1
      (scalarAmplitude T Q F row col Φ Y r) ≤ B 1 * (1 + M + Mᵣ) := by
    apply (hαJ 1).trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add_right hFM 1) hrM) (hBamp 1).le
  refine ⟨hα, hb, hinit, hpos, hpde, hsymbol, hreduce, habound, hidentity, hαLow, hαJ, ?_⟩
  dsimp only
  let b := fun w ↦ scalarAmplitude T Q F row col Φ Y r w • nullvector T Q col w
  let ξ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Euclidean n := fun w ↦ phaseGradient T Q w.1 w.2.2
  have hbW : ∀ w ∈ W, ContDiffAt ℝ ∞ b w :=
    fun w hw ↦ hb.contDiffAt ((hD.preimage C.continuous).mem_nhds (hWD hw))
  have hbJ (m) : cNorm J m b ≤ B m * (1 + cNorm K (m + 13) F +
      cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (m + 13) r) := by
    apply (cNorm_mono_set_of_contDiffAt (hJ2.trans hJW) hW
      (fun w hw ↦ (hbW w hw).of_le (by simp))).trans
    have hh := habound m
    linarith [cNorm_nonneg W m (scalarAmplitude T Q F row col Φ Y r)]
  have hξJ := hξbound F hF hi hrank hF4 hmet hnormal hlow
  have hSJ := hSbound F hF hi hrank hF4 hmet hnormal hlow
  let U₀ := ball (0 : Euclidean n) (2 * σ)
  let V₀ := ball z (2 * σ)
  have hprod : U₀ ×ˢ V₀ ⊆ closedBall ((0 : Euclidean n), z) (2 * σ) := by
    rw [show U₀ ×ˢ V₀ = ball ((0 : Euclidean n), z) (2 * σ) from ball_prod_same ..]
    exact ball_subset_closedBall
  have hUK : closedBall (0 : Euclidean n) (2 * σ) ⊆ K := by
    intro x hxSmall
    have hxz : (x, z) ∈ closedBall ((0 : Euclidean n), z) (2 * σ) := by
      rw [← closedBall_prod_same]
      exact ⟨hxSmall, mem_closedBall_self (by positivity)⟩
    exact interior_subset (hx (hJgeom hxz)).2.2
  have hU₀U : U₀ ⊆ U := ball_subset_closedBall.trans (hUK.trans hKU)
  have hphysical : closedBall (0 : Euclidean n) σ ⊆ K :=
    (closedBall_subset_closedBall (by linarith)).trans hUK
  have hFsmall (m) : cNorm (closedBall (0 : Euclidean n) σ) m F ≤ cNorm K m F :=
    cNorm_mono_set_of_contDiffAt hphysical hK
      (fun x hx ↦ (hF.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
  have hb1 : cNorm J 1 b ≤ Bcov := by
    have hh := hbJ 1
    norm_num only [Nat.reduceAdd] at hh
    have hl : B 1 * (1 + cNorm K 14 F +
        cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) 14 r) ≤
        B 1 * (1 + M + Mᵣ) := mul_le_mul_of_nonneg_left (by linarith) (hBamp 1).le
    have hp : 0 ≤ H 1 * (1 + M) := mul_nonneg (hH 1).le (by linarith)
    exact (hh.trans hl).trans (by dsimp [Bcov]; linarith)
  have hξ1 : cNorm J 1 ξ ≤ Bcov := by
    have hh := hξJ 1
    have h5 : cNorm K (1 + 4) F ≤ M := (cNorm_mono_order (by omega)).trans hFM
    have hl := mul_le_mul_of_nonneg_left (add_le_add_right h5 1) (hH 1).le
    have hp : 0 ≤ B 1 * (1 + M + Mᵣ) := mul_nonneg (hBamp 1).le (by linarith)
    exact (hh.trans hl).trans (by dsimp [Bcov]; linarith)
  have hrec' := hrec U₀ V₀ isOpen_ball isOpen_ball
    (closedBall_subset_ball (by linarith)) (closedBall_subset_ball (by linarith))
    F b ξ (hF.mono hU₀U) (fun x hx ↦ hi x (hU₀U hx)) (fun x hx ↦ hrank x (hU₀U hx))
    (hb.mono (hprod.trans hballD))
    ((phaseGradient_joint_smooth T Q).mono (hprod.trans (hJgeom.trans hdom)))
    ((hFsmall 4).trans (hF4.trans (by linarith)))
    (fun x hx ↦ hmet x (hphysical hx)) (fun x hx ↦ hnormal x (hphysical hx)) hb1 hξ1
  intro m
  let Z := 1 + cNorm K (m + 14) F +
    cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (m + 14) r
  have hSZ : cNorm J m (fun w ↦ phase T Q w.1 w.2.2) ≤ S m * Z := by
    apply (hSJ m).trans
    apply mul_le_mul_of_nonneg_left _ (hS m).le
    dsimp [Z]
    linarith [cNorm_mono_order (s := K) (f := F) (by omega : m + 3 ≤ m + 14),
      cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (m + 14) r]
  have hbZ : cNorm J m b ≤ B m * Z := by
    apply (hbJ m).trans
    apply mul_le_mul_of_nonneg_left _ (hBamp m).le
    dsimp [Z]
    exact add_le_add (add_le_add_right (cNorm_mono_order (by omega)) 1)
      (cNorm_mono_order (by omega))
  have hbZ1 : cNorm J (m + 1) b ≤ B (m + 1) * Z := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hbJ (m + 1)
  have hξZ : cNorm J m ξ ≤ H m * Z := by
    apply (hξJ m).trans
    apply mul_le_mul_of_nonneg_left _ (hH m).le
    dsimp [Z]
    linarith [cNorm_mono_order (s := K) (f := F) (by omega : m + 4 ≤ m + 14),
      cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (m + 14) r]
  have hFZ : 1 + cNorm (closedBall (0 : Euclidean n) σ) (m + 2) F ≤ Z := by
    have hh := (hFsmall (m + 2)).trans (cNorm_mono_order (by omega : m + 2 ≤ m + 14))
    dsimp [Z]
    linarith [cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (m + 14) r]
  have hrecZ := (hrec' m).trans (mul_le_mul_of_nonneg_left
    (show 1 + cNorm (closedBall (0 : Euclidean n) σ) (m + 2) F +
        cNorm J (m + 1) b + cNorm J m ξ ≤ (1 + B (m + 1) + H m) * Z by
      nlinarith) (hE m).le)
  calc
    _ = cNorm J m (fun w ↦ phase T Q w.1 w.2.2) + cNorm J m b +
        (cNorm J m (fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b w)) +
        cNorm J m (fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun y ↦ b (y, w.2)) w.1) +
        cNorm J m (fun w ↦ principalMatrix
          (principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b w)) (ξ w))) := by ring
    _ ≤ S m * Z + B m * Z + E m * ((1 + B (m + 1) + H m) * Z) :=
      add_le_add (add_le_add hSZ hbZ) hrecZ
    _ = Efinal m * Z := by dsimp [Efinal]; ring

end JanetCartan.LeadingWave.FullModulation
