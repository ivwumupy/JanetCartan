module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.FamilyInputs
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.BudgetAssembly
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.LeadingAssembly

/-!
# The actual finite orthogonally corrected family

For `app:ch_waves:eq:primary-algebraic-correction`, `app:ch_waves:eq:WKB-residual`
and `app:ch_waves:eq:WKB-grading`, assemble the correction on the SAME finite
leading family. All original flows, scalar data, carrier restrictions and
leading identities are retained. The selected-minor gap and scalar budgets
are constructed, and the reserve-fourteen correction constants are fixed
before the immersion, initial datum, frequency and carrier label.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.RawPrimary
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open LeadingWave LeadingWave.FullModulation
open ProjectedStressFrame AmbientResponse ResponseTransfer CarrierCompatibility

/-- The actual finite leading family with its literal orthogonal correction:
joint smoothness, complex cancellation, the exact cubic residual, and a
one-high bound of reserve fourteen. Fixed-profile transfer gives `scale ^ j`
after any `k ≤ ν` joint parameter derivatives. Every additional analytic
premise of the correction lemmas is discharged on the original selected
family (`app:ch_waves:thm:wkb`, `app:ch_waves:eq:WKB-grading`). -/
theorem exists_finite_actual_corrected_family {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M Mᵣ κmet κnormal m : ℝ} (hM : 0 ≤ M) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hm : 0 < m)
 :
    ∃ η ε c : ℝ, ∃ E Γ : ℕ → ℝ,
      0 < η ∧ 0 < ε ∧ 0 < c ∧ (∀ j, 0 < E j) ∧ (∀ j, 0 < Γ j) ∧
      ∃ centers : Finset (parameterCube P.radius),
      ∃ row col : centers → Fin n,
      ∃ ρ R τ Rc τc Mc rcomp δcomp σ d δ : centers → ℝ,
      ∃ A H B : centers → ℕ → ℝ,
        (∀ j, 0 < ρ j ∧ 0 < R j ∧ 0 < τ j ∧ 0 < Rc j ∧ 0 < τc j ∧
          0 < Mc j ∧ 0 < rcomp j ∧ 0 < δcomp j ∧ 0 < σ j ∧ 0 < d j ∧ 0 < δ j) ∧
        (∀ j : centers,
          (∀ k, 0 < A j k) ∧ (∀ k, 0 < H j k) ∧ (∀ k, 0 < B j k) ∧ τ j ≤ R j / 16 ∧
          let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
            (0, (j.1.1, T.reference.spatialPatch j.1.1))
          closedBall a (2 * ρ j) ⊆ domain T ∧
          MapsTo Prod.fst (closedBall a (2 * ρ j))
            (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
              (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
          MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
            (closedBall ((0 : ℝ), ((0 : Euclidean (n - 1)),
              (j.1.1, T.reference.spatialPatch j.1.1))) (R j)) (closedBall a (ρ j)) ∧
          closedBall a (2 * σ j) ⊆
            (coordinates (adaptedCoordinates T.data.adapted)).symm ''
              (Icc (-τ j / 2) (τ j / 2) ×ˢ closedBall
                ((0 : Euclidean (n - 1)), (j.1.1, T.reference.spatialPatch j.1.1)) (R j / 64)) ∧
          closedBall a (2 * σ j) ⊆ closedBall a (ρ j)) ∧
        ∃ V : Set (Euclidean 3 × Euclidean (n - 1)),
          IsOpen V ∧ (∀ z ∈ parameterCube P.radius, (z, T.reference.spatialPatch z) ∈ V) ∧
          (ball (0 : Euclidean n) ε ×ˢ V ⊆
            ⋃ j : centers, closedBall ((0 : Euclidean n),
              (j.1.1, T.reference.spatialPatch j.1.1)) (σ j)) ∧
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
        let z₀ := j.1.1
        let row := row j
        let col := col j
        let ρ := ρ j
        let R := R j
        let τ := τ j
        let Rc := Rc j
        let τc := τc j
        let Mc := Mc j
        let rcomp := rcomp j
        let δcomp := δcomp j
        let σ := σ j
        let d := d j
        let δ := δ j
        let A := A j
        let H := H j
        let B := B j
        let g := c
        let b := c
        let cν := c
        let a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
          (0, (z₀, T.reference.spatialPatch z₀))
        let Ω := ball a (2 * ρ)
        closedBall a (2 * ρ) ⊆ domain T ∧
        MapsTo Prod.fst (closedBall a (2 * ρ))
          (ball (0 : Euclidean n) T.data.localReference.stateRadius ∩
            (ball (0 : Euclidean n) T.physicalRadius ∩ interior K)) ∧
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
          (∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) ∧
          ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) (C ⁻¹' D) ∧
          (∀ w ∈ C ⁻¹' D,
            Complex.I • ((reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).map
              Complex.ofReal *ᵥ (fun i ↦ fullCorrectionCovector T Q F row col Φ Y r w i)) +
              (fun i ↦ (reducedOperator F Q.1
                (fun x ↦ fullLeadingCovector T Q F row col Φ Y r (x, w.2)) w.1 i : ℂ)) = 0) ∧
          (∀ w ∈ C ⁻¹' D, ∀ lam : ℝ, lam ≠ 0 →
            complexReducedOperator F Q.1
              (twoTermWave lam (fun x ↦ phase T Q x w.2.2)
                (fun x ↦ euclideanComplexInclusion (fullLeadingCovector T Q F row col Φ Y r (x, w.2)))
                (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2))) w.1 =
              waveCarrier lam (fun x ↦ phase T Q x w.2.2) w.1 •
                (((lam : ℂ)⁻¹)^3 • complexReducedOperator F Q.1
                  (fun x ↦ fullCorrectionCovector T Q F row col Φ Y r (x, w.2)) w.1)) ∧
          (∀ j, cNorm J₀ j (fullCorrectionCovector T Q F row col Φ Y r) ≤
            Γ j * (1 + cNorm K (j + 14) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) ∧
          ∀ (RF Rr ν : ℕ) (scale : ℝ) (AF Ar : ℕ → ℝ),
            HasDerivativeProfile K F RF scale AF →
            HasDerivativeProfile (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) r Rr scale Ar →
            1 ≤ scale → (∀ j, 0 ≤ AF j) → (∀ j, 0 ≤ Ar j) →
            14 + ν ≤ RF → 14 + ν ≤ Rr →
            HasDerivativeProfile J₀ (fullCorrectionCovector T Q F row col Φ Y r) ν scale
              (fun j ↦ Γ j * (1 + AF (j + 14) + Ar (j + 14))) ∧
            ∀ j k : ℕ, k ≤ ν → ∀ w ∈ J₀,
              ‖iteratedFDeriv ℝ (j + k) (fullCorrectionCovector T Q F row col Φ Y r) w‖ ≤
                Γ (j + k) * (1 + AF (j + k + 14) + Ar (j + k + 14)) * scale ^ j := by
  classical
  obtain ⟨η, ε, c, E, hη, hε, hc, hE, centers, row, col, ρ, R, τ, Rc, τc, Mc,
    rcomp, δcomp, σ, d, δ, A, H, B, hpos, hstatic, V, hV, hgraph, hcover, hfamily⟩ :=
    exists_finite_actual_leading_family_with_correction_inputs
      hn hP T hK hKU hball hM hMᵣ hκmet hκnormal hm
  have hbud (j : centers) := by
    rcases hpos j with ⟨hρ, _hR, _hτ, _hRc, _hτc, _hMc, _hrcomp, _hδcomp, hσ, _hd, hδ⟩
    rcases hstatic j with ⟨_hA, _hH, hB, _hτR, hdom, hx, _hbuffer, _hJW, hsmall⟩
    have hsub : closedBall ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (σ j) ⊆
        closedBall ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1)) (2 * ρ j) :=
      (closedBall_subset_closedBall (by linarith : σ j ≤ 2 * σ j)).trans
        (hsmall.trans (closedBall_subset_closedBall (by linarith)))
    exact exists_fullCorrectionCovector_transport_bounds (N := embeddingDimension n)
      T hK hKU hball _ hσ (fun w hw ↦ ball_subset_closedBall (hx (hsub hw)).1)
      (hsub.trans hdom) (row j) (col j) M (B j 1 * (1 + M + Mᵣ)) (B j) hB hκmet hκnormal hδ
  choose G hG hbudget using hbud
  let Γ := fun q ↦ 1 + ∑ j : centers, G j q
  have hΓ (q) : 0 < Γ q := by
    have hh : 0 ≤ ∑ j : centers, G j q := Finset.sum_nonneg (fun j _ ↦ (hG j q).le)
    change 0 < 1 + ∑ j : centers, G j q
    linarith
  have hGΓ (j : centers) (q) : G j q ≤ Γ q := by
    have hh := Finset.single_le_sum (f := fun i : centers ↦ G i q)
      (fun i _ ↦ (hG i q).le) (Finset.mem_univ j)
    change G j q ≤ 1 + ∑ i : centers, G i q
    linarith
  refine ⟨η, ε, c, E, Γ, hη, hε, hc, hE, hΓ, centers, row, col,
    ρ, R, τ, Rc, τc, Mc, rcomp, δcomp, σ, d, δ, A, H, B,
    hpos, hstatic, V, hV, hgraph, hcover, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  obtain ⟨hlow, hfamilyF⟩ := hfamily F hF hi hrank hFM hmet hnormal hclose
  refine ⟨hlow, ?_⟩
  dsimp only
  intro j
  obtain ⟨hdom, hx, hden, hminor, Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcoverD, hbig, hphys, hballD, hphaseInitial,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, hsolution⟩ := hfamilyF j
  refine ⟨hdom, hx, hden, hminor, Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcoverD, hbig, hphys, hballD, hphaseInitial,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, ?_⟩
  intro r hr hrM hrmin
  obtain ⟨hα, hb₀, hinit, hpositive, hpde, hsymbol, hreduce, habound, hidentity,
    hαLow, hαJ, hjoint⟩ := hsolution r hr hrM hrmin
  refine ⟨hα, hb₀, hinit, hpositive, hpde, hsymbol, hreduce, habound, hidentity,
    hαLow, hαJ, hjoint, ?_⟩
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  let C := coordinates (Z := Euclidean 3 × Euclidean (n - 1)) (adaptedCoordinates T.data.adapted)
  let a := ((0 : Euclidean n), (j.1.1, T.reference.spatialPatch j.1.1))
  let J₀ := closedBall a (σ j)
  let Ω := C ⁻¹' D
  have hΩ : IsOpen Ω := hD.preimage C.continuous
  have hxU : MapsTo Prod.fst Ω U :=
    fun w hw ↦ hKU (interior_subset (hx (ball_subset_closedBall (hphys hw))).2.2)
  have hphase : Ω ⊆ domain T := fun _ hw ↦ hdom (ball_subset_closedBall (hphys hw))
  have hnonzero : ∀ w ∈ Ω, nullvector T Q (col j) w ≠ 0 ∧ conullvector T Q (row j) w ≠ 0 :=
    fun w hw ↦ ⟨(hpositive w hw).2.2.1, (hpositive w hw).2.2.2.1⟩
  have hsmooth := contDiffOn_fullCorrectionCovector_of_leading_outputs
    T Q F (row j) (col j) Φ Y r hΩ (fun _ hw ↦ hxU hw) (fun _ hw ↦ hphase hw)
      hF hi hα hnonzero
  have hsym : ∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm := fun w hw i ↦
    (projectedStress_mem_stressSpace
      ((hF.contDiffAt (hU.mem_nhds (hxU hw))).of_le (by simp)) (hrank w.1 (hxU hw)) i).1
  have hσ : 0 < σ j := (hpos j).2.2.2.2.2.2.2.2.1
  have hsmall : J₀ ⊆ closedBall a (2 * σ j) :=
    closedBall_subset_closedBall (by linarith)
  have hJΩ : J₀ ⊆ Ω := hsmall.trans hballD
  have hbound (q) : cNorm J₀ q (fullCorrectionCovector T Q F (row j) (col j) Φ Y r) ≤
      Γ q * (1 + cNorm K (q + 14) F +
        cNorm (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8)) (q + 14) r) := by
    have hb := hbudget j F hF hi hrank hFM hmet hnormal hlow Φ Y r
      (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8)) Ω hΩ hJΩ hxU hphase
      hα hαLow hαJ (fun w hw ↦ (hminor w (hsmall hw)).1) q
    exact hb.trans (mul_le_mul_of_nonneg_right (hGΓ j q)
      (by linarith [cNorm_nonneg K (q + 14) F,
        cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8)) (q + 14) r]))
  refine ⟨hsmooth, ?_, ?_, hbound, ?_⟩
  · intro w hw
    exact fullCorrectionCovector_cancel_of_leading_outputs T Q F (row j) (col j) Φ Y r
      (hphase hw) (hnonzero w hw).1 (hnonzero w hw).2 (hreduce w hw)
  · intro w hw lam hlam
    exact fullTwoTermWave_reduced_residual_of_leading_outputs T Q F (row j) (col j) Φ Y r
      hΩ (fun _ hw ↦ hxU hw) (fun _ hw ↦ hphase hw) hF hi hα hnonzero hreduce hw (hsym w hw) hlam
  · intro RF Rr ν scale AF Ar hPF hPr hscale hAF hAr hRF hRr
    have hprofile : HasDerivativeProfile J₀ (fullCorrectionCovector T Q F (row j) (col j) Φ Y r)
        ν scale (fun q ↦ Γ q * (1 + AF (q + 14) + Ar (q + 14))) := by
      intro q
      have hFgrade : cNorm K (q + 14) F ≤ AF (q + 14) * scale ^ (q - ν) :=
        (hPF (q + 14)).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hscale (by omega : q + 14 - RF ≤ q - ν)) (hAF _))
      have hrgrade : cNorm (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j / 8)) (q + 14) r ≤
          Ar (q + 14) * scale ^ (q - ν) :=
        (hPr (q + 14)).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hscale (by omega : q + 14 - Rr ≤ q - ν)) (hAr _))
      exact (hbound q).trans ((mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (one_le_pow₀ hscale : 1 ≤ scale ^ (q - ν)) hFgrade) hrgrade)
          (hΓ q).le).trans_eq (by ring))
    refine ⟨hprofile, ?_⟩
    intro q k hk w hw
    have hs (v) (hv : v ∈ J₀) :
        ContDiffAt ℝ (q + k) (fullCorrectionCovector T Q F (row j) (col j) Φ Y r) v :=
      (hsmooth.contDiffAt (hΩ.mem_nhds (hJΩ hv))).of_le (by simp)
    apply (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a (σ j)) hs hw le_rfl).trans
    apply (hprofile (q + k)).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hscale (by omega : q + k - ν ≤ q))
      (mul_nonneg (hΓ _).le (by have := hAF (q + k + 14); have := hAr (q + k + 14); positivity))

end JanetCartan.RawPrimary
