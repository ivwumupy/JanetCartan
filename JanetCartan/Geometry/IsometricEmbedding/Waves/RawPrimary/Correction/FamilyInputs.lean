module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.FamilyInputs.Local
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.Density
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers

/-!
# One actual finite leading family with quantitative correction inputs

The finite cover is selected AFTER shrinking the local balls to the scalar tame
working sets and the selected-minor neighborhoods. All rows, columns, domains,
positive numerical gaps and budgets precede the immersion and initial scalar.
The same flows, footpoints and literal scalar retain the original carrier
compatibility, nullvector identities and reduced transport equation.

The outputs supply the primitive inputs to `RawPrimary`'s correction bounds and
`fullTwoTermWave_reduced_residual_of_leading_outputs`; final correction estimates,
grading and WKB assembly remain with that construction
(`app:ch_waves:thm:leading`, `app:ch_waves:eq:primary-algebraic-correction`,
`app:ch_waves:eq:WKB-grading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.LeadingWave.FullModulation
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open ProjectedStressFrame AmbientResponse ResponseTransfer CarrierCompatibility

/-- Finite actual leading waves on a full open neighborhood of the original
carrier graph. The same positive scalar is used by the carrier restriction and
both complex quadratures. The common positive gap and reserve-fourteen joint
constants are fixed before `F` and the original initial scalar `r(y,z)`.
The denominator and minor gaps, working-set containment, scalar `C¹` budget
and reserve-thirteen bound hold on this SAME family. The literal density identity is `scalarAmplitude_principal_tensor_density`
(`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_finite_actual_leading_family_with_correction_inputs {n : ℕ} (hn : 5 ≤ n)
    {P : Patch n} {c₀ C₁ : ℝ} (hP : P.IsValid c₀ C₁)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M Mᵣ κmet κnormal m : ℝ} (hM : 0 ≤ M) (hMᵣ : 0 ≤ Mᵣ)
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hm : 0 < m)
 :
    ∃ η ε c : ℝ, ∃ E : ℕ → ℝ,
      0 < η ∧ 0 < ε ∧ 0 < c ∧ (∀ j, 0 < E j) ∧
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
          ∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) := by
  classical
  choose row col ρ R η τ g b cν Rc τc Mc rcomp δcomp σ denGap minorGap A H B E
    hρ hR hη hτ hg hb hcν hRc hτc hMc hrcomp hδcomp hσ hdenGap hminorGap hA hH hB hE hτR
    hdom hx hbuffer hJW hJcoeff hlocal using
    fun z : parameterCube P.radius ↦ exists_actual_joint_leading_wave_with_correction_inputs
      hn hP T hK hKU hball hM hMᵣ hκmet hκnormal hm z.1 z.2
  let graph := fun z : Euclidean 3 ↦ (z, T.reference.spatialPatch z)
  have hgraph : ContinuousOn graph (parameterCube P.radius) :=
    continuousOn_id.prodMk ((T.reference.spatialPatch_smooth hP).continuousOn.mono
      (parameterCube_subset_doubledInterior hP.1))
  -- Relative openness is enough for compactness, via the subtype graph.
  let Osub := fun z : parameterCube P.radius ↦
    (fun q : parameterCube P.radius ↦ graph q.1) ⁻¹' ball (graph z.1) (σ z / 2)
  have hOsub (z) : IsOpen (Osub z) :=
    isOpen_ball.preimage hgraph.domRestrict
  have hcoverSub : (univ : Set (parameterCube P.radius)) ⊆ ⋃ z, Osub z := by
    intro z _
    exact mem_iUnion.mpr ⟨z, mem_ball_self (half_pos (hσ z))⟩
  let : CompactSpace (parameterCube P.radius) := isCompact_iff_compactSpace.mp
    (isCompact_parameterCube P.radius)
  obtain ⟨centers, hcenters⟩ := isCompact_univ.elim_finite_subcover Osub hOsub hcoverSub
  obtain ⟨ε, d, _, hε, _, hd, _, hcommon⟩ := exists_common_phase_buffers
    (fun j : centers ↦ σ j.1 / 2)
    (fun j : centers ↦ min (η j.1) (min (g j.1) (min (b j.1) (cν j.1))))
    (fun _ ↦ 0) (fun j ↦ half_pos (hσ j.1))
    (fun j ↦ lt_min (hη j.1) (lt_min (hg j.1) (lt_min (hb j.1) (hcν j.1))))
  let Emax := fun m ↦ 1 + ∑ j : centers, E j.1 m
  have hEmax (m) : 0 < Emax m := by
    have hh : 0 ≤ ∑ j : centers, E j.1 m := Finset.sum_nonneg (fun j _ ↦ (hE j.1 m).le)
    change 0 < 1 + ∑ j : centers, E j.1 m
    linarith
  have hEE (j : centers) (m) : E j.1 m ≤ Emax m := by
    have hh := Finset.single_le_sum (f := fun i : centers ↦ E i.1 m)
      (fun i _ ↦ (hE i.1 m).le) (Finset.mem_univ j)
    change E j.1 m ≤ 1 + ∑ i : centers, E i.1 m
    linarith
  let V := ⋃ j : centers, ball (graph j.1.1) (σ j.1 / 2)
  refine ⟨min d T.family.threshold, ε, d, Emax,
    lt_min hd T.family.threshold_pos, hε, hd, hEmax, centers,
    (fun j ↦ row j.1), (fun j ↦ col j.1),
    (fun j ↦ ρ j.1), (fun j ↦ R j.1), (fun j ↦ τ j.1),
    (fun j ↦ Rc j.1), (fun j ↦ τc j.1), (fun j ↦ Mc j.1),
    (fun j ↦ rcomp j.1), (fun j ↦ δcomp j.1), (fun j ↦ σ j.1),
    (fun j ↦ denGap j.1), (fun j ↦ minorGap j.1),
    (fun j ↦ A j.1), (fun j ↦ H j.1), (fun j ↦ B j.1),
    (fun j ↦ ⟨hρ j.1, hR j.1, hτ j.1, hRc j.1, hτc j.1, hMc j.1,
      hrcomp j.1, hδcomp j.1, hσ j.1, hdenGap j.1, hminorGap j.1⟩),
    (fun j ↦ ⟨hA j.1, hH j.1, hB j.1, hτR j.1, hdom j.1, hx j.1,
      hbuffer j.1, hJW j.1, hJcoeff j.1⟩), V, isOpen_iUnion (fun _ ↦ isOpen_ball), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcenters (mem_univ (⟨z, hz⟩ : parameterCube P.radius)))
    obtain ⟨hq', hzq⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨⟨q, hq'⟩, hzq⟩
  · rintro ⟨x, zf⟩ ⟨hx₀, hz⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    apply mem_iUnion.mpr ⟨j, ?_⟩
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    have he : ε ≤ σ j.1 := by
      have hh := (hcommon j).1
      change 3 * ε < σ j.1 / 2 at hh
      linarith
    exact ⟨(mem_ball.mp hx₀).le.trans he,
      (mem_ball.mp hj).le.trans (by linarith [hσ j.1])⟩
  · intro F hF hi hrank hFM hmet hnormal hclose
    have hframe := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
    have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
      apply (cNorm_mono_set_of_contDiffAt hball hK _).trans_lt
        (hclose.trans_le (min_le_right _ _))
      intro x hxK
      exact ((hframe.contDiffAt (hU.mem_nhds (hKU hxK))).sub contDiffAt_const).of_le (by simp)
    refine ⟨hlow, ?_⟩
    dsimp only
    intro j
    obtain ⟨hlowj, hden, hselected, Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
      hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
      hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
      hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, hsolution⟩ :=
      hlocal j.1 F hF hi hrank hFM hmet hnormal
        (hclose.trans_le ((min_le_left _ _).trans ((hcommon j).2.1.trans (min_le_left _ _))))
    have hdrest := (hcommon j).2.1.trans (min_le_right _ _)
    have hdg : d ≤ g j.1 := hdrest.trans (min_le_left _ _)
    have hdb : d ≤ b j.1 := hdrest.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hdν : d ≤ cν j.1 := hdrest.trans ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨hdom j.1, hx j.1, hden, hselected, Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
      hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
      hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
      hΦbuffer, hYbuffer, hflow, ?_, hcoeff, hcompat, ?_⟩
    · intro w hw
      exact ⟨hdb.trans (hgaps w hw).1, hdb.trans (hgaps w hw).2.1, (hgaps w hw).2.2⟩
    · intro r hr hrM hrmin
      obtain ⟨hα, hb₀, hinit, hpos, hpde, hsymbol, hreduce, habound, hidentity, hαLow, hαJ, hjoint⟩ :=
        hsolution r hr hrM hrmin
      refine ⟨hα, hb₀, hinit, (fun w hw ↦ ⟨hdg.trans (hpos w hw).1, (hpos w hw).2⟩),
        hpde, hsymbol, hreduce, habound,
        (fun w hw ↦ ⟨hdν.trans (hidentity w hw).1, (hidentity w hw).2⟩), hαLow, hαJ, ?_⟩
      intro m
      exact (hjoint m).trans (mul_le_mul_of_nonneg_right (hEE j m)
        (by linarith [cNorm_nonneg K (m + 14) F,
          cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), j.1.1) (R j.1 / 8)) (m + 14) r]))

end JanetCartan.LeadingWave.FullModulation
