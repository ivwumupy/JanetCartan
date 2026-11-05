module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.FullModulationConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.PhaseProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.HistoryGeometry.TransportBudget
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.FixedReferenceProfiles.SourceInterval

/-!
# Full-modulation leading profiles along the initialized history

For `main:prop:current-scale` and `app:eq:uniform-high-coeff`, this module
instantiates the actual full-modulation construction on every admissible prefix
of every sufficiently small source dilation. The initializer's reference is
retained by literal map equality. Finite covering domains and the source cap
precede all history orders, budgets and accuracy parameters.

The actual history supplies smoothness, separate geometric gaps, frame
closeness, the C14 immersion budget and the high map profile. Scalar initial
data remain explicit: the mixed estimates retain their actual high seminorms.
The prepared positive scalar and its uniform profile must still be supplied by
the positive-background construction and `PreparedProfiles.prepared_scalar_profiles`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open ProjectedStressFrame AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility

/-- `main:prop:current-scale`, `app:eq:uniform-high-coeff`: the SAME initialized
reference and actual histories support finite full-modulation leading families.
All map, frame, flow and geometric premises of
`exists_finite_actual_leading_family_before_geometry` are discharged. The
scalar and null-amplitude estimate has reserve thirteen; the full phase,
null amplitude, principal normal, reconstruction and principal matrix have
reserve fourteen, independent of the requested high derivative order.

The literal carrier/full-flow compatibility, initial values, positivity,
transport/null identities, exact half-strain, both complex quadratures and
principal tensor are retained. The last estimate gives the paper profile for
fixed initial data; for history-dependent prepared data the preceding mixed
estimate must be combined with their actual prepared-scalar producer on these
same initial balls. This does not assert that remaining construction. -/
theorem exists_source_scale_cap_for_history_full_modulation {n : ℕ} (hn : 5 ≤ n)
    {I : Type*} [Fintype I] (G₀ : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    (P : I → Patch n) {c₀ C₁ : ℝ} (hP : ∀ i, (P i).IsValid c₀ C₁)
    (family : (i : I) → PatchQuantitativeFamily (P i) (ball 0 R) isOpen_ball)
    (hball : ∀ i, closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius ⊆ closedBall 0 r) :
    ∃ ε : I → ℝ, (∀ i, 0 < ε i) ∧
    ∃ centers : (i : I) → Finset (parameterCube (P i).radius),
    ∃ row col : (i : I) → centers i → Fin n,
    ∃ ρ L τ Rc τc Mc rcomp δcomp σcover : (i : I) → centers i → ℝ,
      (∀ i j, 0 < ρ i j ∧ 0 < L i j ∧ 0 < τ i j ∧ 0 < Rc i j ∧ 0 < τc i j ∧
        0 < Mc i j ∧ 0 < rcomp i j ∧ 0 < δcomp i j ∧ 0 < σcover i j) ∧
    ∃ V : I → Set (Euclidean 3 × Euclidean (n - 1)),
      (∀ i, IsOpen (V i) ∧
        (∀ z ∈ parameterCube (P i).radius, (z, (family i).reference.spatialPatch z) ∈ V i) ∧
        (ball (0 : Euclidean n) (ε i) ×ˢ V i ⊆
          ⋃ j : centers i, closedBall ((0 : Euclidean n),
            (j.1.1, (family i).reference.spatialPatch j.1.1)) (σcover i j))) ∧
    ∃ cap : ℝ, 0 < cap ∧ cap ≤ 1 ∧
    ∀ σ : ℝ, 0 < σ → σ ≤ cap →
    ∀ G : FlatReference n, G.map = sourceDilation G₀.map σ →
    ∀ rStar r₀ kMin : ℕ, 14 ≤ rStar → 14 + r₀ ≤ rStar →
      displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin →
    ∀ Mᵣ m₀ : ℝ, 0 ≤ Mᵣ → 0 < m₀ →
    ∃ S : ℝ, 2 ≤ S ∧ ∃ κ > 0,
    ∃ c : I → ℝ, ∃ Amap : ℕ → ℝ, ∃ E : I → ℕ → ℝ,
    ∃ A H B : (i : I) → centers i → ℕ → ℝ,
      (∀ i, 0 < c i) ∧ (∀ m, 0 ≤ Amap m) ∧ (∀ i m, 0 < E i m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (stage : ℕ) (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin stage → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      let K := closedBall (0 : Euclidean n) r
      ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
        (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
        cNorm K 14 F ≤ cNorm K 14 G.map + 1 ∧
        (∀ x ∈ ball 0 R, ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        HasDerivativeProfile K F rStar (currentCoefficientScale R₀ stage) Amap ∧
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (family i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (family i).family.threshold,
        ∀ i,
        let T := family i
        let centers := centers i
        let row := row i
        let col := col i
        let ρ := ρ i
        let R := L i
        let τ := τ i
        let Rc := Rc i
        let τc := τc i
        let Mc := Mc i
        let rcomp := rcomp i
        let δcomp := δcomp i
        let σ := σcover i
        let c := c i
        let E := E i
        let A := A i
        let H := H i
        let B := B i
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩
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
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), m₀ ≤ r p) →
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
              cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 13) r) ∧
            cNorm W j α + cNorm W j (fun w ↦ α w • nullvector T Q col w) ≤
              |B j| * ((1 + Amap (j + 13)) *
                currentCoefficientScale R₀ stage ^ (j - r₀) +
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
          let J₀ := closedBall a σ
          let b₀ := fun w ↦ α w • nullvector T Q col w
          let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            phaseGradient T Q w.1 w.2.2
          let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
          let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
          ∀ j, cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * (1 + cNorm K (j + 14) F +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) ∧
            cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              E j * ((1 + Amap (j + 14)) *
                currentCoefficientScale R₀ stage ^ (j - r₀) +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r) ∧
            cNorm J₀ j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J₀ j b₀ +
            cNorm J₀ j ν + cNorm J₀ j V + cNorm J₀ j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
              (E j * (1 + Amap (j + 14) +
                cNorm (closedBall ((0 : Euclidean (n - 1)), z₀) (R / 8)) (j + 14) r)) *
                  currentCoefficientScale R₀ stage ^ (j - r₀) := by
  classical
  have hK : IsCompact (closedBall (0 : Euclidean n) r) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  choose η ε hη hε centers row col ρ L τ Rc τc Mc rcomp δcomp σcover
    hpositive V hV hgraph hcover hproduce using
    fun i ↦ exists_finite_actual_leading_family_before_geometry hn (hP i)
      (family i) hK hKU (hball i)
  obtain ⟨_, d, _, _, _, hd, _, hcommon⟩ := exists_common_phase_buffers
    (fun _ : I ↦ (1 : ℝ)) η (fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_lt_one) hη
  have heps : 0 < d / (2 * (6 + 1 : ℝ)) := by positivity
  obtain ⟨cap, hcap, hcap₁, hsmall⟩ :=
    FixedReferenceProfiles.exists_source_scale_interval_projectedStress_lt G₀ hK (half_pos heps)
  refine ⟨ε, hε, centers, row, col, ρ, L, τ, Rc, τc, Mc, rcomp, δcomp, σcover,
    hpositive, V, (fun i ↦ ⟨hV i, hgraph i, hcover i⟩), cap, hcap, hcap₁, ?_⟩
  intro σ hσ hσcap Gfixed hmap rStar r₀ kMin hStar hreserve horder Mᵣ m₀ hMᵣ hm₀
  rw [hmap]
  let G := sourceDilationReference G₀ hσ (hσcap.trans hcap₁)
  have h14 : displacementLoss n + bandExponent * (14 + (n : ℝ) / 2) + 2 < kMin := by
    have hs : (14 : ℝ) ≤ rStar := by exact_mod_cast hStar
    have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
    exact lt_of_le_of_lt (by nlinarith) horder
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
    exact lt_of_le_of_lt (by nlinarith) h14
  obtain ⟨Sg, hSg, C₀, _, κ, hκ, hgeom⟩ :=
    HistoryGeometry.exists_cube_frame_neighborhood G hr hrR hR h8 heps (hsmall σ hσ hσcap)
  obtain ⟨St, hSt, hbudget⟩ := HistoryGeometry.exists_initialScale_for_fixed_immersion_bound
    14 G.map G.contDiff (closedBall 0 r) hK h14
  obtain ⟨Amap, hAmap, hprofile⟩ := exists_admissible_history_profile G.map G.contDiff hK
    rStar kMin horder
  choose c E A H B hc hE hactual using fun i ↦ hproduce i
    (cNorm (closedBall 0 r) 14 G.map + 1) Mᵣ (1 / 4) κ m₀
    (by linarith [cNorm_nonneg (closedBall 0 r) 14 G.map]) hMᵣ (by norm_num) hκ hm₀
  refine ⟨max Sg St, hSg.trans (le_max_left _ _), κ, hκ, c, Amap, E, A, H, B,
    hc, hAmap, hE, ?_⟩
  intro R₀ hR₀ stage u ell hu
  have hRg := (le_max_left Sg St).trans hR₀
  have hRt := (le_max_right Sg St).trans hR₀
  have hRtwo : 2 ≤ R₀ := hSg.trans hRg
  have hscale := one_le_currentCoefficientScale (show 1 ≤ R₀ by linarith) stage
  let F := finiteHistoryMap G.map u
  have hF : ContDiffOn ℝ ∞ F (ball 0 R) :=
    (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn
  obtain ⟨hi, hrank, _, hmet, hnormal, hQ, hclose⟩ := hgeom R₀ hRg stage u ell hu
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) := contDiffOn_pi.mpr hQ
  have hframeK : cNorm (closedBall 0 r) 6
      (projectedStress F - fun _ ↦ cubeStress n) < d :=
    frame_cNorm_lt_of_componentwise hK
      (fun x hx ↦ ((hframe.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).sub
        contDiffAt_const).of_le (by simp)) hd hclose
  have hlowF := hbudget R₀ hRt stage u ell hu
  have hp := hprofile R₀ hRtwo stage u ell hu (closedBall 0 r) (Subset.refl _)
  choose hlow hspec using fun i ↦ hactual i F hF hi hrank hlowF
    (fun x hx ↦ hmet x (hKU hx)) (fun x hx ↦ hnormal x (hKU hx))
    (hframeK.trans_le (hcommon i).2.1)
  refine ⟨hF, hi, hrank, hlowF, hmet, hnormal, hp, hlow, ?_⟩
  intro i
  dsimp only
  intro j
  obtain ⟨hdom, hx, Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, hsolution⟩ := hspec i j
  refine ⟨hdom, hx, Dc, φ, y, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, ?_⟩
  intro initial hsmooth hlowInitial hpos
  obtain ⟨hα, hb₀, hinit, hpositive, hpde, hsymbol, hreduce, habound, hidentity, hjoint⟩ :=
    hsolution initial hsmooth hlowInitial hpos
  have hmapBound (m d : ℕ) (hd : d + r₀ ≤ rStar) :
      1 + cNorm (closedBall 0 r) (m + d) F ≤
        (1 + Amap (m + d)) * currentCoefficientScale R₀ stage ^ (m - r₀) := by
    simpa only [one_mul] using JointBudget.fixed_profile_transfer_bound hscale
      (hAmap (m + d)) (by norm_num : (0 : ℝ) ≤ 1) hd (hp (m + d))
      (le_refl (1 * (1 + cNorm (closedBall 0 r) (m + d) F)))
  refine ⟨hα, hb₀, hinit, hpositive, hpde, hsymbol, hreduce, ?_, hidentity, ?_⟩
  · intro m
    refine ⟨habound m, ?_⟩
    have habs := (habound m).trans (mul_le_mul_of_nonneg_right (le_abs_self (B i j m))
      (by linarith [cNorm_nonneg (closedBall (0 : Euclidean n) r) (m + 13) F,
        (cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), j.1.1) (L i j / 8))
          (m + 13) initial)]))
    exact habs.trans (mul_le_mul_of_nonneg_left
      (add_le_add (hmapBound m 13 (by omega)) le_rfl) (abs_nonneg _))
  · intro m
    have hmixed := (hjoint m).trans (mul_le_mul_of_nonneg_left
      (add_le_add (hmapBound m 14 hreserve) le_rfl) (hE i m).le)
    refine ⟨hjoint m, hmixed, ?_⟩
    have hinitBound := mul_le_mul_of_nonneg_left (one_le_pow₀ hscale (n := m - r₀))
      (cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), j.1.1) (L i j / 8))
        (m + 14) initial)
    have hh := hmixed.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (by simpa only [mul_one] using hinitBound)) (hE i m).le)
    simpa only [← add_mul, mul_assoc, F, G, sourceDilationReference] using hh

end JanetCartan.CurrentCoefficientProfiles
