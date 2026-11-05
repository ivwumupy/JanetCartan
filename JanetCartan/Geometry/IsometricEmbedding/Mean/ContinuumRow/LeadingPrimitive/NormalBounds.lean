module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.CarrierGraph
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback

/-!
# Normal bounds from the retained joint leading estimate

Fixed carrier graphs cost no derivative reserve. Arbitrary primitive charts
are permitted: their compact carrier must map into the leading estimate's
compact set, and their open region must lie in the smooth compatibility
neighborhood. These geometric obligations belong to the continuum row's
supported conic refinement. The analytic producer is
`CurrentCoefficientProfiles.exists_full_joint_leading_wave_before_geometry`.
Sources: `app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-mixed-input`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.LeadingPrimitive
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open LeadingWave LeadingWave.FullModulation CanonicalCarrier
open ActualCarriers.ConstructedCarrierJets ContinuumNormalReduction.TransportSymbol

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Restriction of the full leading normal to any compatible primitive chart.
The constants depend on the fixed graph and compact domains, and precede
the immersion, both transport flows, the initial scalar and derivative order.
Only full-modulation smoothness is supplied; the literal carrier normal's
smoothness and seminorm estimate are conclusions
(`app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-mixed-input`). -/
theorem exists_normalField_pullback_bounds {c C : ℝ} (hP : P.IsValid c C)
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    (hparameter : D.region ⊆ univ ×ˢ (parameter ⁻¹' parameterInterior (2 * P.radius)))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hJ : IsCompact J)
    (hgraph : MapsTo (carrierGraph T) D.carrier J) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (V : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → J ⊆ O →
      MapsTo (carrierGraph T) D.region O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) D.region V →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞
        (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) O →
      (∀ q ∈ V,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w) →
      ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col φ y initial)) D.region ∧
      ∀ j, cNorm D.carrier j (Function.uncurry (normalField T Q F row col φ y initial)) ≤
        A j * cNorm J j (fullNormal T Q F row col Φ Y initial) := by
  have hψ := (carrierGraph_smooth T hP).mono hparameter
  obtain ⟨A, hA, hb⟩ := exists_cNorm_fixed_pullback_le (G := Euclidean N)
    (isCompact_closedBall D.center D.radius) hJ
    (fun p hp ↦ hψ.contDiffAt (D.isOpen_region.mem_nhds (D.ball_subset hp))) hgraph
  refine ⟨A, hA, ?_⟩
  intro Q F row col Φ Y φ y initial O V hO hx hphase hJO hregion hcomp hF hi hrank hnull hc
  have hν := fullNormal_smooth T Q F row col Φ Y initial hO hx hphase hF hi hrank hnull
  have he : EqOn (Function.uncurry (normalField T Q F row col φ y initial))
      (fullNormal T Q F row col Φ Y initial ∘ carrierGraph T) D.region :=
    fun p hp ↦ normalField_eq_fullNormal_on_graph T Q F row col Φ Y φ y initial hc (hcomp hp)
  refine ⟨(hν.comp hψ hregion).congr he, fun j ↦ ?_⟩
  have he' : cNorm D.carrier j (Function.uncurry (normalField T Q F row col φ y initial)) =
      cNorm D.carrier j (fullNormal T Q F row col Φ Y initial ∘ carrierGraph T) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ j
    intro p hp
    exact eventuallyEq_of_mem (D.isOpen_region.mem_nhds (D.ball_subset hp))
      (fun q hq ↦ he hq)
  rw [he']
  exact hb _ (fun w hw ↦ hν.contDiffAt (hO.mem_nhds (hJO hw))) j

/-- Reserve-fourteen low and one-high normal bounds for the SAME retained
leading witnesses. The full normal bound is the corresponding nonnegative
summand of `exists_full_joint_leading_wave_before_geometry`; scalar
compatibility is its flow-uniqueness conclusion. No estimate on the carrier
normal or a new scalar is assumed. Fixed C15 budgets supply the C1 bound.
Consumer: `CoefficientNormCharts.Controls.normal`
(`app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-mixed-input`). -/
theorem exists_normalField_bounds_of_jointLeading {c C : ℝ} (hP : P.IsValid c C)
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    (hparameter : D.region ⊆ univ ×ˢ (parameter ⁻¹' parameterInterior (2 * P.radius)))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hJ : IsCompact J)
    (hgraph : MapsTo (carrierGraph T) D.carrier J)
    (K : Set (Euclidean n)) (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
    (E : ℕ → ℝ) (hE : ∀ j, 0 < E j)
    {MF Mr : ℝ} (hMF : 0 ≤ MF) (hMr : 0 ≤ Mr) :
    ∃ M > 0, ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
        (V : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → J ⊆ O →
      MapsTo (carrierGraph T) D.region O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) D.region V →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      ContDiffOn ℝ ∞
        (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) O →
      (∀ q ∈ V,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w) →
      cNorm K 15 F ≤ MF → cNorm Kinitial 15 initial ≤ Mr →
      (∀ j, cNorm J j (fullNormal T Q F row col Φ Y initial) ≤
        E j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial)) →
      ContDiffOn ℝ ∞ (Function.uncurry (normalField T Q F row col φ y initial)) D.region ∧
      cNorm D.carrier 1 (Function.uncurry (normalField T Q F row col φ y initial)) ≤ M ∧
      ∀ j, cNorm D.carrier j (Function.uncurry (normalField T Q F row col φ y initial)) ≤
        B j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial) := by
  obtain ⟨A, hA, hb⟩ := exists_normalField_pullback_bounds T (N := N) hP D hparameter hJ hgraph
  refine ⟨A 1 * E 1 * (1 + MF + Mr), by have := hA 1; have := hE 1; positivity,
    fun j ↦ A j * E j, fun j ↦ mul_pos (hA j) (hE j), ?_⟩
  intro Q F row col Φ Y φ y initial O V hO hx hphase hJO hregion hcomp hF hi hrank hnull hc
    hFM hrM hfull
  obtain ⟨hreg, hbound⟩ := hb Q F row col Φ Y φ y initial O V hO hx hphase hJO hregion hcomp
    hF hi hrank hnull hc
  have hhigh (j) := (hbound j).trans (mul_le_mul_of_nonneg_left (hfull j) (hA j).le)
  refine ⟨hreg, ?_, fun j ↦ (hhigh j).trans_eq (mul_assoc _ _ _).symm⟩
  calc
    _ ≤ A 1 * (E 1 * (1 + cNorm K 15 F + cNorm Kinitial 15 initial)) := hhigh 1
    _ = A 1 * E 1 * (1 + cNorm K 15 F + cNorm Kinitial 15 initial) := (mul_assoc _ _ _).symm
    _ ≤ A 1 * E 1 * (1 + MF + Mr) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_pos (hA 1) (hE 1)).le

end JanetCartan.ContinuumRow.LeadingPrimitive
