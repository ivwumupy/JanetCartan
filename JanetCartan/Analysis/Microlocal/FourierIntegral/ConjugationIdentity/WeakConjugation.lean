module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.WeakOutput

/-!
# The unregularized two-term conjugation identity

The literal compact-frequency identity passes to limits on compact local tests.
The physical operator acts on the undifferentiated graph limit by the weak
formula proved in `WeakOutput`. All integral pairings used here are integrable
by local smoothness and compact test support. Only convergence of the three
undifferentiated graph sequences is assumed.

Source: `app:ch_regular_base:eq:direct-graph-identity`. The consuming finite FIO
and regular-sector constructions must instantiate the phase, transport,
coefficient regularity and convergence inputs; no unconditional existence or
symbol estimate is asserted here.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

set_option maxHeartbeats 600000 in
/-- The unregularized local distributional identity of
`app:ch_regular_base:eq:direct-graph-identity`, obtained from the three actual
undifferentiated graph limits. The limits are specified by convergence on every
compact test in the output chart. Pairing integrability and weak output
integration by parts are proved, not assumed. `F` is the limit of the two-term
graph, `G` of the transport graph applied to `D_t v`, and `R` of the actual
correction remainder graph. The phase/transport producers supply `hreg`; the
finite FIO producer must supply the three convergence statements and local
coefficient smoothness. This conditional theorem asserts no existence of those
limits or solutions. -/
theorem twoTermGraph_distributional_conjugation
    (H : Euclidean n → Euclidean n →L[ℝ] Matrix (Fin r) (Fin r) ℝ)
    (B : Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χ : ℕ → Euclidean n → ℂ) (O : Set (Euclidean n)) (t : Fin n)
    (v : Euclidean n → Fin r → ℂ) (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v)
    (hreg : ∀ k, TwoTermGraphRegularization H B S U (χ k) O t)
    (hA : ∀ (j : Fin n) (i l : Fin r), ContDiffOn ℝ ∞
      (fun x ↦ complexifiedPencil (H x) (EuclideanSpace.single j 1) i l) O)
    (hB : ∀ (i l : Fin r), ContDiffOn ℝ ∞ (fun x ↦ B x i l) O)
    (F G R : 𝓢'(Euclidean n, Fin r → ℂ))
    (hF : ∀ (φ : 𝓢(Euclidean n, ℂ)), HasCompactSupport φ → tsupport φ ⊆ O → ∀ i : Fin r,
      Tendsto (fun k ↦ ∫ x, φ x * graphOperator (r := r) S (fun z _ η ↦ χ k η • twoTermGraphAmplitude (r := r)
        (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v x i)
        atTop (𝓝 (F φ i)))
    (hG : ∀ (φ : 𝓢(Euclidean n, ℂ)), HasCompactSupport φ → tsupport φ ⊆ O → ∀ i : Fin r,
      Tendsto (fun k ↦ ∫ x, φ x * graphOperator (r := r) S (fun z _ η ↦ χ k η • U z η)
        (fun y ↦ -Complex.I • partialDeriv v y t) x i) atTop (𝓝 (G φ i)))
    (hR : ∀ (φ : 𝓢(Euclidean n, ℂ)), HasCompactSupport φ → tsupport φ ⊆ O → ∀ i : Fin r,
      Tendsto (fun k ↦ ∫ x, φ x * graphOperator (r := r) S (fun z _ η ↦ χ k η • twoTermGraphRemainder (r := r)
        (fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)) B
        (fun q ↦ (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal) S U z η) v x i)
        atTop (𝓝 (R φ i))) :
    ∀ (φ : 𝓢(Euclidean n, ℂ)) (hK : HasCompactSupport φ) (hs : tsupport φ ⊆ O) (i : Fin r),
      graphPhysicalDistributionPairing (n := n) (r := r) (O := O) (hreg 0).output_open
        (fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)) B hA hB F φ hK hs i -
        G φ i = R φ i := by
  let A : Euclidean n → Fin n → Matrix (Fin r) (Fin r) ℂ := fun z j ↦ complexifiedPencil (H z) (EuclideanSpace.single j 1)
  let c := fun q : Euclidean n × Euclidean n ↦
    (normalizedAdjugateSymbol (H q.1) q.2).map Complex.ofReal
  let f : ℕ → Euclidean n → Fin r → ℂ := fun k ↦ graphOperator (r := r) S (fun z _ η ↦ χ k η • twoTermGraphAmplitude c S U z η) v
  let g : ℕ → Euclidean n → Fin r → ℂ := fun k ↦ graphOperator (r := r) S (fun z _ η ↦ χ k η • U z η)
    (fun y ↦ -Complex.I • partialDeriv v y t)
  let q : ℕ → Euclidean n → Fin r → ℂ := fun k ↦ graphOperator (r := r) S (fun z _ η ↦ χ k η • twoTermGraphRemainder A B c S U z η) v
  have hO := (hreg 0).output_open
  have hf (k) : ContDiffOn ℝ ∞ (f k) O := by
    apply contDiffOn_graphOperator_of_compact (hreg k).output_open (hreg k).cutoff_compact
      (hreg k).phase_smooth (hreg k).amplitude_smooth _ hv hvK
    intro x _ η hη
    simp [image_eq_zero_of_notMem_tsupport hη]
  have hvd : ContDiff ℝ ∞ (fun y ↦ -Complex.I • partialDeriv v y t) := by
    exact ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).const_smul _
  have hvdK : HasCompactSupport (fun y ↦ -Complex.I • partialDeriv v y t) := by
    exact HasCompactSupport.smul_left (f := fun _ : Euclidean n ↦ -Complex.I)
      (hvK.fderiv_apply ℝ (EuclideanSpace.single t 1))
  have hg (k) : ContDiffOn ℝ ∞ (g k) O := by
    apply contDiffOn_graphOperator_of_compact (r := r) (S := S)
      (b := fun z η ↦ χ k η • U z η)
      (v := fun y ↦ -Complex.I • partialDeriv v y t)
      (hreg k).output_open (hreg k).cutoff_compact
      (hreg k).phase_smooth
      (((hreg k).cutoff_smooth.comp_contDiffOn contDiffOn_snd).smul (hreg k).transport_smooth)
      _ hvd hvdK
    intro x _ η hη
    simp [image_eq_zero_of_notMem_tsupport hη]
  have he (k x) (hx : x ∈ O) : physicalOperator A B (f k) x = g k x + q k x := by
    exact (sub_eq_iff_eq_add.mp ((hreg k).conjugation hv hvK hx)).trans (add_comm _ _)
  have hp (k i) : ContinuousOn (fun x ↦ physicalOperator A B (f k) x i) O :=
    continuousOn_physicalOperator_component (n := n) (r := r) (O := O) hO A B (fun j i l ↦ (hA j i l).continuousOn)
      (fun i l ↦ (hB i l).continuousOn) (hf k) i
  have hq (k i) : ContinuousOn (fun x ↦ q k x i) O := by
    apply ((hp k i).sub (contDiffOn_pi.mp (hg k) i).continuousOn).congr
    intro x hx
    have hh := congrFun (he k x hx) i
    simpa using (sub_eq_iff_eq_add.mpr (hh.trans (add_comm _ _))).symm
  intro φ hK hs i
  have hident (k) : (∫ x, φ x * physicalOperator A B (f k) x i) =
      (∫ x, φ x * g k x i) + (∫ x, φ x * q k x i) := by
    rw [← integral_add
      (integrable_local_graph_test_mul hO φ.continuous hK hs (contDiffOn_pi.mp (hg k) i).continuousOn)
      (integrable_local_graph_test_mul hO φ.continuous hK hs (hq k i))]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ O
    · simp only [he k x hx, Pi.add_apply, mul_add]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh))
      simp [hz]
  have ht := tendsto_physicalOperator_local_pairing (n := n) (r := r) (O := O) hO A B hA hB hf F hF φ hK hs i
  have hu := ((hG φ hK hs i).add (hR φ hK hs i)).congr (fun k ↦ (hident k).symm)
  exact sub_eq_iff_eq_add.mpr ((tendsto_nhds_unique ht hu).trans (add_comm _ _))

end JanetCartan.FourierIntegral
