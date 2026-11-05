module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.QuantitativeGaps
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Localizers.FrequencyGaps

/-!
# Uniform graph masks and actual amplitude-support gaps

The geometric inputs below are the actual inverse chart identities and low
mixed/first-jet bounds supplied by the parent graph construction. They do not
contain a gradient gap or kernel estimate. The assembly constructs the masks
and discharges their geometric separation before deriving a uniform gap for
the actual joint amplitude (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
open Set
namespace JanetCartan.FiniteChain.Graph
open FourierIntegral
variable {n : ℕ}

/-- Low geometry supplied by the forward inverse-chart construction, on its
actual conic domain `D` and input buffer `I`
(`app:ch_regular:eq:joint-stationary`). -/
structure ForwardChartControl (φ : Euclidean n → Euclidean n → ℝ)
    (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (I D : Set (Euclidean n × Euclidean n)) (A B : ℝ) : Prop where
  differentiable : ∀ u ξ, (u,ξ) ∈ D → DifferentiableAt ℝ (Function.uncurry φ) (u,ξ)
  relation : ∀ y η, (y,η) ∈ I → ForwardRelation φ y η (κ (y,η)).1 (κ (y,η)).2
  inverse_bound : ∀ y η, (y,η) ∈ I → ∀ u ξ, (u,ξ) ∈ D →
    ‖u-(κ (y,η)).1‖ ≤ A * ‖fderiv ℝ (φ u) η - fderiv ℝ (φ (κ (y,η)).1) η‖
  covector_variation : ∀ y η, (y,η) ∈ I → ∀ u ξ, (u,ξ) ∈ D →
    ‖fderiv ℝ (φ u) η - fderiv ℝ (φ u) ξ‖ ≤ B * ‖η-ξ‖
  base_variation : ∀ y η, (y,η) ∈ I → ∀ u ξ, (u,ξ) ∈ D →
    ‖fderiv ℝ (fun v => φ v η) (κ (y,η)).1 - fderiv ℝ (fun v => φ v ξ) u‖ ≤
      B * (‖u-(κ (y,η)).1‖ + ‖η-ξ‖)

/-- Low geometry supplied by the literal reverse inverse-chart construction.
The mixed inverse is in the covector variable at the input base
(`app:ch_regular:lem:finite-chain`). -/
structure ReverseChartControl (φ : Euclidean n → Euclidean n → ℝ)
    (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (I D : Set (Euclidean n × Euclidean n)) (A B : ℝ) : Prop where
  differentiable : ∀ u ξ, (u,ξ) ∈ D → DifferentiableAt ℝ (Function.uncurry φ) (u,ξ)
  relation : ∀ y η, (y,η) ∈ I → ForwardRelation φ (κ (y,η)).1 (κ (y,η)).2 y η
  inverse_bound : ∀ y η, (y,η) ∈ I → ∀ u ξ, (u,ξ) ∈ D →
    ‖ξ-(κ (y,η)).2‖ ≤ A *
      ‖fderiv ℝ (fun v => φ v ξ) y - fderiv ℝ (fun v => φ v (κ (y,η)).2) y‖
  base_variation : ∀ y η, (y,η) ∈ I → ∀ u ξ, (u,ξ) ∈ D →
    ‖fderiv ℝ (fun v => φ v ξ) y - fderiv ℝ (fun v => φ v ξ) u‖ ≤ B * ‖u-y‖
  covector_variation : ∀ y η, (y,η) ∈ I → ∀ u ξ, (u,ξ) ∈ D →
    ‖fderiv ℝ (φ y) (κ (y,η)).2 - fderiv ℝ (φ u) ξ‖ ≤
      B * (‖u-y‖ + ‖ξ-(κ (y,η)).2‖)

/-- The quantitative forward gap on the actual complementary amplitude support.
The geometric separation is produced by `exists_bufferedLocalizers_with_gap`;
the parent supplies only the low chart control and actual domain membership
(`app:ch_regular:lem:finite-chain`). -/
theorem ForwardChartControl.jointAmplitude_gap
    {φ : Euclidean n → Euclidean n → ℝ}
    {κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n}
    {I D : Set (Euclidean n × Euclidean n)} {A B : ℝ}
    (H : ForwardChartControl φ κ I D A B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {mi mo : LocalizerSymbol n} (hmi : tsupport mi ⊆ I) {δ : ℝ}
    (hgap : ∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1-mo q), δ ≤ dist (κ q) q')
    {r : ℕ} (ρ : ℝ) (a : FullAmplitude n r) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (p : JointVariables (Euclidean n))
    (hp : p ∈ tsupport (jointAmplitude ρ a mi mo χA χo x y))
    (hD : (p.1.1,p.2.1) ∈ D) :
    δ / graphGapConstant A B ≤ ‖fderiv ℝ (jointPhase false φ x y) p‖ := by
  obtain ⟨hi,ho⟩ := jointAmplitude_tsupport_subset ρ a mi mo χA χo x y hp
  have hI := hmi hi
  have hd := forward_chart_distance_le_jointDerivative φ x y p.1.1 p.1.2 p.2.1
    p.2.2.1 p.2.2.2 (κ (y,p.2.2.1)).1 (κ (y,p.2.2.1)).2
    (H.differentiable _ _ hD) (H.relation _ _ hI) hA hB
    (H.inverse_bound _ _ hI _ _ hD) (H.covector_variation _ _ hI _ _ hD)
    (H.base_variation _ _ hI _ _ hD)
  apply (div_le_iff₀ (graphGapConstant_pos hA hB)).mpr
  have hs := hgap _ hi _ ho
  rw [dist_comm] at hs
  simpa only [mul_comm] using hs.trans hd

/-- The literal reverse gap on the actual complementary amplitude support,
with the same explicit dependence on low geometry
(`app:ch_regular:lem:finite-chain`). -/
theorem ReverseChartControl.jointAmplitude_gap
    {φ : Euclidean n → Euclidean n → ℝ}
    {κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n}
    {I D : Set (Euclidean n × Euclidean n)} {A B : ℝ}
    (H : ReverseChartControl φ κ I D A B) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {mi mo : LocalizerSymbol n} (hmi : tsupport mi ⊆ I) {δ : ℝ}
    (hgap : ∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1-mo q), δ ≤ dist (κ q) q')
    {r : ℕ} (ρ : ℝ) (a : FullAmplitude n r) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) (p : JointVariables (Euclidean n))
    (hp : p ∈ tsupport (jointAmplitude ρ a mi mo χA χo x y))
    (hD : (p.1.1,p.2.1) ∈ D) :
    δ / graphGapConstant A B ≤ ‖fderiv ℝ (jointPhase true φ x y) p‖ := by
  obtain ⟨hi,ho⟩ := jointAmplitude_tsupport_subset ρ a mi mo χA χo x y hp
  have hI := hmi hi
  have hd := reverse_chart_distance_le_jointDerivative φ x y p.1.1 p.1.2 p.2.1
    p.2.2.1 p.2.2.2 (κ (y,p.2.2.1)).1 (κ (y,p.2.2.1)).2
    (H.differentiable _ _ hD) (H.relation _ _ hI) hA hB
    (H.inverse_bound _ _ hI _ _ hD) (H.base_variation _ _ hI _ _ hD)
    (H.covector_variation _ _ hI _ _ hD)
  apply (div_le_iff₀ (graphGapConstant_pos hA hB)).mpr
  have hs := hgap _ hi _ ho
  rw [dist_comm] at hs
  simpa only [mul_comm] using hs.trans hd

/-- Uniform buffered graph localizers and a positive gap for the actual packed
joint derivative on the actual complementary amplitude support. The common
compact image envelope protects all shoulders. The same `A,B` control the whole
phase family, so the gap depends only on this low geometry and the fixed chart
buffers. Parent obligations are the actual conic-domain control, common image
envelope, and (for application) amplitude support in that domain. No gradient
gap or kernel estimate is assumed (`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_bufferedLocalizers_joint_gap
    {P : Type*} (backward : Bool)
    {K I J O : Set (Euclidean n × Euclidean n)}
    (hK : IsCompact K) (hI : IsOpen I) (hKI : K ⊆ I)
    (hJ : IsCompact J) (hO : IsOpen O) (hJO : J ⊆ O)
    (φ : P → Euclidean n → Euclidean n → ℝ)
    (κ : P → (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
    (D : P → Set (Euclidean n × Euclidean n))
    (himage : ∀ t p, p ∈ I → κ t p ∈ J)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (H : ∀ t, if backward then ReverseChartControl (φ t) (κ t) I (D t) A B
      else ForwardChartControl (φ t) (κ t) I (D t) A B) :
    ∃ (mi mo : LocalizerSymbol n) (δ : ℝ), 0 < δ ∧
      IsBufferedLocalizer mi K I ∧ IsBufferedLocalizer mo J O ∧
      (∀ t q, q ∈ tsupport mi → κ t q ∈ interior {q | mo q = 1}) ∧
      ∀ t (r : ℕ) (ρ : ℝ) (a : FullAmplitude n r) (χA χo : Euclidean n → ℝ)
        (x y : Euclidean n) (p : JointVariables (Euclidean n)),
        p ∈ tsupport (jointAmplitude ρ a mi mo χA χo x y) →
        (p.1.1,p.2.1) ∈ D t →
        δ ≤ ‖fderiv ℝ (jointPhase backward (φ t) x y) p‖ := by
  obtain ⟨mi, mo, δ, hδ, hi, ho, hbuffer, hgap⟩ :=
    exists_bufferedLocalizers_of_image_envelope hK hI hKI hJ hO hJO κ himage
  refine ⟨mi, mo, δ / graphGapConstant A B,
    div_pos hδ (graphGapConstant_pos hA hB), hi, ho, hbuffer, ?_⟩
  intro t r ρ a χA χo x y p hp hD
  have hgap' : ∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1-mo q),
      δ ≤ dist (κ t q) q' := fun q hq q' hq' => (hgap t q hq q' hq').le
  cases backward
  · exact (H t).jointAmplitude_gap hA hB hi.support_subset hgap' ρ a χA χo x y p hp hD
  · exact (H t).jointAmplitude_gap hA hB hi.support_subset hgap' ρ a χA χo x y p hp hD

end JanetCartan.FiniteChain.Graph
