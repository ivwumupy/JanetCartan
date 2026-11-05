module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence.Comparison
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots

/-!
# Actual incidence roots for the selected quantitative carriers

Every analytic input of the finite root continuation theorem is discharged
from componentwise frame `C⁶` closeness on the compact construction ball.
The fixed chart family is preserved (`app:ch_seed:prop:seed-actual-menu`, Step 3).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open FrozenMenu CharacteristicRoot CurrentFullPhase

/-- The proved low-order conclusions for a constructed root family. This
predicate only packages output: `exists_constructed_incidence_roots` below
constructs its witnesses from primitive frame data
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def IsConstructedIncidenceRootFamily {n : ℕ} (D : CoverData n) (R : IncidenceRefinement D)
    (r c B ε : ℝ) (Q : Euclidean n → Fin n → MetricTensor n)
    (Θ : (b : Fin D.chartCount) → Fin (D.patchCount b) → Euclidean n → Euclidean 3 → ℝ)
    (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
      Euclidean n × Euclidean n → ℝ) : Prop :=
  ∀ j a,
    let V := ball (0 : Euclidean n) (3 * r) ×ˢ ball (R.center j) (2 * R.radius j)
    let z := D.roots (R.sourceChart j) a (R.center j)
    let f := currentIncidence Q (Θ (R.sourceChart j) a) z
    ContDiffOn ℝ ∞ (g j a) V ∧
    ContDiffOn ℝ ∞ (fun p ↦ incidenceParameter z (g j a p)) V ∧
    (∀ p ∈ V,
      g j a p ∈ Ioo (-R.halfWidth j a) (R.halfWidth j a) ∧
      incidenceParameter z (g j a p) ∈ parameterInterior (D.patches (R.sourceChart j) a).radius ∧
      incidenceParameter z (g j a p) 1 = 0 ∧
      incidenceParameter z (g j a p) 2 = 0 ∧
      f (p, g j a p) = 0 ∧
      c ≤ |scalarDerivative f (p, g j a p)| ∧
      ‖incidenceParameter z (g j a p) - D.roots (R.sourceChart j) a p.2‖ ≤ ε / c ∧
      ‖fderiv ℝ (g j a) p‖ ≤ ‖fderiv ℝ f (p, g j a p)‖ / c) ∧
    (∀ p ∈ V, ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a),
      f (p, t) = 0 ↔ g j a p = t) ∧
    (∀ p ∈ V, ‖fderiv ℝ (g j a) p‖ ≤ B)

/-- Construct the smaller fixed incidence cover and actual smooth roots for
the SAME quantitative carrier family. The construction discharges joint
smoothness, value comparison, scalar comparison and full derivative
comparison from primitive componentwise frame `C⁶` closeness. All constants
and the refinement precede the frame and higher norms; the supplied common
physical radius is preserved (`app:ch_seed:prop:seed-actual-menu`, Step 3).

The positive tolerance can subsequently be decreased to obtain the full
detector inequality at these very roots. -/
theorem exists_constructed_incidence_roots {n : ℕ} {D : CoverData n}
    {c₀ C₀ : ℝ} (hD : D.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {b r : ℝ} (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hframe : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆
      closedBall (0 : Euclidean n) b)
    (hr : ∀ i, 3 * r < (T i).physicalRadius) (hrb : 3 * r < b) :
    ∃ R : IncidenceRefinement D, R.IsValid ∧ ∃ η c B εmax : ℝ,
      0 < η ∧ 0 < c ∧ 0 < B ∧ 0 < εmax ∧
      (∀ j a, ∀ t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a), ∀ i : Fin 3,
        |incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) t i| + η <
          (D.patches (R.sourceChart j) a).radius) ∧
      ∀ ε, 0 < ε → ε ≤ εmax → ∃ δ > (0 : ℝ),
      ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U),
        (∀ j, cNorm (closedBall (0 : Euclidean n) b) 6
          (fun x ↦ Q x j - cubeStress n j) < δ) →
        ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
            (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) <
              (T i).family.threshold,
        ∃ g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
            Euclidean n × Euclidean n → ℝ,
          IsConstructedIncidenceRootFamily D R r c B ε Q
            (fun j a ↦ (T ⟨j, a⟩).carrier ⟨Q, hQ, hlow ⟨j, a⟩⟩) g := by
  classical
  obtain ⟨R, hR, η, c, B, εmax, hη, hc, hB, hemax, hbuffer, hroots⟩ :=
    exists_uniform_current_incidence_roots hD
  refine ⟨R, hR, η, c, B, εmax, hη, hc, hB, hemax, hbuffer, ?_⟩
  intro ε hε he
  let J := (j : Fin D.chartCount) × Fin (D.patchCount j)
  let I := (j : Fin R.chartCount) × Fin (D.patchCount (R.sourceChart j))
  have hP (i : J) := (hD.2.2.2.2.1 i.1 i.2).1
  choose d hd hcomp using fun i : I ↦
    (T ⟨R.sourceChart i.1, i.2⟩).exists_current_incidence_comparison_threshold
      (hP ⟨R.sourceChart i.1, i.2⟩) hBU (hframe _) (hr _) hrb
      (R.center i.1) (R.radius i.1) (D.roots (R.sourceChart i.1) i.2 (R.center i.1))
      (R.halfWidth i.1 i.2)
      (fun t ht l ↦ ((hR.2.2.2 i.1 i.2).2.2.2.1 t ht l).le) hε
  obtain ⟨d₁, hd₁, hd₁i⟩ := Pi.exists_forall_pos_add_lt hd
  obtain ⟨d₂, hd₂, hd₂i⟩ := Pi.exists_forall_pos_add_lt
    (fun i : J ↦ (T i).family.threshold_pos)
  let d₀ := min d₁ d₂
  have hd₀ : 0 < d₀ := lt_min hd₁ hd₂
  refine ⟨d₀ / 14, by positivity, fun Q hQ hclose ↦ ?_⟩
  have hreg : ∀ x ∈ closedBall (0 : Euclidean n) b,
      ContDiffAt ℝ 6 (Q - fun _ ↦ cubeStress n) x := fun x hx ↦
    ((hQ.contDiffAt (hU.mem_nhds (hBU hx))).sub contDiffAt_const).of_le (by simp)
  have hglobal : cNorm (closedBall (0 : Euclidean n) b) 6 (Q - fun _ ↦ cubeStress n) < d₀ := by
    apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _) hreg hd₀
    convert hclose using 1; norm_num
  have hlow (i : J) : cNorm (closedBall (0 : Euclidean n)
      (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) <
        (T i).family.threshold := by
    have hi : d₂ < (T i).family.threshold := by simpa using hd₂i i
    exact (cNorm_mono_set_of_contDiffAt (hframe i) (isCompact_closedBall _ _) hreg).trans_lt
      ((hglobal.trans_le (min_le_right _ _)).trans hi)
  let Θ := fun j a ↦ (T ⟨j, a⟩).carrier ⟨Q, hQ, hlow ⟨j, a⟩⟩
  have hh (j a) (p : Euclidean n × Euclidean n)
      (hp : p ∈ ball (0 : Euclidean n) (3 * r) ×ˢ ball (R.center j) (2 * R.radius j))
      (t : ℝ) (ht : t ∈ Icc (-R.halfWidth j a) (R.halfWidth j a)) :=
    hcomp ⟨j, a⟩ ⟨Q, hQ, hlow ⟨R.sourceChart j, a⟩⟩
      ((hglobal.trans_le (min_le_left _ _)).trans (by simpa using hd₁i ⟨j, a⟩))
      p ⟨ball_subset_closedBall hp.1, ball_subset_closedBall hp.2⟩ t ht
  obtain ⟨g, hg⟩ := hroots (ball (0 : Euclidean n) (3 * r)) isOpen_ball Q Θ ε hε.le he
    (fun j a p hp t ht ↦ (hh j a p hp t ht).1)
    (fun j a p hp t ht ↦ ⟨(hh j a p hp t ht).2.1.le, (hh j a p hp t ht).2.2.1.le⟩)
    (fun j a p hp t ht ↦ (hh j a p hp t ht).2.2.2.le)
  exact ⟨hlow, g, hg⟩

end JanetCartan.ActualCarriers
