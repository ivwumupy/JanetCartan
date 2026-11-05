module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Detection

import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FunProp

/-!
# Full detection at supplied actual carrier roots

The continuity argument in Step 3 of `app:ch_seed:prop:seed-actual-menu`.
Small frame, carrier-value, and root-position errors preserve the full detector
inequality `app:ch_seed:eq:seed-actual-detection`. The quadratic vectors in the
conclusion are evaluated literally at the supplied actual carriers and roots.

The frozen compact boxes, continuous carriers and root sections, and common-kernel
detection are inputs. Constructing actual roots, proving incidence, and obtaining
the phase and frame comparison estimates remain the producer's responsibilities.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology
open Set Filter

namespace JanetCartan.ActualCarriers

variable {n : ℕ} {ι : Type*} [Fintype ι]

private theorem rootDetection_continuous_pencil :
    Continuous (fun p : (Fin n → MetricTensor n) × Euclidean n ↦ pencil p.1 p.2) := by
  unfold pencil
  fun_prop

private theorem rootDetection_continuous_quadratic :
    Continuous (fun p : (Fin n → MetricTensor n) × Euclidean n ↦ quadratic p.1 p.2) := by
  unfold quadratic
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

/-- The evaluated quadratic carrier list is uniformly close when the frame,
carrier values on the fixed compact boxes, and root positions are close.
This supplies the quadratic-vector input to `exists_uniform_detection_at_supplied_roots`
in Step 3 of `app:ch_seed:prop:seed-actual-menu`; no detector inequality is assumed. -/
theorem exists_uniform_root_quadratic_perturbation_radius
    (Q₀ : Fin n → MetricTensor n) (B : ι → Set (Euclidean 3))
    (hB : ∀ a, IsCompact (B a)) (ξ₀ : ι → Euclidean 3 → Euclidean n)
    (hξ₀ : ∀ a, ContinuousOn (ξ₀ a) (B a)) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (Q : Fin n → MetricTensor n) (ξ : ι → Euclidean 3 → Euclidean n)
        (z₀ z : ι → Euclidean 3),
        (∀ a, z₀ a ∈ B a) → (∀ a, z a ∈ B a) →
        ‖Q - Q₀‖ < ε → (∀ a, ∀ w ∈ B a, ‖ξ a w - ξ₀ a w‖ < ε) →
        (∀ a, ‖z a - z₀ a‖ < ε) →
        ‖(fun a ↦ quadratic Q (ξ a (z a))) -
          (fun a ↦ quadratic Q₀ (ξ₀ a (z₀ a)))‖ < η := by
  let Z : Set (ι → Euclidean 3) := {z | ∀ a, z a ∈ B a}
  let E : (ι → Euclidean 3) → (ι → Euclidean n) := fun z a ↦ ξ₀ a (z a)
  have hZ : IsCompact Z := isCompact_pi_infinite hB
  have hE : ContinuousOn E Z := by
    apply continuousOn_pi.mpr
    intro a
    exact (hξ₀ a).comp (continuous_apply a).continuousOn (fun _ hz ↦ hz a)
  have hV : IsCompact (E '' Z) := hZ.image_of_continuousOn hE
  let F : ((Fin n → MetricTensor n) × (ι → Euclidean n)) ×
      (ι → Euclidean n) → ℝ := fun p ↦
    ‖(fun a ↦ quadratic (Q₀ + p.1.1) (p.2 a + p.1.2 a)) -
      (fun a ↦ quadratic Q₀ (p.2 a))‖
  have hF : Continuous F := by
    apply Continuous.norm
    apply Continuous.sub <;> apply continuous_pi <;> intro a
    · exact (rootDetection_continuous_quadratic (n := n)).comp
        (f := fun p : ((Fin n → MetricTensor n) × (ι → Euclidean n)) ×
          (ι → Euclidean n) ↦ (Q₀ + p.1.1, p.2 a + p.1.2 a))
        ((continuous_const.add continuous_fst.fst).prodMk
          (((continuous_apply a).comp continuous_snd).add
            ((continuous_apply a).comp continuous_fst.snd)))
    · exact (rootDetection_continuous_quadratic (n := n)).comp
        (f := fun p : ((Fin n → MetricTensor n) × (ι → Euclidean n)) ×
          (ι → Euclidean n) ↦ (Q₀, p.2 a))
        (continuous_const.prodMk ((continuous_apply a).comp continuous_snd))
  have hev : ∀ᶠ e in 𝓝 (0 : (Fin n → MetricTensor n) × (ι → Euclidean n)),
      ∀ v ∈ E '' Z, F (e, v) < η := by
    apply hV.eventually_forall_of_forall_eventually
    intro v _
    have hz : F (0, v) < η := by simpa [F] using hη
    exact (hF.continuousAt (x := (0, v))).eventually (gt_mem_nhds hz)
  obtain ⟨δ, hδ, hclose⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨ρ, hρ, hroot⟩ := Metric.uniformContinuousOn_iff.mp
    (hZ.uniformContinuousOn_of_continuous hE) (δ / 2) (half_pos hδ)
  refine ⟨min (δ / 2) ρ, lt_min (half_pos hδ) hρ, ?_⟩
  intro Q ξ z₀ z hz₀ hz hQ hξ hzclose
  have hzz : dist z z₀ < ρ := by
    rw [dist_eq_norm]
    exact (pi_norm_lt_iff hρ).mpr (fun a ↦ (hzclose a).trans_le (min_le_right _ _))
  have hEclose : ‖E z - E z₀‖ < δ / 2 := by
    simpa only [dist_eq_norm] using hroot z hz z₀ hz₀ hzz
  have hξclose : ‖(fun a ↦ ξ a (z a)) - E z‖ < δ / 2 := by
    exact (pi_norm_lt_iff (half_pos hδ)).mpr
      (fun a ↦ (hξ a (z a) (hz a)).trans_le (min_le_left _ _))
  have hvclose : ‖(fun a ↦ ξ a (z a)) - E z₀‖ < δ := by
    calc
      _ ≤ ‖(fun a ↦ ξ a (z a)) - E z‖ + ‖E z - E z₀‖ := by
        simpa only [dist_eq_norm] using dist_triangle (fun a ↦ ξ a (z a)) (E z) (E z₀)
      _ < δ / 2 + δ / 2 := add_lt_add hξclose hEclose
      _ = δ := add_halves δ
  have heclose : dist (Q - Q₀, (fun a ↦ ξ a (z a)) - E z₀) 0 < δ := by
    rw [dist_eq_norm, sub_zero, Prod.norm_def]
    exact max_lt (hQ.trans_le ((min_le_left _ _).trans (half_le_self hδ.le))) hvclose
  have h := hclose heclose (E z₀) ⟨z₀, hz₀, rfl⟩
  simpa [F, ← add_sub_assoc, E] using h

/-- Full detector stability at supplied actual roots, uniformly over the compact
direction set and every physical/family index. This is precisely the concluding
continuity deduction of Step 3 of `app:ch_seed:prop:seed-actual-menu`, giving
`app:ch_seed:eq:seed-actual-detection` with the literal actual pencil and quadratic
carriers. The inputs are frozen common-kernel detection and small frame,
carrier-value, and root-position errors. Actual root existence, incidence, and
the estimates producing those errors are not asserted here. -/
theorem exists_uniform_detection_at_supplied_roots
    (Q₀ : Fin n → MetricTensor n) {K : Set (Euclidean n)} (hK : IsCompact K)
    (B : ι → Set (Euclidean 3)) (hB : ∀ a, IsCompact (B a))
    (ξ₀ : ι → Euclidean 3 → Euclidean n) (hξ₀ : ∀ a, ContinuousOn (ξ₀ a) (B a))
    (z₀ : ι → Euclidean n → Euclidean 3) (hz₀ : ∀ a, ContinuousOn (z₀ a) K)
    (hz₀B : ∀ a, ∀ k ∈ K, z₀ a k ∈ B a)
    (hdet : ∀ k ∈ K, ∀ s, imageChannel (pencil Q₀ k) s = 0 →
      (∀ a, ⟪quadratic Q₀ (ξ₀ a (z₀ a k)), s⟫_ℝ = 0) → s = 0) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
      ∀ {X : Type*} (Q : X → Fin n → MetricTensor n)
        (ξ : X → ι → Euclidean 3 → Euclidean n)
        (z : X → ι → Euclidean n → Euclidean 3),
        (∀ x a, ∀ k ∈ K, z x a k ∈ B a) →
        (∀ x, ‖Q x - Q₀‖ < ε) →
        (∀ x a, ∀ w ∈ B a, ‖ξ x a w - ξ₀ a w‖ < ε) →
        (∀ x a, ∀ k ∈ K, ‖z x a k - z₀ a k‖ < ε) →
        ∀ x, ∀ k ∈ K, ∀ s : Euclidean n,
          c * ‖s‖ ^ 2 ≤ ‖imageChannel (pencil (Q x) k) s‖ ^ 2 +
            ∑ a, ⟪quadratic (Q x) (ξ x a (z x a k)), s⟫_ℝ ^ 2 := by
  let D : Euclidean n → MetricTensor n × (ι → Euclidean n) := fun k ↦
    (pencil Q₀ k, fun a ↦ quadratic Q₀ (ξ₀ a (z₀ a k)))
  have hD : ContinuousOn D K := by
    apply ContinuousOn.prodMk
    · exact ((rootDetection_continuous_pencil (n := n)).comp
        (continuous_const.prodMk continuous_id)).continuousOn
    · apply continuousOn_pi.mpr
      intro a
      exact (rootDetection_continuous_quadratic (n := n)).continuousOn.comp
        (f := fun k ↦ (Q₀, ξ₀ a (z₀ a k)))
        (continuousOn_const.prodMk ((hξ₀ a).comp (hz₀ a) (hz₀B a)))
        (fun _ _ ↦ mem_univ _)
  obtain ⟨c, δ, hc, hδ, hgap⟩ := exists_uniform_detection_perturbation_radius
    (hK.image_of_continuousOn hD) (by
      rintro p ⟨k, hk, rfl⟩
      exact hdet k hk)
  obtain ⟨εq, hεq, hquad⟩ := exists_uniform_root_quadratic_perturbation_radius
    Q₀ B hB ξ₀ hξ₀ hδ
  have hcont : Continuous (fun p : (Fin n → MetricTensor n) × Euclidean n ↦
      ‖pencil p.1 p.2 - pencil Q₀ p.2‖) := by
    exact ((rootDetection_continuous_pencil (n := n)).sub
      ((rootDetection_continuous_pencil (n := n)).comp (continuous_const.prodMk continuous_snd))).norm
  have hev : ∀ᶠ Q in 𝓝 Q₀, ∀ k ∈ K, ‖pencil Q k - pencil Q₀ k‖ < δ := by
    apply hK.eventually_forall_of_forall_eventually
    intro k _
    have hz : ‖pencil Q₀ k - pencil Q₀ k‖ < δ := by simpa using hδ
    exact (hcont.continuousAt (x := (Q₀, k))).eventually (gt_mem_nhds hz)
  obtain ⟨εM, hεM, hpencil⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨c, min εM εq, hc, lt_min hεM hεq, ?_⟩
  intro X Q ξ z hzB hQ hξ hz x k hk s
  apply hgap (D k) ⟨k, hk, rfl⟩ (pencil (Q x) k)
    (fun a ↦ quadratic (Q x) (ξ x a (z x a k)))
  · apply hpencil _ k hk
    simpa only [dist_eq_norm] using (hQ x).trans_le (min_le_left _ _)
  · exact hquad (Q x) (ξ x) (fun a ↦ z₀ a k) (fun a ↦ z x a k)
      (fun a ↦ hz₀B a k hk) (fun a ↦ hzB x a k hk)
      ((hQ x).trans_le (min_le_right _ _))
      (fun a w hw ↦ (hξ x a w hw).trans_le (min_le_right _ _))
      (fun a ↦ (hz x a k hk).trans_le (min_le_right _ _))

end JanetCartan.ActualCarriers
