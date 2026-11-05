module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RootFamily.Bounds

/-!
# Fixed nested state buffers for the uniform pencil root

For `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:lem:retarded-kernel`, the physical coefficient ball and
the normalized covector patch determine a positive state radius before the
field varies. The three concentric state balls remain in the same root
domain, their physical projections remain in the prescribed coefficient
ball, and their radial coordinate stays at least one half. This last bound
converts the normalized gaps to actual gaps for the amplitude consumer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.RootFamily

open AmplitudeBounds

variable {n d : ℕ}

/-- The nested state buffers and the radial lower bound are constructed
before `Q`. The outer ball supplies the joint seminorm domain for the actual
flow and amplitude inputs (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_fieldRoot_buffers
    (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    {Ω : Set (Euclidean n)} (hΩ : IsOpen Ω)
    (x : Euclidean n) {R : ℝ} (hR : 0 < R) (hKΩ : closedBall x R ⊆ Ω)
    (ℓ : Euclidean d →L[ℝ] ℝ) (η₀ : Euclidean d) (hℓ : ℓ η₀ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > (0 : ℝ),
      ∀ w ∈ closedBall ((e x).1, ((e x).2, η₀)) (3 * ρ),
        w ∈ fieldDomain e Ω ℓ η₀ ε ∧
        rootPhysicalPosition e w ∈ closedBall x R ∧
        w.2.2 ∈ closedBall η₀ ε ∧ (1 / 2 : ℝ) ≤ ℓ w.2.2 := by
  let z : RootState (Euclidean d) := ((e x).1, ((e x).2, η₀))
  let L := rootPhysicalPosition e
  let η : RootState (Euclidean d) → Euclidean d := fun w ↦ w.2.2
  let S := ((fieldDomain e Ω ℓ η₀ ε ∩ L ⁻¹' ball x R) ∩
    η ⁻¹' ball η₀ ε) ∩ {w | (1 / 2 : ℝ) < ℓ (η w)}
  have hη : Continuous η := continuous_snd.snd
  have hS : IsOpen S :=
    (((isOpen_fieldDomain e hΩ ℓ η₀ ε).inter
      (isOpen_ball.preimage L.continuous)).inter (isOpen_ball.preimage hη)).inter
        (isOpen_lt continuous_const (ℓ.continuous.comp hη))
  have hzD : z ∈ fieldDomain e Ω ℓ η₀ ε := by
    refine ⟨by simpa only [z, hℓ] using zero_lt_one, ?_, ?_⟩
    · simpa only [z, Prod.eta, e.symm_apply_apply] using
        hKΩ (mem_closedBall_self hR.le)
    · simpa only [z, hℓ, inv_one, one_smul] using mem_ball_self hε
  have hLz : L z = x := e.symm_apply_apply x
  have hzS : z ∈ S := by
    refine ⟨⟨⟨hzD, ?_⟩, mem_ball_self hε⟩, ?_⟩
    · change L z ∈ ball x R
      rw [hLz]
      exact mem_ball_self hR
    · change (1 / 2 : ℝ) < ℓ η₀
      rw [hℓ]
      norm_num
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hzS)
  refine ⟨a / 4, by positivity, ?_⟩
  intro w hw
  have hwS : w ∈ S := hball (mem_ball.mpr (by
    have hd := mem_closedBall.mp hw
    change dist w z ≤ 3 * (a / 4) at hd
    linarith))
  exact ⟨hwS.1.1.1, ball_subset_closedBall hwS.1.1.2,
    ball_subset_closedBall hwS.1.2, hwS.2.le⟩

end JanetCartan.RegularSector.Characteristic.RootFamily
