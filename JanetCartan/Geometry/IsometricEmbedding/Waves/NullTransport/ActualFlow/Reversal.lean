module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.UniformExistence
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FlowJetBounds

/-!
# Quantitative reversal of the constructed characteristic flow

For `app:ch_waves:thm:leading`, uniqueness identifies the backwards trajectory
with the actual inverse. The time and state buffers depend only on the
zeroth and first derivative bounds of the vector field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff NNReal
namespace JanetCartan.NullTransport.ActualFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ODE uniqueness cancels a forward trajectory with its backwards trajectory.
The consumer is `buffered_footpoint_chart` (`app:ch_waves:thm:leading`). -/
theorem reverse_flow_eq {V : E → E} {Ψ : E × ℝ → E}
    {q₀ : E} {R ε : ℝ} {M : ℝ≥0} (hε : 0 < ε)
    (hlip : LipschitzOnWith M V (closedBall q₀ R))
    (hi : ∀ q ∈ closedBall q₀ (R / 2), Ψ (q, 0) = q)
    (hd : ∀ q ∈ closedBall q₀ (R / 2), ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s ↦ Ψ (q, s)) (V (Ψ (q, t))) t)
    (hr : ∀ q ∈ closedBall q₀ (R / 2), ∀ t ∈ Ioo (-ε) ε,
      Ψ (q, t) ∈ closedBall q₀ R)
    {q : E} (hq : q ∈ closedBall q₀ (R / 2))
    {t : ℝ} (ht : t ∈ Ioo (-ε / 2) (ε / 2))
    (hqt : Ψ (q, t) ∈ closedBall q₀ (R / 2)) : Ψ (Ψ (q, t), -t) = q := by
  have hs {s : ℝ} (hs : s ∈ Ioo (-ε / 2) (ε / 2)) : s ∈ Ioo (-ε) ε := by
    constructor <;> linarith [hs.1, hs.2]
  have hst {s : ℝ} (hs : s ∈ Ioo (-ε / 2) (ε / 2)) : t + s ∈ Ioo (-ε) ε := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have heq := ODE_solution_unique_of_mem_Ioo (v := fun _ ↦ V)
    (s := fun _ ↦ closedBall q₀ R) (f := fun s ↦ Ψ (Ψ (q, t), s))
    (g := fun s ↦ Ψ (q, t + s)) (fun _ _ ↦ hlip)
    (show (0 : ℝ) ∈ Ioo (-ε / 2) (ε / 2) by constructor <;> linarith)
    (fun s h ↦ ⟨hd _ hqt s (hs h), hr _ hqt s (hs h)⟩)
    (fun s h ↦ ⟨by
      simpa only [Function.comp_def, one_smul] using (hd q hq (t + s) (hst h)).scomp s
        ((hasDerivAt_id s).const_add t), hr q hq (t + s) (hst h)⟩)
    (by simp only [add_zero, hi _ hqt])
  have h := heq (show -t ∈ Ioo (-ε / 2) (ε / 2) by constructor <;> linarith [ht.1, ht.2])
  simpa only [add_neg_cancel, hi q hq] using h

/-- The state displacement is controlled by the value bound, also backwards
in time. Used by `buffered_footpoint_chart` (`app:ch_waves:thm:leading`). -/
theorem flow_displacement_le {V : E → E} {Ψ : E × ℝ → E}
    {q₀ : E} {R ε M : ℝ} (hε : 0 < ε)
    (hv : ∀ q ∈ closedBall q₀ R, ‖V q‖ ≤ M)
    (hi : ∀ q ∈ closedBall q₀ (R / 2), Ψ (q, 0) = q)
    (hd : ∀ q ∈ closedBall q₀ (R / 2), ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s ↦ Ψ (q, s)) (V (Ψ (q, t))) t)
    (hr : ∀ q ∈ closedBall q₀ (R / 2), ∀ t ∈ Ioo (-ε) ε,
      Ψ (q, t) ∈ closedBall q₀ R)
    {q : E} (hq : q ∈ closedBall q₀ (R / 2))
    {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : dist (Ψ (q, t)) q ≤ M * |t| := by
  have hseg := ordConnected_Ioo.uIcc_subset
    (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨neg_neg_of_pos hε, hε⟩) ht
  simpa only [hi q hq, sub_zero] using HamiltonPhase.autonomousFlow_time_dist_le
    (fun s hs ↦ hd q hq s (hseg hs))
    (fun s hs ↦ hv _ (hr q hq s (hseg hs)))

/-- The explicit existence time respects both geometric and displacement
buffers (`app:ch_waves:thm:leading`). -/
theorem existenceTime_le {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) :
    existenceTime R M ≤ R / 4 ∧ M * existenceTime R M ≤ R / 4 := by
  have hden : 0 < 4 * (M + 1) := by positivity
  constructor
  · unfold existenceTime
    rw [div_le_iff₀ hden]
    nlinarith
  · unfold existenceTime
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith

end JanetCartan.NullTransport.ActualFlow
