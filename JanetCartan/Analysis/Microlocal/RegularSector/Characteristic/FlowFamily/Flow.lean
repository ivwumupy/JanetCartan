module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.FlowFamily.FieldJets
public import JanetCartan.Analysis.ODE.FlowStability
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FlowJetBounds

/-!
# A common root-Hamilton flow with single-high joint budgets

The flow part of `paper-v2.tex`, `app:ch_regular_base:lem:characteristic-kernel`.
The closed state ball and scalar root's finite low budget determine a positive
time interval before the root is chosen. Picard–Lindelöf constructs the actual
flow on this cylinder. All orders are estimated for that same flow, with one
derivative of reserve, by the genuine ODE estimates of `FlowJetBounds`.

The low root order is three, also allowing a uniform second-order flow budget
for the inverse projection construction. Neither a flow nor any flow estimate
is an input to the construction. Homogeneity is only needed later for the phase.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology NNReal

namespace JanetCartan.RegularSector.Characteristic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance rootFlowFamilyNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace

/-- Fixed scalar `C³` control implies both the value and Lipschitz bounds
needed by Picard–Lindelöf; there is no field-bound premise
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem rootHamiltonField_bounds_of_cNorm_three
    {D : Set (RootState E)} (hD : IsOpen D) {z : RootState E} {R M : ℝ}
    (hRD : closedBall z R ⊆ D) (hM : 0 ≤ M)
    {h : RootState E → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hlow : cNorm (closedBall z R) 3 h ≤ M) :
    LipschitzOnWith ⟨2 * (1 + M), by positivity⟩ (rootHamiltonField h) (closedBall z R) ∧
      ∀ w ∈ closedBall z R, ‖rootHamiltonField h w‖ ≤ 2 * (1 + M) := by
  have hV := contDiffOn_rootHamiltonField hD hh
  have hVat (w) (hw : w ∈ closedBall z R) : ContDiffAt ℝ 1 (rootHamiltonField h) w :=
    (hV.contDiffAt (hD.mem_nhds (hRD hw))).of_le (by simp)
  have hnorm : cNorm (closedBall z R) 1 (rootHamiltonField h) ≤ 2 * (1 + M) := by
    have hb := cNorm_rootHamiltonField_le hD (isCompact_closedBall z R) hRD 1
      (hh.of_le (by simp))
    have hl := (cNorm_mono_order (f := h) (s := closedBall z R) (by norm_num : 2 ≤ 3)).trans hlow
    norm_num at hb
    linarith
  have hv (w) (hw : w ∈ closedBall z R) :
      ‖rootHamiltonField h w‖ ≤ 2 * (1 + M) ∧
        ‖fderiv ℝ (rootHamiltonField h) w‖ ≤ 2 * (1 + M) := by
    constructor
    · have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall z R)
        hVat hw (show 0 ≤ 1 by omega)
      simpa only [norm_iteratedFDeriv_zero] using hb.trans hnorm
    · have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall z R)
        hVat hw (show 1 ≤ 1 from le_rfl)
      simpa only [norm_iteratedFDeriv_one] using hb.trans hnorm
  refine ⟨(convex_closedBall z R).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun w hw ↦ (hVat w hw).differentiableAt (by simp)) ?_, fun w hw ↦ (hv w hw).1⟩
  intro w hw
  exact_mod_cast (hv w hw).2

/-- Every actual smooth flow on the prescribed cylinder has a single-high
joint budget, with scalar-root reserve one. The constant precedes both the
root and the flow. This is consumed by `exists_common_rootHamiltonFlow` and
the common inverse projection construction
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_rootHamiltonFlow_cNorm_bound
    (z : RootState E) {R T M : ℝ} (hR : 0 < R) (hT : 0 < T) (hM : 0 ≤ M)
    {D : Set (RootState E)} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ (h : RootState E → ℝ) (Φ : RootState E × ℝ → RootState E),
      ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
      ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ →
      cNorm (closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ ≤
        C * (1 + cNorm (closedBall z R) (n + 1) h) := by
  let K := closedBall z (R / 4)
  let N := cNorm K 1 (id : RootState E → RootState E)
  let A := cNorm K n (id : RootState E → RootState E)
  have hN : 0 ≤ N := cNorm_nonneg _ _ _
  have hA : 0 ≤ A := cNorm_nonneg _ _ _
  obtain ⟨B, hB, hbound⟩ := HamiltonPhase.exists_autonomousFlow_joint_cNorm_bound
    z z (by positivity : 0 < R / 4) (by linarith : R / 4 < R / 2) hR
    (div_pos hT hR) (by norm_num : (1 : ℝ) < 2) hD hRD 0
    (show 0 ≤ 2 * (1 + M) by positivity) hN n
  refine ⟨B * (1 + (n + 1 : ℝ) + A), by positivity, ?_⟩
  intro h Φ hh hlow hΦ
  have houter : T / R * 2 * (R / 2) = T := by field_simp
  have hinner : T / R * (R / 4) = T / 4 := by field_simp
  have hfield := cNorm_rootHamiltonField_le hD (isCompact_closedBall z R) hRD 1
    (hh.of_le (by simp))
  have hl := (cNorm_mono_order (f := h) (s := closedBall z R) (by norm_num : 2 ≤ 3)).trans hlow
  have hb := hbound (rootHamiltonField h) id Φ (contDiffOn_rootHamiltonField hD hh)
    contDiffOn_id (by simpa only [houter, zero_sub, zero_add] using hΦ.smooth)
    (by norm_num at hfield; linarith) le_rfl
    (fun w hw ↦ hΦ.initial w (ball_subset_closedBall hw))
    (fun w hw u hu ↦ hΦ.hasDerivAt (ball_subset_closedBall hw)
      (by simpa only [houter, zero_sub, zero_add] using hu))
    (fun w hw u hu ↦ hΦ.range w
      (closedBall_subset_closedBall (by linarith) hw) u
      (Ioo_subset_Icc_self (by simpa only [houter, zero_sub, zero_add] using hu)))
  simp only [hinner, zero_sub, zero_add] at hb
  have hn := cNorm_rootHamiltonField_le hD (isCompact_closedBall z R) hRD n
    (hh.of_le (by simp))
  have hhigh := cNorm_nonneg (closedBall z R) (n + 1) h
  have hb' : 1 + cNorm (closedBall z R) n (rootHamiltonField h) + A ≤
      (1 + (n + 1 : ℝ) + A) * (1 + cNorm (closedBall z R) (n + 1) h) := by
    nlinarith
  calc
    _ ≤ B * (1 + cNorm (closedBall z R) n (rootHamiltonField h) + A) := by
      simpa only [neg_div] using hb
    _ ≤ B * ((1 + (n + 1 : ℝ) + A) * (1 + cNorm (closedBall z R) (n + 1) h)) :=
      mul_le_mul_of_nonneg_left hb' hB.le
    _ = _ := by ring

/-- Construct actual Hamilton flows on common closed cylinders from the fixed
root `C³` budget. The time, initial radius and all constants precede the root;
one flow is chosen before all derivative orders. Its ODE, full closed range,
initial condition and variational equation are retained in `IsSmoothFlowOn`.
The inner joint budgets have fixed reserve one
(`app:ch_regular_base:lem:characteristic-kernel`,
`app:ch_regular_base:lem:retarded-kernel`). -/
theorem exists_common_rootHamiltonFlow
    (z : RootState E) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    {D : Set (RootState E)} (hD : IsOpen D) (hRD : closedBall z R ⊆ D) :
    ∃ T > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ n, 0 < C n) ∧
      ∀ h : RootState E → ℝ, ContDiffOn ℝ ∞ h D → cNorm (closedBall z R) 3 h ≤ M →
        ∃ Φ : RootState E × ℝ → RootState E,
          ODE.IsSmoothFlowOn (rootHamiltonField h) z R (R / 2) T Φ ∧
          ∀ n, cNorm (closedBall z (R / 4) ×ˢ Icc (-T / 4) (T / 4)) n Φ ≤
            C n * (1 + cNorm (closedBall z R) (n + 1) h) := by
  let L : ℝ≥0 := ⟨2 * (1 + M), by positivity⟩
  let T := R / (2 * (L : ℝ))
  have hL : 0 < (L : ℝ) := by change 0 < 2 * (1 + M); linarith
  have hT : 0 < T := div_pos hR (mul_pos (by norm_num) hL)
  choose C hC hbound using fun n ↦ exists_rootHamiltonFlow_cNorm_bound z hR hT hM hD hRD n
  refine ⟨T, hT, C, hC, ?_⟩
  intro h hh hlow
  obtain ⟨hlip, hfield⟩ := rootHamiltonField_bounds_of_cNorm_three hD hRD hM hh hlow
  have htime : (L : ℝ) * T ≤ R - R / 2 := by
    dsimp [T]
    have he : (L : ℝ) * (R / (2 * (L : ℝ))) = R / 2 := by field_simp
    rw [he]; linarith
  obtain ⟨Φ, hΦ⟩ := ODE.exists_smoothFlowOn_of_bounds (L := L) hD hRD
    (contDiffOn_rootHamiltonField hD hh) hR.le (by positivity) hT hlip hfield htime
  exact ⟨Φ, hΦ, fun n ↦ hbound n h Φ hh hlow hΦ⟩

end JanetCartan.RegularSector.Characteristic
