module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Physical
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Multiplier
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.ActualTerminal

/-! # Ordinary localizer bound for the bounded-frequency terminal range

The uncut kernel jets give the ordinary Sobolev estimate needed below the
angular cancellation threshold in `app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open FourierIntegral FiniteChain.Graph LowBounds Pseudodifferential
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The original right localizer maps all L² data to Hᵐ with a fixed
`ρ^(n+m)` loss. The proof uses the actual uncut compact-frequency kernel;
this supplies the bounded-frequency range of the full terminal defect
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_leftLocalizer_adjoint_sobolev_bound
    (mi : LocalizerSymbol n) (hi : ContDiff ℝ ∞ mi) (his : HasCompactSupport mi)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ M : H →L[ℂ] H,
      (∀ u : H, (∀ i, Integrable (fun y ↦ u y i)) → M u =ᵐ[volume]
        fun x ↦ WithLp.toLp 2 (leftLocalizer ρ mi (fun y ↦ (u y).ofLp) x)) →
      ∀ u : H, MemVectorFourierSobolev (m : ℝ) (M.adjoint u) ∧
        vectorFourierSobolevNorm (m : ℝ) (M.adjoint u) ≤ C * ρ ^ (n + m) * ‖u‖ := by
  obtain ⟨A, hA, ha⟩ := exists_rightLocalizerScalarKernel_jet_decay mi hi his m (n + 1)
  obtain ⟨S, hS, hs⟩ := exists_leftLocalizer_adjoint_physicalTail_sobolev_constant
    (n := n) (r := r) m
  let c : ℝ := min 1 (1 / (2 * Real.pi))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨S * (A / c ^ (n + 1)), by positivity, ?_⟩
  intro ρ hρ M hM u
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hjets : ∀ j ≤ m, ∀ x y : E,
      (1 + ‖x - y‖) ^ (n + 1) *
        ‖iteratedFDeriv ℝ j (fun z ↦ ((1 - (0 : ℝ) : ℝ) : ℂ) *
          rightLocalizerScalarKernel ρ mi z y) x‖ ≤
        (A / c ^ (n + 1)) * ρ ^ (n + m) := by
    intro j hj x y
    simp only [sub_zero, Complex.ofReal_one, one_mul]
    have hspace : c * (1 + ‖x - y‖) ≤ 1 + ρ / (2 * Real.pi) * ‖x - y‖ := by
      have hcρ : c ≤ ρ / (2 * Real.pi) :=
        (min_le_right _ _).trans (div_le_div_of_nonneg_right hρ (by positivity))
      calc
        _ = c + c * ‖x - y‖ := by ring
        _ ≤ _ := add_le_add (min_le_left _ _) (mul_le_mul_of_nonneg_right hcρ (norm_nonneg _))
    have hscaled : c ^ (n + 1) * ((1 + ‖x - y‖) ^ (n + 1) *
        ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖) ≤
          A * ρ ^ (n + m) := by
      calc
        _ = (c * (1 + ‖x - y‖)) ^ (n + 1) *
            ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖ := by
          rw [mul_pow]; ring
        _ ≤ (1 + ρ / (2 * Real.pi) * ‖x - y‖) ^ (n + 1) *
            ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖ := by gcongr
        _ ≤ _ := ha ρ hρ j hj x y
    have hd : (1 + ‖x - y‖) ^ (n + 1) *
        ‖iteratedFDeriv ℝ j (fun z ↦ rightLocalizerScalarKernel ρ mi z y) x‖ ≤
          (A * ρ ^ (n + m)) / c ^ (n + 1) :=
      (le_div_iff₀ (pow_pos hc (n + 1))).mpr (by simpa only [mul_comm] using hscaled)
    exact hd.trans_eq (by ring)
  have hzero : sourceCutMultiplier (r := r) (fun _ : E ↦ (0 : ℝ))
      continuous_const (fun _ ↦ by simp) = 0 := by
    ext v : 1
    apply Lp.ext
    filter_upwards [sourceCutMultiplier_coeFn (fun _ : E ↦ (0 : ℝ))
      continuous_const (fun _ ↦ by simp) v,
      Lp.coeFn_zero (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)] with x hx hz
    change sourceCutMultiplier (fun _ : E ↦ (0 : ℝ)) continuous_const
      (fun _ ↦ by simp) v x = (0 : H) x
    rw [hx, hz]
    simp
  obtain ⟨hm, hn⟩ := hs ρ hρpos.ne' mi hi his (fun _ ↦ 0) contDiff_const
    (fun _ ↦ by simp) ((A / c ^ (n + 1)) * ρ ^ (n + m)) (by positivity) hjets M hM u
  simp only [hzero, zero_sub, ContinuousLinearMap.comp_apply,
    neg_apply, one_apply_eq_self] at hm hn
  obtain ⟨hm', he⟩ := TerminalBounds.neg_bound hm
  simp only [neg_neg] at hm' he
  exact ⟨hm', by rw [he]; simpa only [mul_assoc] using hn⟩


section Actual
variable {d : ℕ}
open RegularSector.FiniteMasks
local notation "E₁" => Euclidean (d + 1)
local notation "H₁" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E₁)

/-- The full fixed terminal defect is bounded on Hᵐ in both literal
orientations, retaining its low-frequency bump and source multiplication.
Combined with the ordinary localizer bound, this handles frequencies below
the cancellation threshold (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem exists_actualAngularPDO_sub_identity_sobolev_bound
    {Ω : Set E₁} {center : E₁} {RQ Mbound : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E₁}
    (f : ActualFamily.ActualMaskFamily Ω center RQ A₀ K Mbound) (backward : Bool)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H₁, MemVectorFourierSobolev (m : ℝ) u →
      let P := if backward then (actualAngularPDO (r := r) f).adjoint else actualAngularPDO f
      MemVectorFourierSobolev (m : ℝ) ((P - 1) u) ∧
      vectorFourierSobolevNorm (m : ℝ) ((P - 1) u) ≤ C * vectorFourierSobolevNorm (m : ℝ) u := by
  let χo := if backward then f.inputMask else f.outputMask
  let χs := if backward then f.outputMask else f.inputMask
  have ho : ContDiff ℝ ∞ χo := by
    cases backward <;> first | exact f.outputMask_smooth | exact f.inputMask_smooth
  have hs : ContDiff ℝ ∞ χs := by
    cases backward <;> first | exact f.outputMask_smooth | exact f.inputMask_smooth
  have hoc : HasCompactSupport χo := by
    cases backward <;> first | exact f.outputMask_compact | exact f.inputMask_compact
  have hsc : HasCompactSupport χs := by
    cases backward <;> first | exact f.outputMask_compact | exact f.inputMask_compact
  have hor : ∀ x, χo x ∈ Icc (0 : ℝ) 1 := by
    cases backward <;> first | exact f.outputMask_range | exact f.inputMask_range
  have hsr : ∀ x, χs x ∈ Icc (0 : ℝ) 1 := by
    cases backward <;> first | exact f.outputMask_range | exact f.inputMask_range
  let hob := fun x ↦ (Real.norm_of_nonneg (hor x).1).trans_le (hor x).2
  let hsb := fun x ↦ (Real.norm_of_nonneg (hsr x).1).trans_le (hsr x).2
  let To := sourceCutMultiplier (r := r) χo ho.continuous hob
  let Ts := sourceCutMultiplier (r := r) χs hs.continuous hsb
  obtain ⟨Co, hCo, hco⟩ := exists_sourceCutMultiplier_fourierSobolev_bound (r := r) χo ho hoc hob m
  obtain ⟨Cs, hCs, hcs⟩ := exists_sourceCutMultiplier_fourierSobolev_bound (r := r) χs hs hsc hsb m
  refine ⟨Co * Cs + 1, by positivity, ?_⟩
  intro u hu P
  let b := fun ξ ↦ ∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ
  have hb : Continuous b := continuous_finsetSum _ (fun p _ ↦
    (contDiff_dilatedConicMask (f.angularMask_smooth p) f.radialThreshold).continuous)
  have hbb : ∀ ξ, ‖b ξ‖ ≤ 1 := fun ξ ↦
    (Real.norm_of_nonneg (actualFamily_sum_dilatedConicMask_mem_Icc f ξ).1).trans_le
      (actualFamily_sum_dilatedConicMask_mem_Icc f ξ).2
  let B := scalarPhysicalFrequencyOperator (r := r) b hb hbb
  have he : P = To.comp (B.comp Ts) := by
    obtain ⟨_, _, hf, ha⟩ := actualAngularPDO_eq_fourier_composition (r := r) f
    cases backward
    · exact hf
    · exact ha
  obtain ⟨hsm, hsn⟩ := hcs u hu
  obtain ⟨hbm, hbn⟩ := scalarPhysicalFrequencyOperator_fourierSobolev_bound b hb hbb
    (m : ℝ) (Ts u) hsm
  obtain ⟨hom, hon⟩ := hco _ hbm
  obtain ⟨hnm, hnn⟩ := TerminalBounds.neg_bound hu
  obtain ⟨hm, hn⟩ := TerminalBounds.add_bound hom hnm
  rw [he]
  change MemVectorFourierSobolev (m : ℝ) (To (B (Ts u)) - u) ∧ _
  refine ⟨by simpa only [sub_eq_add_neg] using hm, ?_⟩
  change vectorFourierSobolevNorm (m : ℝ) (To (B (Ts u)) - u) ≤ _
  rw [sub_eq_add_neg]
  calc
    _ ≤ vectorFourierSobolevNorm (m : ℝ) (To (B (Ts u))) + vectorFourierSobolevNorm (m : ℝ) (-u) := hn
    _ ≤ Co * (Cs * vectorFourierSobolevNorm (m : ℝ) u) + vectorFourierSobolevNorm (m : ℝ) u :=
      add_le_add (hon.trans (mul_le_mul_of_nonneg_left (hbn.trans hsn) hCo)) hnn.le
    _ = _ := by ring

end Actual

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
