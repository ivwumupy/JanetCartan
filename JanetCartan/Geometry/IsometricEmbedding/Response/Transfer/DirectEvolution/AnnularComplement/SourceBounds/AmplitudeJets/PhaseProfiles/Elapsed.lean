module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.LowPhase

/-!
# Fixed-frequency elapsed phase from original joint two-time data

The consumer is the normalized external phase profile in
`app:ch_response:lem:energy-carrier-jets`. All derivatives below precede
normalization by `λ + ‖ξ‖`. Original phase regularity is local to its open
chart; no regularity outside the supported frequency neighborhood is used.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.PhaseProfiles
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)

/-- Insert the physical position, with zero source and covector. The actual
covector is restored by translation before evaluating the original phase.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
def positionInsertion : E →L[ℝ] FullAmplitudePrimitiveBudget.Local.Point (d + 1) :=
  ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)).prod (0 : E →L[ℝ] E)

/-- The fixed-frequency elapsed linear substitution is a contraction,
uniformly in elapsed time and frequency (`fixed-time-representation`). -/
theorem norm_elapsedLinear_positionInsertion_le :
    ‖(elapsedLinear (d := d)).comp positionInsertion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  calc
    ‖elapsedLinear (positionInsertion x)‖ ≤ ‖positionInsertion x‖ :=
      (elapsedLinear.le_opNorm _).trans (by
        simpa using mul_le_mul_of_nonneg_right (norm_elapsedLinear_le (d := d))
          (norm_nonneg (positionInsertion x)))
    _ = 1 * ‖x‖ := by simp [positionInsertion, Prod.norm_def]

/-- The affine map retains both original times and the unchanged physical
frequency. No homogeneous phase extension is used (`fixed-time-representation`). -/
theorem elapsedPoint_fixedFrequency_eq (t : ℝ) (ξ x : E) :
    elapsedPoint t ((x, 0), ξ) =
      (elapsedLinear.comp positionInsertion) x + elapsedPoint t ((0, 0), ξ) := by
  have hz : spatialPart (0 : E) = 0 := (spatialProjection (d := d)).map_zero
  simp [elapsedPoint, elapsedLinear, positionInsertion, elapsedTranslation, hz]

/-- Local original two-time smoothness supplies the literal elapsed phase
at fixed frequency on its physical neighborhood. Consumer: normalized
annular external phase smoothness (`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffOn_elapsedPhase_fixedFrequency
    {W : Set E} {O : Set (TwoTimePoint d)} (Ψ : TwoTimePhase d)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) O) (t : ℝ) (ξ : E)
    (hmap : ∀ x ∈ W, elapsedPoint t ((x, 0), ξ) ∈ O) :
    ContDiffOn ℝ ∞ (fun x => elapsedPhase Ψ t x ξ) W := by
  apply (contDiffOn_jointElapsedPhase Ψ hΨ t).comp
    ((contDiffOn_id.prodMk contDiffOn_const).prodMk contDiffOn_const)
  exact hmap

private theorem norm_iteratedFDeriv_affine_le {D : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (l : D →L[ℝ] ℝ) (b : ℝ) (y : D) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun x => l x + b) y‖ ≤ ‖l y + b‖ + ‖l‖ := by
  cases m with
  | zero => simp
  | succ m =>
    have hd : fderiv ℝ (fun x => l x + b) = fun _ => l := by
      funext x
      simp
    rw [← norm_iteratedFDeriv_fderiv, hd]
    cases m with
    | zero => simp
    | succ m =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m), Pi.zero_apply, norm_zero]
      positivity

/-- The affine time term costs only a fixed physical radius and slab length,
including order zero. Consumer: the normalized annular phase profile. -/
theorem norm_iteratedFDeriv_elapsedTime_le
    {R Δ t : ℝ} (_hR : 0 ≤ R) (ht : t ∈ Icc 0 Δ)
    (ξ x : E) (hx : ‖x‖ ≤ R) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y : E => (y 0 - t) * ξ 0) x‖ ≤
      (R + Δ + 1) * ‖ξ‖ := by
  let l : E →L[ℝ] ℝ := (ξ 0) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0
  have hl : ‖l‖ ≤ ‖ξ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    change ‖ξ 0 * y 0‖ ≤ ‖ξ‖ * ‖y‖
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le ξ 0) (PiLp.norm_apply_le y 0)
      (norm_nonneg _) (norm_nonneg _)
  have he : (fun y : E => (y 0 - t) * ξ 0) = fun y => l y + (-t * ξ 0) := by
    funext y
    change (y 0 - t) * ξ 0 = ξ 0 * y 0 + (-t * ξ 0)
    ring
  rw [he]
  apply (norm_iteratedFDeriv_affine_le l (-t * ξ 0) x m).trans
  have hv : ‖l x + (-t * ξ 0)‖ ≤ (R + Δ) * ‖ξ‖ := by
    calc
      _ = ‖(x 0 - t) * ξ 0‖ := by congr 1; change ξ 0 * x 0 + _ = _; ring
      _ = ‖x 0 - t‖ * ‖ξ 0‖ := norm_mul _ _
      _ ≤ (‖x 0‖ + ‖t‖) * ‖ξ‖ := mul_le_mul (norm_sub_le _ _) (PiLp.norm_apply_le ξ 0)
        (norm_nonneg _) (by positivity)
      _ ≤ (R + Δ) * ‖ξ‖ := by
        gcongr
        · exact (PiLp.norm_apply_le x 0).trans hx
        · simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  nlinarith

/-- The Fourier pairing has a uniform all-order profile, including order
zero, on a fixed physical ball. No frequency bound is assumed. -/
theorem norm_iteratedFDeriv_frequencyPairing_le
    {R : ℝ} (_hR : 0 ≤ R) (ξ x : E) (hx : ‖x‖ ≤ R) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => inner ℝ y ξ) x‖ ≤ (R + 1) * ‖ξ‖ := by
  let l := InnerProductSpace.toDual ℝ E ξ
  have he : (fun y => inner ℝ y ξ) = fun y => l y + 0 := by
    funext y
    simp [l, real_inner_comm]
  rw [he]
  apply (norm_iteratedFDeriv_affine_le l 0 x m).trans
  have hb : ‖l x + 0‖ ≤ R * ‖ξ‖ := by
    simpa [l, real_inner_comm] using
      (norm_inner_le_norm (𝕜 := ℝ) x ξ).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg ξ))
  have hn : ‖l‖ = ‖ξ‖ := by simp [l]
  nlinarith

/-- Original joint phase jets give actual elapsed physical jets. Both times
are pulled back by the published affine contraction; the time pairing is
estimated separately. This preserves the physical order-one frequency
weight, including bounded-frequency shoulders. Consumer: `norm_normalizedExternalJet_source_le`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_elapsedPhase_fixedFrequency_le
    {O : Set (TwoTimePoint d)} (hO : IsOpen O)
    (Ψ : TwoTimePhase d) (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) O)
    {R Δ t L B : ℝ} (hR : 0 ≤ R) (ht : t ∈ Icc 0 Δ) (hL : 1 ≤ L)
    (ξ x : E) (hx : ‖x‖ ≤ R) (hm : elapsedPoint t ((x, 0), ξ) ∈ O)
    (m : ℕ)
    (hb : ‖iteratedFDeriv ℝ m (jointPhase Ψ) (elapsedPoint t ((x, 0), ξ))‖ ≤
      B * (1 + ‖ξ‖) * L ^ m) :
    ‖iteratedFDeriv ℝ m (fun y => elapsedPhase Ψ t y ξ) x‖ ≤
      (R + Δ + 1 + B) * (1 + ‖ξ‖) * L ^ m := by
  let f : E → ℝ := fun y => jointPhase Ψ (elapsedPoint t ((y, 0), ξ))
  have hf : ContDiffAt ℝ ∞ f x := by
    change ContDiffAt ℝ ∞ (jointPhase Ψ ∘ (fun y : E => elapsedPoint t ((y, 0), ξ))) x
    apply (hΨ.contDiffAt (hO.mem_nhds hm)).comp x
    have hemap : (fun y : E => elapsedPoint t ((y, 0), ξ)) =
        fun y => (elapsedLinear.comp positionInsertion) y + elapsedPoint t ((0, 0), ξ) :=
      funext (elapsedPoint_fixedFrequency_eq t ξ)
    rw [hemap]
    exact ((elapsedLinear.comp positionInsertion).contDiff.add contDiff_const).contDiffAt
  have hjet : ‖iteratedFDeriv ℝ m f x‖ ≤ B * (1 + ‖ξ‖) * L ^ m := by
    have ha := norm_iteratedFDeriv_preAffine_le (elapsedLinear.comp positionInsertion)
      (elapsedPoint t ((0, 0), ξ)) hO hΨ
      (by rwa [← elapsedPoint_fixedFrequency_eq]) m
    have hpow := pow_le_one₀ (norm_nonneg _) (norm_elapsedLinear_positionInsertion_le (d := d))
      (n := m)
    simp_rw [← elapsedPoint_fixedFrequency_eq] at ha
    exact ha.trans ((mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans
      (by simpa using hb))
  have he : (fun y => elapsedPhase Ψ t y ξ) = (fun y : E => (y 0 - t) * ξ 0) + f := by
    funext y
    simp [elapsedPhase, f, jointPhase]
  have htimeSmooth : ContDiff ℝ ∞ (fun y : E => (y 0 - t) * ξ 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0).contDiff.sub
      contDiff_const).mul contDiff_const
  rw [he, iteratedFDeriv_add_apply (htimeSmooth.contDiffAt.of_le (by simp))
    (hf.of_le (by simp))]
  apply (norm_add_le _ _).trans
  have htime := norm_iteratedFDeriv_elapsedTime_le hR ht ξ x hx m
  have hscale : 1 ≤ L ^ m := one_le_pow₀ hL
  have hcoeff : 0 ≤ R + Δ + 1 := by linarith [ht.1, ht.2]
  have ht' : (R + Δ + 1) * ‖ξ‖ ≤ (R + Δ + 1) * (1 + ‖ξ‖) * L ^ m := by
    calc
      _ ≤ (R + Δ + 1) * (1 + ‖ξ‖) := by gcongr; linarith [norm_nonneg ξ]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hscale
  nlinarith

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.PhaseProfiles
