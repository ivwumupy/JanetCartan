module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.PrimitiveNorm
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformGeometry.RootFlow

/-!
# Common nested buffers for the literal characteristic amplitudes

The amplitude producer needs four forward/inverse inclusions on nested balls,
not just an inverse chart. Derive them with radii chosen before the chart from
its common source/target radii and the common first-derivative bounds. The same
radii also control the actual initial-state/elapsed-time flow input.

Consumer: `AmplitudeBounds.exists_pencilPrimitiveAmplitudes_cNorm_bounds`,
for `app:ch_regular_base:lem:characteristic-kernel` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.UniformAmplitudes
open AmplitudeBounds
variable {d : ℕ}
local notation "TPoint" => TwoTimePoint (Euclidean d)

/-- The original two-time projection's first joint norm bounds its distance
from the diagonal centre. This supplies the forward estimate used when
choosing the common amplitude balls; no chart Lipschitz estimate is assumed.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem projection_displacement_le_cNorm
    (z : RootState (Euclidean d)) {a : ℝ} (ha : 0 < a)
    {U : Set TPoint} (hU : IsOpen U) (hsub : closedBall (z.1, z) a ⊆ U)
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    (hΦ : ContDiffOn ℝ ∞ (twoTimeProjection Φ) U)
    (hdiag : twoTimeProjection Φ (z.1, z) = (z.1, z))
    {A : ℝ} (hA : cNorm (closedBall (z.1, z) a) 1 (twoTimeProjection Φ) ≤ A)
    {q : TPoint} (hq : q ∈ closedBall (z.1, z) a) :
    ‖twoTimeProjection Φ q - (z.1, z)‖ ≤ A * ‖q - (z.1, z)‖ := by
  have hs (p : TPoint) (hp : p ∈ closedBall (z.1, z) a) :=
    hΦ.contDiffAt (hU.mem_nhds (hsub hp))
  have hd (p : TPoint) (hp : p ∈ closedBall (z.1, z) a) :
      ‖fderiv ℝ (twoTimeProjection Φ) p‖ ≤ A := by
    have h := JanetCartan.norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall (z.1, z) a) (fun w hw ↦ (hs w hw).of_le (by simp)) hp
      (show 1 ≤ 1 by rfl)
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans hA
  simpa only [hdiag] using (convex_closedBall (z.1, z) a).norm_image_sub_le_of_norm_fderiv_le
    (fun p hp ↦ (hs p hp).differentiableAt (by simp)) hd
    (mem_closedBall_self ha.le) hq

/-- The literal flow-input map has cost at most two in the product norm,
including the difference of both times. Source: `characteristic-kernel`. -/
theorem twoTimeFlowInput_displacement_le (z : RootState (Euclidean d)) (q : TPoint) :
    ‖twoTimeFlowInput q - (z, (0 : ℝ))‖ ≤ 2 * ‖q - (z.1, z)‖ := by
  have h₁ : ‖q.2 - z‖ ≤ ‖q - (z.1, z)‖ := le_max_right _ _
  have h₂ : ‖q.1 - z.1‖ ≤ ‖q - (z.1, z)‖ := le_max_left _ _
  have h₃ : ‖q.2.1 - z.1‖ ≤ ‖q.2 - z‖ := le_max_left _ _
  change max ‖q.2 - z‖ ‖q.1 - q.2.1 - 0‖ ≤ _
  rw [sub_zero]
  apply max_le
  · linarith [norm_nonneg (q - (z.1, z))]
  · calc
      ‖q.1 - q.2.1‖ = ‖(q.1 - z.1) - (q.2.1 - z.1)‖ := by congr 1; ring
      _ ≤ ‖q.1 - z.1‖ + ‖q.2.1 - z.1‖ := norm_sub_le _ _
      _ ≤ _ := by linarith

/-- The physical image of a two-time ball is contained in the physical image
of the root-state ball with the same centre. This converts the actual root
producer's physical buffer to the amplitude producer's coordinates, without
an additional coordinate-norm constant (`characteristic-kernel`). -/
theorem physicalPosition_mapsTo_of_rootPhysicalPosition
    {n : ℕ} (e : Euclidean n ≃L[ℝ] (ℝ × Euclidean d))
    (z : RootState (Euclidean d)) {L S : ℝ} (hL : 0 ≤ L) (hSL : S ≤ L)
    {K : Set (Euclidean n)}
    (hroot : MapsTo (rootPhysicalPosition e) (closedBall z L) K) :
    MapsTo (PhysicalAction.physicalPosition e) (closedBall (z.1, z) S) K := by
  intro q hq
  have hd : ‖q - (z.1, z)‖ ≤ S := by simpa only [mem_closedBall, dist_eq_norm] using hq
  have ht : ‖q.1 - z.1‖ ≤ S := (le_max_left _ _).trans hd
  have hy : ‖q.2.2.1 - z.2.1‖ ≤ S :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  have hw : (q.1, (q.2.2.1, z.2.2)) ∈ closedBall z L := by
    rw [mem_closedBall, dist_eq_norm]
    change max ‖q.1 - z.1‖ (max ‖q.2.2.1 - z.2.1‖ ‖z.2.2 - z.2.2‖) ≤ L
    rw [sub_self, norm_zero]
    exact max_le (ht.trans hSL) (max_le (hy.trans hSL) hL)
  exact hroot hw

/-- The literal source radius also lies within half the prescribed amplitude
radius. With `r = ρ / 2`, this gives `src ≤ ρ / 4` to
`exists_uniform_pencilAmplitudes_with_retarded_radii` before the chart or masks
are chosen. Sources: `app:ch_regular_base:lem:characteristic-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_common_amplitude_flowout_radius_le_half
    (z : RootState (Euclidean d)) {a r K : ℝ} (ha : 0 < a) (hr : 0 < r) (hK : 1 ≤ K) :
    ∃ b > (0 : ℝ), b < a ∧ b ≤ r / 2 ∧
      ∀ C : OpenPartialHomeomorph TPoint TPoint,
        (∀ q ∈ ball (z.1, z) a, ‖C q - (z.1, z)‖ ≤ K * ‖q - (z.1, z)‖) →
        MapsTo C (closedBall (z.1, z) b) (closedBall (z.1, z) r) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let b := min a (r / K) / 2
  have hb : 0 < b := half_pos (lt_min ha (div_pos hr hKp))
  have hba : b < a := by dsimp [b]; linarith only [min_le_left a (r / K), ha]
  have hbhalf : b ≤ r / 2 :=
    div_le_div_of_nonneg_right ((min_le_right a (r / K)).trans (div_le_self hr.le hK))
      (by norm_num : (0 : ℝ) ≤ 2)
  have hbr : K * b ≤ r := by
    have h : b ≤ r / K := by
      dsimp [b]; linarith only [min_le_right a (r / K), div_pos hr hKp]
    nlinarith only [(le_div_iff₀ hKp).mp h]
  refine ⟨b, hb, hba, hbhalf, ?_⟩
  intro C hC q hq
  have h := hC q ((closedBall_subset_ball hba) hq)
  have hqnorm : ‖q - (z.1, z)‖ ≤ b := by simpa only [mem_closedBall, dist_eq_norm] using hq
  rw [mem_closedBall, dist_eq_norm]
  exact h.trans ((mul_le_mul_of_nonneg_left hqnorm hKp.le).trans hbr)

/-- A source radius fixed before the chart sends the full closed source box
into a prescribed inner amplitude ball. This is the flowout containment for
the actual compact source mask (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_common_amplitude_flowout_radius
    (z : RootState (Euclidean d)) {a r K : ℝ} (ha : 0 < a) (hr : 0 < r) (hK : 1 ≤ K) :
    ∃ b > (0 : ℝ), b < a ∧
      ∀ C : OpenPartialHomeomorph TPoint TPoint,
        (∀ q ∈ ball (z.1, z) a, ‖C q - (z.1, z)‖ ≤ K * ‖q - (z.1, z)‖) →
        MapsTo C (closedBall (z.1, z) b) (closedBall (z.1, z) r) := by
  obtain ⟨b, hb, hba, _, hflow⟩ := exists_common_amplitude_flowout_radius_le_half z ha hr hK
  exact ⟨b, hb, hba, hflow⟩

/-- Choose every nested amplitude radius before the varying chart. The four
forward/inverse image hypotheses and the closed flow-input inclusion of the
local amplitude producer are conclusions. The larger open output ball has
its own margin inside the same target and flow-input ball.
Source: `app:ch_regular_base:lem:characteristic-kernel`. -/
theorem exists_common_amplitude_chart_buffers
    (z : RootState (Euclidean d)) {a b F K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hF : 0 < F) (hK : 1 ≤ K) :
    ∃ S > (0 : ℝ), ∃ R > (0 : ℝ), ∃ σ > (0 : ℝ), ∃ τ > (0 : ℝ),
      ∃ ρ > (0 : ℝ), ∃ ρo > ρ,
      σ < R ∧ τ < S ∧ ρo ≤ S ∧ R < a ∧ 2 * R ≤ F ∧ 2 * S ≤ b ∧
      ∀ C : OpenPartialHomeomorph TPoint TPoint,
        C.source = ball (z.1, z) a → closedBall (z.1, z) b ⊆ C.target →
        (∀ q ∈ ball (z.1, z) a, ‖C q - (z.1, z)‖ ≤ K * ‖q - (z.1, z)‖) →
        (∀ q ∈ C.target, ‖C.symm q - (z.1, z)‖ ≤ K * ‖q - (z.1, z)‖) →
        MapsTo C (closedBall (z.1, z) σ) (closedBall (z.1, z) τ) ∧
        MapsTo C (ball (z.1, z) R) (ball (z.1, z) S) ∧
        MapsTo C.symm (closedBall (z.1, z) ρ) (closedBall (z.1, z) σ) ∧
        MapsTo C.symm (ball (z.1, z) ρo) (ball (z.1, z) R) ∧
        closedBall (z.1, z) (2 * S) ⊆ C.target ∧
        MapsTo (twoTimeFlowInput ∘ C.symm) (closedBall (z.1, z) S)
          (closedBall (z, 0) F) ∧
        MapsTo (twoTimeFlowInput ∘ C.symm) (ball (z.1, z) (2 * S))
          (ball (z, 0) F) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let S := min b (F / (4 * K)) / 2
  have hS : 0 < S := half_pos (lt_min hb (div_pos hF (by positivity)))
  have hSb : 2 * S ≤ b := by dsimp [S]; linarith [min_le_left b (F / (4 * K))]
  have hSF : 8 * K * S ≤ F := by
    have h := min_le_right b (F / (4 * K))
    have he : 2 * S ≤ F / (4 * K) := by dsimp [S]; linarith
    have := (le_div_iff₀ (by positivity : 0 < 4 * K)).mp he
    nlinarith
  let R := min a (min (F / 4) (S / (2 * K))) / 2
  have hR : 0 < R := half_pos (lt_min ha
    (lt_min (by positivity) (div_pos hS (by positivity))))
  have hRa : R < a := by
    have : 2 * R ≤ a := by dsimp [R]; linarith [min_le_left a (min (F / 4) (S / (2 * K)))]
    linarith
  have hRF : 2 * R ≤ F := by
    have h := (min_le_right a (min (F / 4) (S / (2 * K)))).trans
      (min_le_left (F / 4) (S / (2 * K)))
    dsimp [R]; linarith
  have hRS : 4 * K * R ≤ S := by
    have h := (min_le_right a (min (F / 4) (S / (2 * K)))).trans
      (min_le_right (F / 4) (S / (2 * K)))
    have he : 2 * R ≤ S / (2 * K) := by dsimp [R]; linarith
    have := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp he
    nlinarith
  let ρo := min S (R / (2 * K)) / 2
  have hρo : 0 < ρo := half_pos (lt_min hS (div_pos hR (by positivity)))
  have hoS : ρo ≤ S := by dsimp [ρo]; linarith [min_le_left S (R / (2 * K))]
  have hoR : 4 * K * ρo ≤ R := by
    have he : 2 * ρo ≤ R / (2 * K) := by
      dsimp [ρo]; linarith [min_le_right S (R / (2 * K))]
    have := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp he
    nlinarith
  refine ⟨S, hS, R, hR, R / 2, by positivity, S / 2, by positivity,
    ρo / 2, by positivity, ρo, by linarith, by linarith, by linarith,
    hoS, hRa, hRF, hSb, ?_⟩
  intro C _hsource htarget hforward hinverse
  have htargetS : closedBall (z.1, z) (2 * S) ⊆ C.target :=
    (closedBall_subset_closedBall hSb).trans htarget
  have hi (q : TPoint) (hq : q ∈ closedBall (z.1, z) (2 * S)) := hinverse q (htargetS hq)
  have hKnonneg : 0 ≤ K := hKp.le
  refine ⟨?_, ?_, ?_, ?_, htargetS, ?_, ?_⟩
  · intro q hq
    have hqa : q ∈ ball (z.1, z) a := (closedBall_subset_ball (by linarith : R / 2 < a)) hq
    have h := (hforward q hqa).trans (mul_le_mul_of_nonneg_left
      (show ‖q - (z.1, z)‖ ≤ R / 2 by simpa only [mem_closedBall, dist_eq_norm] using hq) hKnonneg)
    rw [mem_closedBall, dist_eq_norm]
    nlinarith
  · intro q hq
    have hqa := ball_subset_ball hRa.le hq
    have h := (hforward q hqa).trans_lt (mul_lt_mul_of_pos_left
      (show ‖q - (z.1, z)‖ < R by simpa only [mem_ball, dist_eq_norm] using hq) hKp)
    rw [mem_ball, dist_eq_norm]
    nlinarith
  · intro q hq
    have hqs := (closedBall_subset_closedBall (by linarith : ρo / 2 ≤ 2 * S)) hq
    have h := (hi q hqs).trans (mul_le_mul_of_nonneg_left
      (show ‖q - (z.1, z)‖ ≤ ρo / 2 by simpa only [mem_closedBall, dist_eq_norm] using hq) hKnonneg)
    rw [mem_closedBall, dist_eq_norm]
    nlinarith
  · intro q hq
    have hqs : q ∈ closedBall (z.1, z) (2 * S) :=
      (closedBall_subset_closedBall (by linarith : ρo ≤ 2 * S)) (ball_subset_closedBall hq)
    have h := (hi q hqs).trans_lt (mul_lt_mul_of_pos_left
      (show ‖q - (z.1, z)‖ < ρo by simpa only [mem_ball, dist_eq_norm] using hq) hKp)
    rw [mem_ball, dist_eq_norm]
    nlinarith
  · intro q hq
    have hqs := (closedBall_subset_closedBall (by linarith : S ≤ 2 * S)) hq
    have h := (hi q hqs).trans (mul_le_mul_of_nonneg_left
      (show ‖q - (z.1, z)‖ ≤ S by simpa only [mem_closedBall, dist_eq_norm] using hq) hKnonneg)
    have hf := twoTimeFlowInput_displacement_le z (C.symm q)
    simpa only [mem_closedBall, dist_eq_norm, Function.comp_apply] using
      (show ‖twoTimeFlowInput (C.symm q) - (z, (0 : ℝ))‖ ≤ F by nlinarith)
  · intro q hq
    have h := (hi q (ball_subset_closedBall hq)).trans_lt (mul_lt_mul_of_pos_left
      (show ‖q - (z.1, z)‖ < 2 * S by simpa only [mem_ball, dist_eq_norm] using hq) hKp)
    have hf := twoTimeFlowInput_displacement_le z (C.symm q)
    simpa only [mem_ball, dist_eq_norm, Function.comp_apply] using
      (show ‖twoTimeFlowInput (C.symm q) - (z, (0 : ℝ))‖ < F by nlinarith)

end JanetCartan.RegularSector.Characteristic.UniformAmplitudes
