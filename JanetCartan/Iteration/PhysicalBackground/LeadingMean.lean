module

public import JanetCartan.Iteration.PhysicalBackground.MeanProfiles
public import JanetCartan.Iteration.PhysicalPrimary.LeadingCurrent

/-!
# Constant-initial principal profiles from the one retained leading tuple

This adapter specializes the actual checked `LeadingCell.solution` on the
parent-selected `hdata`; it never chooses another row, chart, flow or scalar
solution. It extracts the principal matrix's last nonnegative summand and
spends the original shift fourteen. The consumer is the literal current mean
in `app:ch_background:prop:bg-current`.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace JanetCartan.PhysicalBackground
open PhysicalPrimary ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave LeadingWave.FullModulation AmbientResponse ContinuumRow.LeadingPrimitive

private theorem constant_initial_cNorm_le {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (K : Set D) (s : ℕ) (v : ℝ) : cNorm K s (fun _ ↦ v) ≤ |v| := by
  induction s with
  | zero =>
    rw [cNorm_order_zero]
    exact Real.sSup_le (by rintro _ ⟨x, _, rfl⟩; exact le_rfl) (abs_nonneg _)
  | succ s ih =>
    rw [cNorm_succ]
    have hz : sSup ((fun x : D ↦ ‖iteratedFDeriv ℝ (s + 1) (fun _ : D ↦ v) x‖) '' K) ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro _ ⟨x, _, rfl⟩
      simp [iteratedFDeriv_succ_const]
    linarith

/-- The exact SAME selected leading solution with initial constant `σ` has a
principal-matrix profile, spending only the existing shift fourteen. The
parent's `exists_original_retained_physical_leading` supplies `hdata` and the
physical map profile. Neither a principal-matrix bound nor a source-profile
success assumption is introduced (`app:ch_background:eq:bg-current-profile`). -/
theorem retained_constant_initial_principal_profile
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {K : Set (Euclidean n)}
    (centers : Finset (parameterCube P.radius)) (row col : centers → Fin n)
    (ρ R τ Rc τc Mc rcomp δcomp σcover : centers → ℝ)
    (Ωc : centers → Set (Euclidean n × Euclidean 3)) (ρc Bc gc Bfull : centers → ℝ)
    (Mscalar mscalar c : ℝ) (E : ℕ → ℝ) (A H B : centers → ℕ → ℝ)
    (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hdata : RetainedLeadingData T (K := K) centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
      Ωc ρc Bc gc Bfull Mscalar mscalar c E A H B F hF hi hrank)
    (cell : centers) {σ : ℝ} (hσ : 0 ≤ σ) (hσone : σ ≤ 1)
    (hM : σ ≤ Mscalar) (hm : mscalar ≤ σ)
    (Amap : ℕ → ℝ) (hAmap : ∀ s, 0 ≤ Amap s) (hE : ∀ s, 0 ≤ E s)
    {rStar reserve : ℕ} (hreserve : reserve + 14 ≤ rStar) {scale : ℝ} (hscale : 1 ≤ scale)
    (hprofile : HasDerivativeProfile K F rStar scale Amap) :
    let Q := LeadingData.Q T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
      Mscalar mscalar c E A H B F hF hi hrank hdata
    let J := closedBall
      (LeadingCell.a T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
        Mscalar mscalar c E A H B F hF hi hrank hdata cell)
      (LeadingCell.σ T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
        Mscalar mscalar c E A H B F hF hi hrank hdata cell)
    let Φ := LeadingCell.Φ T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
      Mscalar mscalar c E A H B F hF hi hrank hdata cell
    let Y := LeadingCell.Y T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
      Mscalar mscalar c E A H B F hF hi hrank hdata cell
    let r := LeadingCell.row T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
      Mscalar mscalar c E A H B F hF hi hrank hdata cell
    let k := LeadingCell.col T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
      Mscalar mscalar c E A H B F hF hi hrank hdata cell
    HasDerivativeProfile J
      (fun w ↦ principalMatrix (fullNormal T Q F r k Φ Y (fun _ ↦ σ) w)
        (phaseGradient T Q w.1 w.2.2)) reserve scale (fun s ↦ E s * (2 + Amap (s + 14))) := by
  intro Q J Φ Y r k
  have hinit (Kinit : Set (Euclidean (n - 1) × Euclidean 3)) (s : ℕ) :
      cNorm Kinit s (fun _ ↦ σ) ≤ σ :=
    (constant_initial_cNorm_le Kinit s σ).trans_eq (abs_of_nonneg hσ)
  let z₀ := LeadingCell.z₀ T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
    Mscalar mscalar c E A H B F hF hi hrank hdata cell
  let R₀ := LeadingCell.R T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
    Mscalar mscalar c E A H B F hF hi hrank hdata cell
  let J₀ : Set (Euclidean (n - 1) × Euclidean 3) :=
    closedBall ((0 : Euclidean (n - 1)), z₀) (R₀ / 8)
  have hconst (s : ℕ) : cNorm J₀ s (fun _ ↦ σ) ≤ σ := hinit J₀ s
  have hsolution := LeadingCell.solution T centers row col ρ R τ Rc τc Mc rcomp δcomp σcover
    Ωc ρc Bc gc Bfull Mscalar mscalar c E A H B F hF hi hrank hdata cell
    (fun _ ↦ σ) contDiffOn_const ((hinit _ 14).trans hM) (fun _ _ ↦ hm)
  intro s
  have hfull := hsolution.2.2 s
  dsimp only at hfull
  have hphase : 0 ≤ cNorm J s (fun w ↦ phase T Q w.1 w.2.2) := cNorm_nonneg ..
  have hamp : 0 ≤ cNorm J s (fun w ↦ scalarAmplitude T Q F r k Φ Y (fun _ ↦ σ) w • nullvector T Q k w) := cNorm_nonneg ..
  have hnormal : 0 ≤ cNorm J s (fun w ↦ principalNormal (canonicalNormalCompletion F w.1)
      (phaseGradient T Q w.1 w.2.2)
      (scalarAmplitude T Q F r k Φ Y (fun _ ↦ σ) w • nullvector T Q k w)) := cNorm_nonneg ..
  have hrec : 0 ≤ cNorm J s (fun w ↦ reconstruction F (canonicalNormalCompletion F)
      (fun x ↦ scalarAmplitude T Q F r k Φ Y (fun _ ↦ σ) (x, w.2) • nullvector T Q k (x, w.2)) w.1) := cNorm_nonneg ..
  have hpre : 0 ≤
      cNorm J s (fun w ↦ phase T Q w.1 w.2.2) +
      cNorm J s (fun w ↦ scalarAmplitude T Q F r k Φ Y (fun _ ↦ σ) w • nullvector T Q k w) +
      cNorm J s (fun w ↦ principalNormal (canonicalNormalCompletion F w.1)
        (phaseGradient T Q w.1 w.2.2)
        (scalarAmplitude T Q F r k Φ Y (fun _ ↦ σ) w • nullvector T Q k w)) +
      cNorm J s (fun w ↦ reconstruction F (canonicalNormalCompletion F)
        (fun x ↦ scalarAmplitude T Q F r k Φ Y (fun _ ↦ σ) (x, w.2) • nullvector T Q k (x, w.2)) w.1) := by
    exact add_nonneg (add_nonneg (add_nonneg hphase hamp) hnormal) hrec
  have hprincipal : cNorm J s (fun w ↦ principalMatrix
      (principalNormal (canonicalNormalCompletion F w.1) (phaseGradient T Q w.1 w.2.2)
        (scalarAmplitude T Q F r k Φ Y (fun _ ↦ σ) w • nullvector T Q k w))
      (phaseGradient T Q w.1 w.2.2)) ≤
      E s * (1 + cNorm K (s + 14) F + cNorm J₀ (s + 14) (fun _ ↦ σ)) := by
    dsimp [J₀, z₀, R₀]
    nlinarith [hfull, hpre]
  have hb : cNorm J s (fun w ↦ principalMatrix (fullNormal T Q F r k Φ Y (fun _ ↦ σ) w)
      (phaseGradient T Q w.1 w.2.2)) ≤ E s * (1 + cNorm K (s + 14) F + σ) := by
    rw [show (fun w ↦ principalMatrix (fullNormal T Q F r k Φ Y (fun _ ↦ σ) w)
        (phaseGradient T Q w.1 w.2.2)) = (fun w ↦ principalMatrix
          (principalNormal (canonicalNormalCompletion F w.1) (phaseGradient T Q w.1 w.2.2)
            (scalarAmplitude T Q F r k Φ Y (fun _ ↦ σ) w • nullvector T Q k w))
          (phaseGradient T Q w.1 w.2.2)) by
      funext w; rfl]
    exact hprincipal.trans (mul_le_mul_of_nonneg_left
      (add_le_add_right (hconst (s + 14)) _) (hE s))
  have hmap : cNorm K (s + 14) F ≤ Amap (s + 14) * scale ^ (s - reserve) :=
    (hprofile (s + 14)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hscale (by omega)) (hAmap _))
  have hpow : 1 ≤ scale ^ (s - reserve) := one_le_pow₀ hscale
  apply hb.trans
  have hb' : 1 + cNorm K (s + 14) F + σ ≤ (2 + Amap (s + 14)) * scale ^ (s - reserve) := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hb' (hE s)).trans_eq (by ring)

end JanetCartan.PhysicalBackground
