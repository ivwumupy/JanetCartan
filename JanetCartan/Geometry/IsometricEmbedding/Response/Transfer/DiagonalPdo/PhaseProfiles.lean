module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DiagonalPdo.Geometry
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-!
# Full-source diagonal carrier phase profiles

The elliptic forward and literal-adjoint carriers have the same diagonal
phase. Its fixed bilinear part and two contractive physical projections
preserve the original source reserve at every joint derivative order.
This supplies the phase-jet input of both selected elliptic envelope branches
(`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace JanetCartan.ResponseTransfer.DiagonalPdo
open DirectEvolution
variable {d : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "W" => CarrierVariables (d + 1)
local notation "Joint" => (E × Par) × W

/-- The diagonal phase has a global smooth representative whenever the
original source phase does (`app:ch_response:eq:response-exact-phase`). -/
theorem contDiff_diagonalCarrierPhase {φ : E → Par → ℝ}
    (hφ : ContDiff ℝ ∞ (Function.uncurry φ)) :
    ContDiff ℝ ∞ (Function.uncurry (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ)) := by
  have hz : ContDiff ℝ ∞ (fun v : Joint ↦ v.2.fst) :=
    (WithLp.fstL 2 ℝ E E).contDiff.comp contDiff_snd
  have hξ : ContDiff ℝ ∞ (fun v : Joint ↦ v.2.snd) :=
    (WithLp.sndL 2 ℝ E E).contDiff.comp contDiff_snd
  exact ((contDiff_fst.fst.inner ℝ hξ).sub (hz.inner ℝ hξ) |>.add
    (hφ.comp (hz.prodMk contDiff_fst.snd))).sub (hφ.comp contDiff_fst)

/-- The full diagonal carrier phase preserves the original source reserve.
Both physical evaluations use contractive projections; its fixed bilinear
part costs no history order (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_diagonal_fullSourcePhase_joint_profiles
    {Kjoint : Set Joint} (hKjoint : IsCompact Kjoint)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (φ : E → Par → ℝ), ContDiff ℝ ∞ (Function.uncurry φ) →
      ∀ (KP : Set (E × Par)),
      (∀ v ∈ Kjoint, v.1 ∈ KP ∧ (v.2.fst,v.1.2) ∈ KP) →
      ∀ (Rstar : ℕ) (L : ℝ), 1 ≤ L →
      (∀ j q, q ∈ KP → ‖iteratedFDeriv ℝ j (Function.uncurry φ) q‖ ≤ A j * L^(j-Rstar)) →
      ∀ j v, v ∈ Kjoint →
        ‖iteratedFDeriv ℝ j
          (Function.uncurry (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ)) v‖ ≤
          C j * L^(j-Rstar) := by
  let px : Joint →L[ℝ] (E × Par) := ContinuousLinearMap.fst ℝ (E × Par) W
  let pz : Joint →L[ℝ] (E × Par) :=
    ((WithLp.fstL 2 ℝ E E).comp (ContinuousLinearMap.snd ℝ (E × Par) W)).prod
      ((ContinuousLinearMap.snd ℝ E Par).comp (ContinuousLinearMap.fst ℝ (E × Par) W))
  have hpx : ‖px‖ ≤ 1 := by
    apply px.opNorm_le_bound zero_le_one
    intro v
    change ‖v.1‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using norm_fst_le v
  have hpz : ‖pz‖ ≤ 1 := by
    apply pz.opNorm_le_bound zero_le_one
    intro v
    change max ‖v.2.fst‖ ‖v.1.2‖ ≤ 1 * ‖v‖
    rw [one_mul]
    exact max_le ((WithLp.norm_fst_le (p := 2) E v.2).trans (norm_snd_le v))
      ((norm_snd_le v.1).trans (norm_fst_le v))
  let b : Joint → ℝ := fun v ↦ inner ℝ v.1.1 v.2.snd - inner ℝ v.2.fst v.2.snd
  have hb : ContDiff ℝ ∞ b := by
    have hz : ContDiff ℝ ∞ (fun v : Joint ↦ v.2.fst) :=
      (WithLp.fstL 2 ℝ E E).contDiff.comp contDiff_snd
    have hξ : ContDiff ℝ ∞ (fun v : Joint ↦ v.2.snd) :=
      (WithLp.sndL 2 ℝ E E).contDiff.comp contDiff_snd
    exact (contDiff_fst.fst.inner ℝ hξ).sub (hz.inner ℝ hξ)
  refine ⟨fun j ↦ cNorm Kjoint j b + 2 * A j,
    fun j ↦ add_nonneg (cNorm_nonneg _ _ _) (mul_nonneg (by norm_num) (hA j)),?_⟩
  intro φ hφ KP hKP Rstar L hL hsource j v hv
  have hcomp (p : Joint →L[ℝ] (E × Par)) (hp : ‖p‖ ≤ 1) (hv : p v ∈ KP) :
      ‖iteratedFDeriv ℝ j (Function.uncurry φ ∘ p) v‖ ≤ A j * L^(j-Rstar) := by
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le p isOpen_univ
      hφ.contDiffOn (mem_univ _) j).trans
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hp)).trans
      (hsource j (p v) hv)
  have hjx := hcomp px hpx (hKP v hv).1
  have hjz := hcomp pz hpz (hKP v hv).2
  have hjb : ‖iteratedFDeriv ℝ j b v‖ ≤ cNorm Kjoint j b * L^(j-Rstar) :=
    (norm_iteratedFDeriv_le_cNorm hKjoint (hb.of_le (by simp)) hv le_rfl).trans
      (le_mul_of_one_le_right (cNorm_nonneg _ _ _) (one_le_pow₀ hL))
  have he : Function.uncurry (carrierPhase (fun x ξ : E ↦ inner ℝ x ξ) φ) =
      b + Function.uncurry φ ∘ pz - Function.uncurry φ ∘ px := by
    rfl
  rw [he,iteratedFDeriv_sub_apply
    (f := b + Function.uncurry φ ∘ pz) (g := Function.uncurry φ ∘ px)
    ((hb.add (hφ.comp pz.contDiff)).contDiffAt.of_le (by simp))
    ((hφ.comp px.contDiff).contDiffAt.of_le (by simp)),
    iteratedFDeriv_add_apply (f := b) (g := Function.uncurry φ ∘ pz)
      (hb.contDiffAt.of_le (by simp))
      ((hφ.comp pz.contDiff).contDiffAt.of_le (by simp))]
  calc
    _ ≤ (‖iteratedFDeriv ℝ j b v‖ + ‖iteratedFDeriv ℝ j (Function.uncurry φ ∘ pz) v‖) +
        ‖iteratedFDeriv ℝ j (Function.uncurry φ ∘ px) v‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (cNorm Kjoint j b * L^(j-Rstar) + A j * L^(j-Rstar)) + A j * L^(j-Rstar) :=
      add_le_add (add_le_add hjb hjz) hjx
    _ = _ := by ring

end JanetCartan.ResponseTransfer.DiagonalPdo
