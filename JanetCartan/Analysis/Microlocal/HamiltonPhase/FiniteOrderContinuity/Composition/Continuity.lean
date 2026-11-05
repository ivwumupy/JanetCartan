module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition.JetBounds
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Joint continuity of composition in finite derivative seminorms

This is the composition step of `app:lem:common-hamilton-phase`, for the
root-initialized flow and for differentiated inverse equations. Smoothness is
local near the compact sets. Range containment is explicit and no derivative
above the requested order is used, even for the reference maps.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.HamiltonPhase.CompositionContinuity

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `app:lem:common-hamilton-phase`: seminorm control gives the difference of
ambient jets on a compact set for maps smooth on neighborhoods of that set. -/
theorem norm_iteratedFDeriv_sub_le_cNorm {K : Set E} (hK : IsCompact K) {m i : ℕ}
    {g g₀ : E → F} (hg : ∀ x ∈ K, ContDiffAt ℝ m g x)
    (hg₀ : ∀ x ∈ K, ContDiffAt ℝ m g₀ x) (hi : i ≤ m) {x : E} (hx : x ∈ K) :
    ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g₀ x‖ ≤ cNorm K m (g - g₀) := by
  rw [← iteratedFDeriv_sub_apply ((hg x hx).of_le (by exact_mod_cast hi))
    ((hg₀ x hx).of_le (by exact_mod_cast hi))]
  exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK (fun x hx ↦ (hg x hx).sub (hg₀ x hx)) hx hi

/-- `app:lem:common-hamilton-phase`: joint `C^m` continuity of composition on
fixed compact sets. The threshold depends only on the reference maps, compact
sets, order and tolerance. Both perturbed maps need only be `C^m` near their
respective compact sets. The range hypothesis is retained for the consumer's
buffered domains; no closeness of the compositions is assumed. -/
theorem exists_cNorm_comp_sub_lt {K : Set E} {L : Set F}
    (hK : IsCompact K) (hL : IsCompact L) {m : ℕ} {f₀ : F → G} {g₀ : E → F}
    (hf₀ : ∀ y ∈ L, ContDiffAt ℝ m f₀ y)
    (hg₀ : ∀ x ∈ K, ContDiffAt ℝ m g₀ x) (hrange₀ : Set.MapsTo g₀ K L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (f : F → G) (g : E → F),
      (∀ y ∈ L, ContDiffAt ℝ m f y) → (∀ x ∈ K, ContDiffAt ℝ m g x) →
      Set.MapsTo g K L → cNorm L m (f - f₀) < δ → cNorm K m (g - g₀) < δ →
      cNorm K m (f ∘ g - f₀ ∘ g₀) < ε := by
  let A := cNorm L m f₀
  let B := 1 + cNorm K m g₀
  have hA : 0 ≤ A := cNorm_nonneg _ _ _
  have hB : 0 ≤ B := by dsimp [B]; linarith [cNorm_nonneg K m g₀]
  let C := jetDifferenceConstant m A B
  have hC : 0 ≤ C := jetDifferenceConstant_nonneg m hA hB
  let η := ε / (2 * (C + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  let J : F → (i : Fin (m + 1)) → F [×i.val]→L[ℝ] G :=
    fun y i ↦ iteratedFDeriv ℝ i.val f₀ y
  have hJ : ContinuousOn J L := by
    apply continuousOn_pi.mpr
    intro i y hy
    exact ((hf₀ y hy).continuousAt_iteratedFDeriv
      (by exact_mod_cast Nat.le_of_lt_succ i.isLt)).continuousWithinAt
  obtain ⟨d, hd, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hL.uniformContinuousOn_of_continuous hJ) (η / 2) (half_pos hη)
  refine ⟨min 1 (min d (η / 2)), lt_min zero_lt_one (lt_min hd (half_pos hη)), ?_⟩
  intro f g hf hg hrange hsmallf hsmallg
  have hdg : cNorm K m (g - g₀) < d :=
    hsmallg.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηg : cNorm K m (g - g₀) < η / 2 :=
    hsmallg.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hηf : cNorm L m (f - f₀) < η / 2 :=
    hsmallf.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have h1g : cNorm K m (g - g₀) < 1 := hsmallg.trans_le (min_le_left _ _)
  have hdiffg := fun i hi x hx ↦ norm_iteratedFDeriv_sub_le_cNorm hK hg hg₀ (i := i) hi (x := x) hx
  have hboundg₀ := fun i hi x hx ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hg₀
    (x := x) hx (j := i) hi
  have hb : cNorm K m (f ∘ g - f₀ ∘ g₀) ≤ C * η := by
    apply cNorm_comp_sub_le_of_jet_bounds (fun x hx ↦ hf _ (hrange hx))
      (fun x hx ↦ hf₀ _ (hrange₀ hx)) hg hg₀ hA hB hη.le
    · intro i hi x hx
      exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL hf₀ (hrange₀ hx) hi
    · intro i hi x hx
      refine ⟨(hboundg₀ i hi x hx).trans (by dsimp [B]; linarith), ?_⟩
      calc
        _ ≤ ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g₀ x‖ +
            ‖iteratedFDeriv ℝ i g₀ x‖ := by
              simpa only [sub_add_cancel] using
                norm_add_le (iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g₀ x)
                  (iteratedFDeriv ℝ i g₀ x)
        _ ≤ cNorm K m (g - g₀) + cNorm K m g₀ :=
          add_le_add (hdiffg i hi x hx) (hboundg₀ i hi x hx)
        _ ≤ B := by dsimp [B]; linarith
    · intro i hi x hx
      have hv : dist (g₀ x) (g x) < d := by
        rw [dist_eq_norm, norm_sub_rev]
        have hh := hdiffg 0 (Nat.zero_le m) x hx
        rw [← iteratedFDeriv_sub_apply ((hg x hx).of_le (by simp))
          ((hg₀ x hx).of_le (by simp)), norm_iteratedFDeriv_zero] at hh
        exact hh.trans_lt hdg
      have hj : ‖iteratedFDeriv ℝ i f₀ (g₀ x) - iteratedFDeriv ℝ i f₀ (g x)‖ < η / 2 := by
        have hh := (dist_le_pi_dist (J (g₀ x)) (J (g x)) ⟨i, Nat.lt_succ_of_le hi⟩).trans_lt
          (hmod _ (hrange₀ hx) _ (hrange hx) hv)
        simpa only [J, dist_eq_norm] using hh
      have hfDiff := norm_iteratedFDeriv_sub_le_cNorm hL hf hf₀ hi (hrange hx)
      rw [norm_sub_rev] at hfDiff
      exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (by linarith [hfDiff.trans_lt hηf])
    · intro i hi x hx
      rw [norm_sub_rev]
      exact (hdiffg i hi x hx).trans (by linarith)
  apply hb.trans_lt
  have he : η * (2 * (C + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  nlinarith

end JanetCartan.HamiltonPhase.CompositionContinuity
