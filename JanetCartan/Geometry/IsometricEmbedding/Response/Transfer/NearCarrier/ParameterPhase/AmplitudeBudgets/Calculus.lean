module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Finite local calculus for the carrier amplitude

Finite-order versions of the open-set composition estimates, used by
`norm_iteratedFDeriv_normalizedParameterAmplitude_le` in the amplitude step of
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer.ParameterAmplitudeBudget

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite primitive jets restrict along a contraction without loss, for the
selector and carrier projections in `app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_comp_contraction_le (L : E →L[ℝ] H) (hL : ‖L‖ ≤ 1)
    {f : H → F} {V : Set H} (hV : IsOpen V) {N k : ℕ}
    (hf : ContDiffOn ℝ N f V) (hk : k ≤ N) {p : E} (hp : L p ∈ V) :
    ‖iteratedFDeriv ℝ k (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ k f (L p)‖ := by
  have hpre : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hV.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := k) (by exact_mod_cast hk)
  rw [iteratedFDerivWithin_of_isOpen _ hpre hp,
    iteratedFDerivWithin_of_isOpen _ hV hp] at h
  rw [h]
  exact ((iteratedFDeriv ℝ k f (L p)).norm_compContinuousLinearMap_le
    (fun _ ↦ L)).trans (by
      simpa using mul_le_of_le_one_right (norm_nonneg (iteratedFDeriv ℝ k f (L p)))
        (pow_le_one₀ (norm_nonneg L) hL))

/-- Explicit finite composition constant on the buffered open chart, used for
`Aρ(x,y,ζ(c)+ε)` in `app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_comp_le {f : E → H} {g : H → F} {U : Set E} {V : Set H}
    (hU : IsOpen U) (hV : IsOpen V) {N k : ℕ}
    (hf : ContDiffOn ℝ N f U) (hg : ContDiffOn ℝ N g V)
    (hmap : MapsTo f U V) (hk : k ≤ N) {p : E} (hp : p ∈ U) {A B : ℝ}
    (hgjet : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f p)‖ ≤ A)
    (hfjet : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f p‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (g ∘ f) p‖ ≤ (k.factorial : ℝ) * A * (max 1 B)^k := by
  have h := norm_iteratedFDerivWithin_comp_le hg hf (n := k) (by exact_mod_cast hk)
    hV.uniqueDiffOn hU.uniqueDiffOn hmap hp
    (fun i hi ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ hV (hmap hp)]
      exact hgjet i hi)
    (fun i hi hik ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ hU hp]
      exact ((hfjet i hi hik).trans (le_max_right 1 B)).trans
        (le_self_pow₀ (le_max_left 1 B) (by omega)))
  rwa [iteratedFDerivWithin_of_isOpen _ hU hp] at h

/-- Positive jets of a linear contraction, used for the physical positions in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_positive_jet_linear_le (L : E →L[ℝ] H) (hL : ‖L‖ ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) (p : E) : ‖iteratedFDeriv ℝ k L p‖ ≤ 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ ↦ L := funext (fun _ ↦ L.fderiv)
  rw [he]
  cases j with
  | zero => simpa using hL
  | succ j => simp [iteratedFDeriv_succ_const]

end JanetCartan.ResponseTransfer.ParameterAmplitudeBudget
