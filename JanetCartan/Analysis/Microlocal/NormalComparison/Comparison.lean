module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Integrating the transport-channel estimate

This is the final Banach-space step in `app:ch_osc:prop:osc-normal`, conditional
on the operator derivative decomposition and the channel bounds. It does not
assert those analytic inputs for the oscillatory kernels.
-/

@[expose] public section

open Set

namespace JanetCartan.NormalComparison

/-- Closed-interval derivative version of the conditional last step of `app:ch_osc:prop:osc-normal`. A bounded undifferentiated
mask channel and `n` channels of size `B L / h` give the `ε / h` estimate.
For the manuscript application `F` is the space of bounded operators on L²,
`Q₀ = N(c₀,m)`, and `Qⱼ = N(cⱼ,∂ⱼm)`. These inputs still require proof. -/
theorem norm_sub_le_of_transport_channels_within
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (E Q₀ : ℝ → F) (Q : ℝ → Fin n → F)
    {ε h B L : ℝ} (hε : 0 ≤ ε) (hh : 0 < h) (hh₁ : h ≤ 1) (hB : 0 ≤ B)
    (hE : ∀ t ∈ Icc 0 ε, HasDerivWithinAt E (Q₀ t + ∑ j, Q t j) (Icc 0 ε) t)
    (hQ₀ : ∀ t ∈ Icc 0 ε, ‖Q₀ t‖ ≤ B)
    (hQ : ∀ t ∈ Icc 0 ε, ∀ j, ‖Q t j‖ ≤ B * L / h) :
    ‖E ε - E 0‖ ≤ B * (1 + (n : ℝ) * L) * ε / h := by
  have bound : ∀ t ∈ Ico 0 ε, ‖Q₀ t + ∑ j, Q t j‖ ≤
      B * (1 + (n : ℝ) * L) / h := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    calc
      ‖Q₀ t + ∑ j, Q t j‖ ≤ ‖Q₀ t‖ + ‖∑ j, Q t j‖ := norm_add_le _ _
      _ ≤ B + ∑ j, ‖Q t j‖ := add_le_add (hQ₀ t ht') (norm_sum_le _ _)
      _ ≤ B + ∑ _j : Fin n, B * L / h :=
        add_le_add le_rfl (Finset.sum_le_sum (fun j _ ↦ hQ t ht' j))
      _ = B + (n : ℝ) * (B * L / h) := by simp
      _ ≤ B * (1 + (n : ℝ) * L) / h := by
        apply (le_div_iff₀ hh).2
        have hBh : B * h ≤ B := by nlinarith
        calc
          (B + (n : ℝ) * (B * L / h)) * h = B * h + (n : ℝ) * (B * L) := by
            field_simp
          _ ≤ B + (n : ℝ) * (B * L) := add_le_add hBh le_rfl
          _ = B * (1 + (n : ℝ) * L) := by ring
  have est := norm_image_sub_le_of_norm_deriv_le_segment'
    hE bound ε ⟨hε, le_rfl⟩
  simpa only [sub_zero, div_mul_eq_mul_div] using est

/-- Conditional last step of `app:ch_osc:prop:osc-normal`. A bounded undifferentiated
mask channel and `n` channels of size `B L / h` give the `ε / h` estimate.
For the manuscript application `F` is the space of bounded operators on L²,
`Q₀ = N(c₀,m)`, and `Qⱼ = N(cⱼ,∂ⱼm)`. These inputs still require proof. -/
theorem norm_sub_le_of_transport_channels
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (E Q₀ : ℝ → F) (Q : ℝ → Fin n → F)
    {ε h B L : ℝ} (hε : 0 ≤ ε) (hh : 0 < h) (hh₁ : h ≤ 1) (hB : 0 ≤ B)
    (hE : ∀ t ∈ Icc 0 ε, HasDerivAt E (Q₀ t + ∑ j, Q t j) t)
    (hQ₀ : ∀ t ∈ Icc 0 ε, ‖Q₀ t‖ ≤ B)
    (hQ : ∀ t ∈ Icc 0 ε, ∀ j, ‖Q t j‖ ≤ B * L / h) :
    ‖E ε - E 0‖ ≤ B * (1 + (n : ℝ) * L) * ε / h := by
  exact norm_sub_le_of_transport_channels_within E Q₀ Q hε hh hh₁ hB
    (fun t ht ↦ (hE t ht).hasDerivWithinAt) hQ₀ hQ

end JanetCartan.NormalComparison
