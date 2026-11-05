module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Calculus
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets

/-!
# Reserve-graded selected amplitude

The selected-amplitude primitive for `app:ch_response:eq:direct-envelope-profile`
and `NearCarrierSymbol.hasFullSourceSymbolBound_of_expression`. The derivatives
are joint in both physical positions, normalized covector, and carrier parameter.
The amplitude includes every physical and frequency mask. Only its unshifted
annular profile, fixed selector jets, and fixed carrier jets are inputs.

The response geometry producer must supply these finite profiles uniformly in
frequency and scale on the buffered chart. The parent construction supplies the
global smooth extension. The constants here do not depend on either frequency or
scale. Take `R = Rstar - 2` and use `reserve_exponent` for the consumer's exponent.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives
open FourierIntegral ParameterAmplitudeBudget

/-- The finite Leibniz/chain constant for the selected amplitude in
`app:ch_response:eq:direct-envelope-profile`, chosen before frequency and scale. -/
def selectedAmplitudeConstant (A Q : ℕ → ℝ) (Z : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Q i *
    compositionConstant A (fun _ ↦ 1 + Z) (k - i)

/-- Positivity needed to instantiate the primitive expression budget in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem selectedAmplitudeConstant_nonneg {A Q : ℕ → ℝ} {Z : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hQ : ∀ j, 0 ≤ Q j) (hZ : 0 ≤ Z) (k : ℕ) :
    0 ≤ selectedAmplitudeConstant A Q Z k :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (hQ _))
    (compositionConstant_nonneg hA (fun _ ↦ by positivity) _)

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Finite reserve-graded jets of the actual selected amplitude. The joint
order `k` counts all physical, normalized covector, and parameter derivatives
together. No inverse or selected-amplitude jets are assumed. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_normalizedParameterAmplitude_le
    {a : FullAmplitude n r} {q : P × Euclidean n → ℂ} {ζ : P → Euclidean n}
    {ρ : ℝ} {N k R : ℕ} {U : Set (ParameterAmplitudePoint n P)}
    {V : Set (Euclidean n × Euclidean n × Euclidean n)}
    {W : Set (P × Euclidean n)} {C : Set P}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W) (hC : IsOpen C)
    (ha : ContDiffOn ℝ N (normalizedFullAmplitude a ρ) V)
    (hq : ContDiffOn ℝ N q W) (hζ : ContDiffOn ℝ N ζ C)
    (hUV : MapsTo (carrierAmplitudeShift ζ) U V)
    (hUW : ∀ p ∈ U, (p.2, p.1.2.2) ∈ W) (hUC : ∀ p ∈ U, p.2 ∈ C)
    {A Q : ℕ → ℝ} {Z L : ℝ}
    (hA : ∀ j, 0 ≤ A j) (hQ : ∀ j, 0 ≤ Q j) (hZ : 0 ≤ Z) (hL : 1 ≤ L)
    (hajet : ∀ j ≤ N, ∀ v ∈ V,
      ‖iteratedFDeriv ℝ j (normalizedFullAmplitude a ρ) v‖ ≤ A j * L ^ (j - R))
    (hqjet : ∀ j ≤ N, ∀ w ∈ W, ‖iteratedFDeriv ℝ j q w‖ ≤ Q j)
    (hζjet : ∀ j, 1 ≤ j → j ≤ N → ∀ c ∈ C, ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z)
    (hk : k ≤ N) {p : ParameterAmplitudePoint n P} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ k (normalizedParameterAmplitude a q ζ ρ) p‖ ≤
      selectedAmplitudeConstant A Q Z k * L ^ (k - R) := by
  let f := q ∘ (selectorProjection (n := n) (P := P))
  let g := normalizedFullAmplitude a ρ ∘ carrierAmplitudeShift ζ
  have hf : ContDiffOn ℝ N f U :=
    hq.comp (selectorProjection (n := n) (P := P)).contDiff.contDiffOn hUW
  have hg : ContDiffOn ℝ N g U :=
    ha.comp (carrierAmplitudeShift_contDiffOn hζ hUC) hUV
  have hfjet (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j f p‖ ≤ Q j :=
    (norm_jet_comp_contraction_le (selectorProjection (n := n) (P := P))
      norm_selectorProjection_le hW hq hj (p := p) (hUW p hp)).trans
        (hqjet j hj _ (hUW p hp))
  have hgjet (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j g p‖ ≤
        compositionConstant A (fun _ ↦ 1 + Z) j * L ^ (j - R) :=
    norm_jet_comp_fixed_inner_le
      ((carrierAmplitudeShift_contDiffOn hζ hUC).contDiffAt (hU.mem_nhds hp))
      (ha.contDiffAt (hV.mem_nhds (hUV hp))) hj A (fun _ ↦ 1 + Z) hA
      (fun _ ↦ by positivity) hL R
      (fun i hi ↦ hajet i (hi.trans hj) _ (hUV hp))
      (fun i hi hij ↦ norm_jet_carrierAmplitudeShift_le hC hζ (hij.trans hj) hi
        (hUC p hp) (hζjet i hi (hij.trans hj) _ (hUC p hp)))
  have hb := norm_iteratedFDerivWithin_smul_le hf hg hU.uniqueDiffOn hp
    (n := k) (by exact_mod_cast hk)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hp] at hb
  change ‖iteratedFDeriv ℝ k (fun u ↦ f u • g u) p‖ ≤ _
  apply hb.trans
  rw [selectedAmplitudeConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
  calc
    _ ≤ (k.choose i : ℝ) * Q i *
        (compositionConstant A (fun _ ↦ 1 + Z) (k - i) * L ^ (k - i - R)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfjet i (hik.trans hk)) (Nat.cast_nonneg _))
        (hgjet _ ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hQ _))
    _ = ((k.choose i : ℝ) * Q i *
        compositionConstant A (fun _ ↦ 1 + Z) (k - i)) * L ^ (k - i - R) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL (by omega))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hQ _))
        (compositionConstant_nonneg hA (fun _ ↦ by positivity) _))

end JanetCartan.ResponseTransfer.GradedPrimitives
