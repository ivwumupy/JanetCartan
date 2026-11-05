module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.ForwardJets.Integral

/-! # Primitive mixed jets imply transport forward bounds

For `app:ch_background:eq:bg-Psi`, the literal averaged gradient and its
augmentation retain `x`, `x'`, `s`, `v`, and `η`. Their joint seminorms are
linear in the `C^(m+1)` norm of `Y` on a fixed compact primitive domain.
The constants precede `Y`. The final theorem transfers the one-high primitive
budget in `app:ch_background:eq:bg-mixed-input` with fixed loss `D + 1`.

Consumer: the smoothness and forward high-bound premises of
`exists_inverseCoordinates_fixedShift_bound`. Inverse identities, differential
gaps and the final inverse/Jacobian assembly remain the consumer's obligations.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

private def transportUnchangedCoordinates (n : ℕ) :
    InputVariables n →L[ℝ] Variables n × Euclidean 2 :=
  let xy := ContinuousLinearMap.fst ℝ (Euclidean n × Euclidean n)
    ((ℝ × Euclidean 2) × Euclidean (n - 1))
  let x := (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).comp xy
  let y := (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)).comp xy
  let v := (ContinuousLinearMap.snd ℝ ℝ (Euclidean 2)).comp
    ((ContinuousLinearMap.fst ℝ (ℝ × Euclidean 2) (Euclidean (n - 1))).comp
      (ContinuousLinearMap.snd ℝ (Euclidean n × Euclidean n)
        ((ℝ × Euclidean 2) × Euclidean (n - 1))))
  (x.prod (y.prod 0)).prod v

private def transportGradientInsertion (n : ℕ) :
    Euclidean n →L[ℝ] Variables n × Euclidean 2 :=
  (0 : Euclidean n →L[ℝ] Euclidean n).prod
    ((0 : Euclidean n →L[ℝ] Euclidean n).prod (ContinuousLinearMap.id ℝ _)) |>.prod 0

private theorem augmentedTransportGradient_eq_add
    (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)) :
    augmentedTransportGradient Y = (transportUnchangedCoordinates n : InputVariables n → _) +
      (transportGradientInsertion n ∘ transportAveragedGradient Y) := by
  funext p
  simp [augmentedTransportGradient, transportUnchangedCoordinates, transportGradientInsertion]

/-- Smoothness of the full augmented forward map is deduced from primitive
smoothness and segment containment (`app:ch_background:eq:bg-Psi`). -/
theorem augmentedTransportGradient_contDiffOn
    {U : Set (InputVariables n)} (hU : IsOpen U)
    {V : Set (Euclidean n × (ℝ × Euclidean 2))} (hV : IsOpen V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hseg : ∀ t ∈ T, MapsTo (transportSegmentInput n t) U V)
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    (hY : ContDiffOn ℝ ∞ Y V) : ContDiffOn ℝ ∞ (augmentedTransportGradient Y) U := by
  rw [augmentedTransportGradient_eq_add]
  exact (transportUnchangedCoordinates n).contDiff.contDiffOn.add
    ((transportGradientInsertion n).contDiff.comp_contDiffOn
      (transportAveragedGradient_contDiffOn hU hV hT hIT hseg hY))

/-- On any fixed compact subset of a buffered bounded input domain, both
literal forward maps have a one-high bound with loss exactly one. In particular
`S` may be the closed input ball of `exists_inverseCoordinates_fixedShift_bound`.
All domain and covector constants precede `Y`
(`app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-mixed-input`). -/
theorem exists_transportForward_cNorm_bound
    {S U K : Set (InputVariables n)} (hS : IsCompact S) (hSU : S ⊆ U)
    (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) U V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) U L) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)),
      ContDiffOn ℝ ∞ Y V → ∀ m,
        cNorm S m (transportAveragedGradient Y) ≤ C m * (1 + cNorm L (m + 1) Y) ∧
        cNorm S m (augmentedTransportGradient Y) ≤ C m * (1 + cNorm L (m + 1) Y) := by
  let Q := transportUnchangedCoordinates n
  let I := transportGradientInsertion n
  let B := fun m ↦ ∑ j ∈ Finset.range (m + 1), transportIntegrandJetConstant K m j
  have hB (m : ℕ) : 0 ≤ B m :=
    Finset.sum_nonneg (fun j _ ↦ transportIntegrandJetConstant_nonneg K m j)
  let D := fun m ↦ ((m + 1 : ℕ) : ℝ) * cNorm S m (Q : InputVariables n → _)
  have hD (m : ℕ) : 0 ≤ D m := mul_nonneg (by positivity) (cNorm_nonneg _ _ _)
  refine ⟨fun m ↦ 1 + D m + (1 + ‖I‖) * B m, fun m ↦ by
    have := mul_nonneg (by positivity : 0 ≤ 1 + ‖I‖) (hB m)
    linarith [hD m], ?_⟩
  intro Y hY m
  have hg := transportAveragedGradient_contDiffOn hU hV hT hIT hsegT hY
  have hb := cNorm_transportAveragedGradient_le hSU hU hK hUK hV hL hLV hseg hY m
  have hj : ∀ j ≤ m, ∀ p ∈ S,
      ‖iteratedFDeriv ℝ j (augmentedTransportGradient Y) p‖ ≤
        cNorm S m (Q : InputVariables n → _) +
          ‖I‖ * (transportIntegrandJetConstant K m j * cNorm L (m + 1) Y) := by
    intro j hj p hp
    have hgp := hg.contDiffAt (hU.mem_nhds (hSU hp))
    rw [augmentedTransportGradient_eq_add]
    change ‖iteratedFDeriv ℝ j (fun p ↦ Q p + (I ∘ transportAveragedGradient Y) p) p‖ ≤ _
    rw [fun_iteratedFDeriv_add_apply ((Q.contDiff (n := j)).contDiffAt)
      ((I.contDiff (n := j)).contDiffAt.comp p (hgp.of_le (by simp)))]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hS (fun _ _ ↦ Q.contDiff.contDiffAt) hp hj
    · exact (I.norm_iteratedFDeriv_comp_left hgp (by simp)).trans
        (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_transportAveragedGradient_le
          hU hK hUK hV hL hLV hseg hY hj (hSU hp)) (norm_nonneg I))
  have ha : cNorm S m (augmentedTransportGradient Y) ≤
      D m + ‖I‖ * B m * cNorm L (m + 1) Y := by
    apply (cNorm_le_sum_of_bounds (fun j _ ↦ add_nonneg (cNorm_nonneg _ _ _)
      (mul_nonneg (norm_nonneg I) (mul_nonneg
        (transportIntegrandJetConstant_nonneg K m j) (cNorm_nonneg _ _ _)))) hj).trans_eq
    simp [D, B, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  have hN := cNorm_nonneg L (m + 1) Y
  constructor
  · apply hb.trans
    change B m * cNorm L (m + 1) Y ≤ _
    nlinarith [hB m, hD m, mul_nonneg (hD m) hN, mul_nonneg (norm_nonneg I) (hB m),
      mul_nonneg (mul_nonneg (norm_nonneg I) (hB m)) hN]
  · apply ha.trans
    nlinarith [hB m, hD m, mul_nonneg (hD m) hN, mul_nonneg (norm_nonneg I) (hB m),
      mul_nonneg (hB m) hN]

/-- Transfer of the primitive geometry budget to the actual augmented forward
map, with one high geometry norm and fixed shift `D + 1`. This discharges the
forward smoothness and high-bound premises of
`exists_inverseCoordinates_fixedShift_bound`; no forward or inverse high bound
is an input (`app:ch_background:eq:bg-mixed-input`). -/
theorem exists_transportForward_fixedShift_bound
    {S U K : Set (InputVariables n)} (hS : IsCompact S) (hSU : S ⊆ U)
    (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) U V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) U L)
    (D : ℕ) (B : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)) (H : ℕ → ℝ),
      ContDiffOn ℝ ∞ Y V → (∀ j, 0 ≤ H j) →
      (∀ j, cNorm L j Y ≤ B j * (1 + H (j + D))) →
      ContDiffOn ℝ ∞ (augmentedTransportGradient Y) U ∧
      ∀ m, cNorm S m (transportAveragedGradient Y) ≤ C m * (1 + H (m + (D + 1))) ∧
        cNorm S m (augmentedTransportGradient Y) ≤ C m * (1 + H (m + (D + 1))) := by
  obtain ⟨C, hC, hb⟩ := exists_transportForward_cNorm_bound
    hS hSU hU hK hUK hV hL hLV hT hIT hsegT hseg
  refine ⟨fun m ↦ C m * (1 + B (m + 1)), fun m ↦ mul_pos (hC m) (by linarith [hB (m + 1)]), ?_⟩
  intro Y H hY hH hjet
  refine ⟨augmentedTransportGradient_contDiffOn hU hV hT hIT hsegT hY, ?_⟩
  intro m
  have hprim := hjet (m + 1)
  rw [show m + 1 + D = m + (D + 1) by omega] at hprim
  have hbound : C m * (1 + cNorm L (m + 1) Y) ≤
      C m * (1 + B (m + 1)) * (1 + H (m + (D + 1))) := by
    apply (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hprim) (hC m).le).trans
    nlinarith [mul_nonneg (hC m).le (hH (m + (D + 1)))]
  exact ⟨((hb Y hY m).1).trans hbound, ((hb Y hY m).2).trans hbound⟩

end JanetCartan.ContinuumNormalReduction.TransportSymbol
