module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.Inverse
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.SecondJet

/-!
# Differences of the actual transport gradient

Subtraction through the gradient integral in `app:ch_background:eq:bg-Psi`.
The consumer is the primitive-input inverse and Jacobian comparison for
`app:ch_osc:prop:osc-normal`, Step 4'. Both positions and the spectator vary.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation
open ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- Subtract the literal gradient integrals, using primitive smoothness to
justify integrability and the derivative subtraction (`bg-Psi`). -/
theorem transportAveragedGradient_sub_eq
    {V : Set (Euclidean n × (ℝ × Euclidean 2))} (hV : IsOpen V)
    {Y Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    (hY : ContDiffOn ℝ ∞ Y V) (hY₀ : ContDiffOn ℝ ∞ Y₀ V)
    {p : InputVariables n}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, transportSegmentInput n t p ∈ V) :
    transportAveragedGradient Y p - transportAveragedGradient Y₀ p =
      transportAveragedGradient (Y - Y₀) p := by
  have hs (Z : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (hZ : ContDiffOn ℝ ∞ Z V) :
      IntervalIntegrable (fun t ↦ transportSegmentGradient Z t p) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro t ht
    exact ((transportSegmentGradient_contDiffAt (z := (t, p))
      (hZ.contDiffAt (hV.mem_nhds (hseg t ht)))).comp t
        (contDiffAt_id.prodMk contDiffAt_const)).continuousAt.continuousWithinAt
  have hd (Z : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (hZ : ContDiffOn ℝ ∞ Z V) :
      ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ Z (transportSegmentInput n t p) :=
    fun t ht ↦ (hZ.contDiffAt (hV.mem_nhds (hseg t ht))).differentiableAt (by simp)
  rw [transportAveragedGradient_eq_integral_segment p (hd Y hY),
    transportAveragedGradient_eq_integral_segment p (hd Y₀ hY₀),
    transportAveragedGradient_eq_integral_segment p (hd (Y - Y₀) (hY.sub hY₀)),
    ← intervalIntegral.integral_sub (hs Y hY) (hs Y₀ hY₀)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  simp only [transportSegmentGradient]
  rw [fderiv_sub (hd Y hY t ht') (hd Y₀ hY₀ t ht'), map_sub, sub_apply]

private def gradientInsertion (n : ℕ) : Euclidean n →L[ℝ] Variables n × Euclidean 2 :=
  ((0 : Euclidean n →L[ℝ] Euclidean n).prod
    ((0 : Euclidean n →L[ℝ] Euclidean n).prod (ContinuousLinearMap.id ℝ _))).prod 0

private theorem augmented_sub_eq_insertion
    (Y Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)) :
    augmentedTransportGradient Y - augmentedTransportGradient Y₀ =
      gradientInsertion n ∘ (transportAveragedGradient Y - transportAveragedGradient Y₀) := by
  funext p
  simp [augmentedTransportGradient, gradientInsertion]

/-- A common constant controls the averaged gradient, its augmentation, and
its fixed normalization by the primitive difference. It precedes both inputs.
This supplies the forward premise of `exists_inverseCoordinates_sub_le` and
the differential premise of the Jacobian comparison (`bg-Psi`, Step 4'). -/
theorem exists_transportForward_sub_le
    {K W B : Set (InputVariables n)} (hKW : K ⊆ W)
    (hW : IsOpen W) (hB : IsCompact B) (hWB : W ⊆ B)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hsegT : ∀ t ∈ T, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀
      (Y Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)),
      ContDiffOn ℝ ∞ Y V → ContDiffOn ℝ ∞ Y₀ V →
      cNorm K m (transportAveragedGradient Y - transportAveragedGradient Y₀) ≤
          C * cNorm L (m + 1) (Y - Y₀) ∧
      cNorm K m (augmentedTransportGradient Y - augmentedTransportGradient Y₀) ≤
          C * cNorm L (m + 1) (Y - Y₀) ∧
      cNorm K m ((A.symm ∘ augmentedTransportGradient Y) -
        (A.symm ∘ augmentedTransportGradient Y₀)) ≤ C * cNorm L (m + 1) (Y - Y₀) := by
  let I := gradientInsertion n
  let R := A.symm.toContinuousLinearMap.comp I
  let D := ∑ j ∈ Finset.range (m + 1), transportIntegrandJetConstant B m j
  have hD : 0 ≤ D := Finset.sum_nonneg (fun j _ ↦ transportIntegrandJetConstant_nonneg B m j)
  refine ⟨1 + (1 + ‖I‖ + ‖R‖) * D, by positivity, ?_⟩
  intro Y Y₀ hY hY₀
  let f := transportAveragedGradient (Y - Y₀)
  have hf := transportAveragedGradient_contDiffOn hW hV hT hIT hsegT (hY.sub hY₀)
  have he (p) (hp : p ∈ K) :
      transportAveragedGradient Y - transportAveragedGradient Y₀ =ᶠ[𝓝 p] f :=
    (hW.eventually_mem (hKW hp)).mono (fun q hq ↦ transportAveragedGradient_sub_eq
      hV hY hY₀ (fun t ht ↦ hLV (hseg t ht hq)))
  have heI (p) (hp : p ∈ K) :
      augmentedTransportGradient Y - augmentedTransportGradient Y₀ =ᶠ[𝓝 p] I ∘ f := by
    rw [augmented_sub_eq_insertion]
    exact (he p hp).mono (fun q hq ↦ congrArg I hq)
  have heR (p) (hp : p ∈ K) :
      (A.symm ∘ augmentedTransportGradient Y) - (A.symm ∘ augmentedTransportGradient Y₀)
        =ᶠ[𝓝 p] R ∘ f := by
    filter_upwards [heI p hp] with q hq
    change A.symm (augmentedTransportGradient Y q) -
      A.symm (augmentedTransportGradient Y₀ q) = A.symm (I (f q))
    rw [← map_sub]
    exact congrArg A.symm hq
  have hb {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (P : Euclidean n →L[ℝ] E) :
      cNorm K m (P ∘ f) ≤ ‖P‖ * D * cNorm L (m + 1) (Y - Y₀) := by
    have hh := cNorm_le_sum_of_bounds (s := K) (r := m)
      (C := fun j ↦ ‖P‖ * (transportIntegrandJetConstant B m j * cNorm L (m + 1) (Y - Y₀)))
      (fun j _ ↦ mul_nonneg (norm_nonneg P) (mul_nonneg
        (transportIntegrandJetConstant_nonneg B m j) (cNorm_nonneg _ _ _))) (by
        intro j hj p hp
        exact (P.norm_iteratedFDeriv_comp_left (hf.contDiffAt (hW.mem_nhds (hKW hp)))
          (by simp)).trans (mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_transportAveragedGradient_le hW hB hWB hV hL hLV
              hseg (hY.sub hY₀) hj (hKW hp)) (norm_nonneg P)))
    simpa only [f, Pi.sub_def, D, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc] using hh
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq he m,
    GeometricProfile.cNorm_eq_of_eventuallyEq heI m,
    GeometricProfile.cNorm_eq_of_eventuallyEq heR m]
  have hN := cNorm_nonneg L (m + 1) (Y - Y₀)
  have hlarge : D ≤ 1 + (1 + ‖I‖ + ‖R‖) * D := by nlinarith [mul_nonneg (norm_nonneg I) hD, mul_nonneg (norm_nonneg R) hD]
  have hlargeI : ‖I‖ * D ≤ 1 + (1 + ‖I‖ + ‖R‖) * D := by nlinarith [mul_nonneg (norm_nonneg I) hD, mul_nonneg (norm_nonneg R) hD]
  have hlargeR : ‖R‖ * D ≤ 1 + (1 + ‖I‖ + ‖R‖) * D := by nlinarith [mul_nonneg (norm_nonneg I) hD, mul_nonneg (norm_nonneg R) hD]
  exact ⟨(cNorm_transportAveragedGradient_le hKW hW hB hWB hV hL hLV hseg
      (hY.sub hY₀) m).trans (mul_le_mul_of_nonneg_right hlarge hN),
    (hb I).trans (mul_le_mul_of_nonneg_right hlargeI hN),
    (hb R).trans (mul_le_mul_of_nonneg_right hlargeR hN)⟩

end JanetCartan.ContinuumNormal.CarrierVariation
