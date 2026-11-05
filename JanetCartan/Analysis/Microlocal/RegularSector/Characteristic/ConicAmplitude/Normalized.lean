module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicAmplitude.JetBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.EvolutionCoordinates
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ConicPhase.JetBounds.Normalized
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Amplitude

/-!
# Actual normalized symbol budgets for the continued matrices

Radial homogeneity removes the shell radius before differentiating. The
remaining fixed coordinate regrouping and section map cost zero derivatives.
This connects the literal local matrices in `AmplitudeBounds` to the original
order-zero/order-minus-one inputs of `EvolutionIntegral.SymbolBudgets`, in
`app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.ConicAmplitude
open EvolutionIntegral SymbolBudgets AmplitudeBounds

variable {d n : ℕ}

/-- The normalized shell field is literally independent of the positive
shell radius. This proves the required symbol order for the actual continued
matrix (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem twoTimeOrderField_curry_extend (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (f : Characteristic.TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ)
    {R : ℝ} (hR : R ≠ 0) :
    twoTimeOrderField o R (curryCharacteristicMatrix (extend ℓ o f)) =
      jointAmplitude (curryCharacteristicMatrix (extend ℓ o f)) := by
  funext p
  change R ^ o • extend ℓ o f (p.1.1, (p.1.2.1, (p.1.2.2, R • p.2))) = _
  rw [extend_smul ℓ o f (p.1.1, (p.1.2.1, (p.1.2.2, p.2))) hR,
    smul_smul, ← mul_pow, mul_inv_cancel₀ hR, one_pow, one_smul]
  rfl

/-- The actual normalized seminorm is finite; no bounded-symbol premise is
needed for the radial continuation (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem boundedTwoTimeOrderSeminorm_curry_extend (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (K : Set (SymbolBudgets.TwoTimePoint d)) (m : ℕ)
    (f : Characteristic.TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ) :
    BoundedTwoTimeOrderSeminorm o K m (curryCharacteristicMatrix (extend ℓ o f)) := by
  refine ⟨cNorm K m (jointAmplitude (curryCharacteristicMatrix (extend ℓ o f))), ?_⟩
  rintro _ ⟨R, rfl⟩
  dsimp only
  rw [twoTimeOrderField_curry_extend ℓ o f (lt_of_lt_of_le zero_lt_one R.2).ne']

/-- The shell supremum equals the single normalized-section seminorm,
including every time and covector derivative (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem twoTimeOrderSeminorm_curry_extend (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (K : Set (SymbolBudgets.TwoTimePoint d)) (m : ℕ)
    (f : Characteristic.TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ) :
    twoTimeOrderSeminorm o K m (curryCharacteristicMatrix (extend ℓ o f)) =
      cNorm K m (jointAmplitude (curryCharacteristicMatrix (extend ℓ o f))) := by
  have he (R : {R : ℝ // 1 ≤ R}) :=
    twoTimeOrderField_curry_extend ℓ o f (lt_of_lt_of_le zero_lt_one R.2).ne'
  simp only [twoTimeOrderSeminorm, he, range_const, csSup_singleton]

/-- Smoothness of the actual continued matrix in the consumer's joint
coordinates (`app:ch_regular_base:lem:retarded-kernel`). -/
theorem contDiffOn_jointAmplitude_curry_extend (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    {U : Set (Characteristic.TwoTimePoint (Euclidean d))} (hU : IsOpen U)
    {f : Characteristic.TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ}
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (jointAmplitude (curryCharacteristicMatrix (extend ℓ o f)))
      (evolutionToCharacteristicPoint ⁻¹' ConicPhase.domain ℓ U) :=
  (contDiffOn_extend ℓ o hU hf).comp evolutionToCharacteristicPoint.contDiff.contDiffOn
    (fun _ hp ↦ hp)

/-- Fixed constant for the actual normalized matrix symbol; it is chosen
before the local matrix and every shell radius
(`app:ch_regular_base:lem:retarded-kernel`). -/
def symbolBoundConstant (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (K : Set (SymbolBudgets.TwoTimePoint d)) (m : ℕ) : ℝ :=
  jetBoundConstant (F := Matrix (Fin n) (Fin n) ℂ) ℓ o (evolutionToCharacteristicPoint '' K) m

/-- Positivity of the fixed normalized symbol constant
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem symbolBoundConstant_pos (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    (K : Set (SymbolBudgets.TwoTimePoint d)) (m : ℕ) :
    0 < symbolBoundConstant (n := n) ℓ o K m := jetBoundConstant_pos _ _ _ _

/-- The actual spatial symbol budget follows linearly from the local
amplitude budget, at the same derivative order and uniformly over all
shells. In particular the local reserve nine remains nine
(`app:ch_regular_base:lem:retarded-kernel`). -/
theorem twoTimeOrderSeminorm_curry_extend_le (ℓ : Euclidean d →L[ℝ] ℝ) (o : ℕ)
    {K : Set (SymbolBudgets.TwoTimePoint d)}
    {J U : Set (Characteristic.TwoTimePoint (Euclidean d))}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (hpos : ∀ p ∈ K, 0 < ℓ p.2)
    (hmap : MapsTo (ConicPhase.normalize ℓ ∘ evolutionToCharacteristicPoint) K J)
    {f : Characteristic.TwoTimePoint (Euclidean d) → Matrix (Fin n) (Fin n) ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) :
    twoTimeOrderSeminorm o K m (curryCharacteristicMatrix (extend ℓ o f)) ≤
      symbolBoundConstant (n := n) ℓ o K m * cNorm J m f := by
  rw [twoTimeOrderSeminorm_curry_extend, jointAmplitude_curryCharacteristicMatrix]
  have himage := hK.image (evolutionToCharacteristicPoint (d := d)).continuous
  have himagepos : ∀ q ∈ evolutionToCharacteristicPoint '' K, 0 < ℓ q.2.2.2 := by
    rintro q ⟨p, hp, rfl⟩
    exact hpos p hp
  have himagemap : MapsTo (ConicPhase.normalize ℓ) (evolutionToCharacteristicPoint '' K) J := by
    rintro q ⟨p, hp, rfl⟩
    exact hmap hp
  have hsubset : evolutionToCharacteristicPoint '' K ⊆ ConicPhase.domain ℓ U :=
    fun q hq ↦ ⟨himagepos q hq, hJU (himagemap hq)⟩
  have h := cNorm_preAffine_contraction_le evolutionToCharacteristicPoint
    (show ‖evolutionToCharacteristicPoint (d := d)‖ ≤ 1 from ConicPhase.norm_budgetCoordinates_le)
    0 himage (ConicPhase.isOpen_domain ℓ hU) hsubset (contDiffOn_extend ℓ o hU hf)
    (show MapsTo (fun p ↦ evolutionToCharacteristicPoint p + 0) K
      (evolutionToCharacteristicPoint '' K) by
        simpa only [add_zero] using mapsTo_image (evolutionToCharacteristicPoint (d := d)) K) m
  simp only [add_zero] at h
  exact h.trans (cNorm_extend_le ℓ o himage hJ hU hJU himagepos himagemap hf m)

end JanetCartan.RegularSector.Characteristic.ConicAmplitude
