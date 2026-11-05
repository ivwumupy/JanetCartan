module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ComplexAmplitude

/-!
# Physical coordinates and reflection for amplitude differences

The global matrix-jet conclusion of `ShellTransfer.Global` is converted to
the literal full amplitudes with `k = 2πξ`. Reflection has exactly the
existing factor two multiplying the sum at `ξ` and `-ξ`, hence costs four.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and `bg-real-symbol`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
open ContinuumNormalReduction.TransportSymbol ContinuumRow CarrierNormalRealization
open TransportKernel Pseudodifferential AmplitudeBound
variable {n N : ℕ}

private def physicalPositionInclusion : Euclidean (2 * n) →L[ℝ] Variables n :=
  freezingOutputProjection.prod (freezingSourceProjection.prod 0)

private theorem exists_physicalEntry_jet_bound (s : ℕ) :
    ∃ C > 0, ∀ (f : Variables n → Matrix (Fin n) (Fin n) ℝ), ContDiff ℝ ∞ f →
      ∀ A : ℝ, 0 ≤ A → (∀ p, ∀ k ≤ s, ‖iteratedFDeriv ℝ k f p‖ ≤ A) →
      ∀ (ξ : Euclidean n) (i j : Fin n),
      ContDiff ℝ ∞ (fun z ↦ (((2 * Real.pi) ^ n *
        f (freezingOutputProjection z, freezingSourceProjection z, (2 * Real.pi) • ξ) i j : ℝ) : ℂ)) ∧
      ∀ z, ∀ k ≤ s, ‖iteratedFDeriv ℝ k (fun z ↦ (((2 * Real.pi) ^ n *
        f (freezingOutputProjection z, freezingSourceProjection z, (2 * Real.pi) • ξ) i j : ℝ) : ℂ)) z‖ ≤
        C * A := by
  let L (i j : Fin n) := Complex.ofRealCLM.comp (realMatrixEntry i j)
  let E := (∑ i, ∑ j, ‖L i j‖) + 1
  have hE : 0 < E := by dsimp [E]; positivity
  have hLE (i j : Fin n) : ‖L i j‖ ≤ E := by
    calc
      _ ≤ ∑ j, ‖L i j‖ := Finset.single_le_sum (fun j _ ↦ norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, ‖L i j‖ := Finset.single_le_sum
        (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ norm_nonneg _)) (Finset.mem_univ i)
      _ ≤ E := le_add_of_nonneg_right zero_le_one
  let D := max 1 ‖physicalPositionInclusion (n := n)‖
  have hD : 1 ≤ D := le_max_left _ _
  let c := (2 * Real.pi) ^ n
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨E * c * D ^ s, by positivity, ?_⟩
  intro f hf A hA hm ξ i j
  let g := L i j ∘ (c • f)
  have hg : ContDiff ℝ ∞ g := (L i j).contDiff.comp (hf.const_smul c)
  have hjoint (p : Variables n) (k : ℕ) (hk : k ≤ s) :
      ‖iteratedFDeriv ℝ k g p‖ ≤ E * c * A := by
    apply ((L i j).norm_iteratedFDeriv_comp_left (hf.const_smul c).contDiffAt (by simp)).trans
    change ‖L i j‖ * ‖iteratedFDeriv ℝ k (c • f) p‖ ≤ E * c * A
    rw [iteratedFDeriv_const_smul_apply (i := k) (a := c) (hf.contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact (mul_le_mul (hLE i j) (mul_le_mul_of_nonneg_left (hm p k hk) hc.le)
      (by positivity) hE.le).trans_eq (by ring)
  have hfun : (fun z ↦ (((2 * Real.pi) ^ n *
        f (freezingOutputProjection z, freezingSourceProjection z, (2 * Real.pi) • ξ) i j : ℝ) : ℂ)) =
      (fun p ↦ g (p + (0, 0, (2 * Real.pi) • ξ))) ∘ physicalPositionInclusion := by
    funext z
    simp [g, L, c, physicalPositionInclusion, Function.comp_def, realMatrixEntry]
  rw [hfun]
  have hsmooth : ContDiff ℝ ∞ (fun p ↦ g (p + (0, 0, (2 * Real.pi) • ξ))) :=
    hg.comp (contDiff_id.add contDiff_const)
  refine ⟨hsmooth.comp physicalPositionInclusion.contDiff, ?_⟩
  intro z k hk
  apply (norm_iteratedFDeriv_comp_linear_le physicalPositionInclusion _ hsmooth k z).trans
  rw [iteratedFDeriv_comp_add_right]
  have hpow : ‖physicalPositionInclusion (n := n)‖ ^ k ≤ D ^ s :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hD hk)
  exact (mul_le_mul (hjoint _ k hk) hpow (by positivity) (by positivity)).trans_eq (by ring)

/-- The physical conversion of a global matrix difference estimate gives
both literal full-amplitude bounds. This intermediate implication is consumed
by `exists_fullAmplitude_sub_bounds_of_supported_shell`, which supplies its
global-jet input from primitive shell density estimates. The factor four is
the existing reflection normalization, not an additional quadrature factor.
Source: `app:ch_background:eq:bg-full-complex-amplitude` and `bg-real-symbol`. -/
theorem exists_fullAmplitude_sub_bounds_of_global_jets (s : ℕ) :
    ∃ C > 0, ∀ (a : Fin 2 → Coefficients n N) (J : Fin 2 → InputVariables n → ℝ)
      (u : Fin 2 → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)),
      ContDiff ℝ ∞ (amplitude (a 0) (J 0) (u 0) Ω S - amplitude (a 1) (J 1) (u 1) Ω S) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ p, ∀ k ≤ s, ‖iteratedFDeriv ℝ k
        (amplitude (a 0) (J 0) (u 0) Ω S - amplitude (a 1) (J 1) (u 1) Ω S) p‖ ≤ A) →
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude (a 0) (J 0) (u 0) Ω S ξ z i j -
          fullComplexMatrixAmplitude (a 1) (J 1) (u 1) Ω S ξ z i j) s (C * A) ∧
        HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude (a 0) (J 0) (u 0) Ω S ξ z i j -
          fullReflectedMatrixAmplitude (a 1) (J 1) (u 1) Ω S ξ z i j) s (4 * (C * A)) := by
  obtain ⟨C, hC, hb⟩ := exists_physicalEntry_jet_bound (n := n) s
  refine ⟨C, hC, ?_⟩
  intro a J u Ω S hf A hA hj i j
  let f := amplitude (a 0) (J 0) (u 0) Ω S - amplitude (a 1) (J 1) (u 1) Ω S
  let b := fun ξ z ↦ fullComplexMatrixAmplitude (a 0) (J 0) (u 0) Ω S ξ z i j -
    fullComplexMatrixAmplitude (a 1) (J 1) (u 1) Ω S ξ z i j
  have he (ξ : Euclidean n) : b ξ = fun z ↦ (((2 * Real.pi) ^ n *
      f (freezingOutputProjection z, freezingSourceProjection z, (2 * Real.pi) • ξ) i j : ℝ) : ℂ) := by
    funext z
    simp [b, f, fullComplexMatrixAmplitude, mul_sub]
  have hb' (ξ : Euclidean n) : ContDiff ℝ ∞ (b ξ) ∧
      ∀ z, ∀ k ≤ s, ‖iteratedFDeriv ℝ k (b ξ) z‖ ≤ C * A := by
    rw [he]
    exact hb f hf A hA hj ξ i j
  constructor
  · intro ξ is his z
    exact (norm_euclideanCoordinateDerivList_le_iteratedFDeriv (hb' ξ).1 is z).trans
      ((hb' ξ).2 z is.length his)
  · intro ξ is his z
    have hreflect : (fun z ↦ fullReflectedMatrixAmplitude (a 0) (J 0) (u 0) Ω S ξ z i j -
        fullReflectedMatrixAmplitude (a 1) (J 1) (u 1) Ω S ξ z i j) =
        (2 : ℂ) • (b ξ + b (-ξ)) := by
      funext z
      simp only [fullReflectedMatrixAmplitude_eq_complex_add_reflection,
        Matrix.smul_apply, Matrix.add_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, b]
      ring
    change ‖euclideanCoordinateDerivList is
      (fun z ↦ fullReflectedMatrixAmplitude (a 0) (J 0) (u 0) Ω S ξ z i j -
        fullReflectedMatrixAmplitude (a 1) (J 1) (u 1) Ω S ξ z i j) z‖ ≤ _
    rw [hreflect]
    have hsm := ((hb' ξ).1.add (hb' (-ξ)).1).const_smul (2 : ℂ)
    apply (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hsm is z).trans
    change ‖iteratedFDeriv ℝ is.length ((2 : ℂ) • (b ξ + b (-ξ))) z‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (f := b ξ + b (-ξ)) (a := (2 : ℂ))
      (((hb' ξ).1.add (hb' (-ξ)).1).contDiffAt.of_le (by simp)), norm_smul,
      iteratedFDeriv_add_apply (f := b ξ) (g := b (-ξ)) ((hb' ξ).1.contDiffAt.of_le (by simp))
        ((hb' (-ξ)).1.contDiffAt.of_le (by simp))]
    have hn : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hn]
    have ht := (norm_add_le _ _).trans
      (add_le_add ((hb' ξ).2 z is.length his) ((hb' (-ξ)).2 z is.length his))
    nlinarith

/-- Absolute full complex-amplitude regularity and entry bounds, in the
original paired physical coordinates. This conversion uses the same `2π`
normalization as the difference estimate. Its global matrix-jet input is
supplied by the supported primitive mixed-amplitude producer in
`OperatorDifference.ComplexPrimitiveBudget`. Consumer: the unreflected
normal identification (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem exists_fullComplexMatrixAmplitude_bounds_of_global_jets (s : ℕ) :
    ∃ C > 0, ∀ (a : Coefficients n N) (J : InputVariables n → ℝ)
      (u : Variables n × Euclidean 2 → SliceVariable n)
      (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2)),
      ContDiff ℝ ∞ (amplitude a J u Ω S) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ p, ∀ k ≤ s, ‖iteratedFDeriv ℝ k (amplitude a J u Ω S) p‖ ≤ A) →
      ContDiff ℝ ∞ (Function.uncurry (fullComplexMatrixAmplitude a J u Ω S)) ∧
      ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullComplexMatrixAmplitude a J u Ω S ξ z i j) s (C * A) := by
  obtain ⟨C, hC, hb⟩ := exists_physicalEntry_jet_bound (n := n) s
  refine ⟨C, hC, ?_⟩
  intro a J u Ω S ha A hA hj
  have harg : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean (2 * n) ↦
      (freezingOutputProjection p.2, freezingSourceProjection p.2, (2 * Real.pi) • p.1)) :=
    (freezingOutputProjection.contDiff.comp contDiff_snd).prodMk
      ((freezingSourceProjection.contDiff.comp contDiff_snd).prodMk
        (contDiff_fst.const_smul (2 * Real.pi)))
  have hsmooth (i j : Fin n) : ContDiff ℝ ∞
      (fun p : Euclidean n × Euclidean (2 * n) ↦
        fullComplexMatrixAmplitude a J u Ω S p.1 p.2 i j) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((realMatrixEntry i j).contDiff.comp (ha.comp harg)))
  refine ⟨?_, ?_⟩
  · have he : Function.uncurry (fullComplexMatrixAmplitude a J u Ω S) =
        fun p : Euclidean n × Euclidean (2 * n) ↦
          ∑ i : Fin n, ∑ j : Fin n,
            fullComplexMatrixAmplitude a J u Ω S p.1 p.2 i j •
              (Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℂ) := by
      classical
      funext p
      ext i j
      simp [Matrix.single, Matrix.sum_apply, ite_and, Function.uncurry_def]
    rw [he]
    exact ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦
      (hsmooth i j).smul contDiff_const
  · intro i j ξ is his z
    have hjets := hb (amplitude a J u Ω S) ha A hA hj ξ i j
    exact (norm_euclideanCoordinateDerivList_le_iteratedFDeriv hjets.1 is z).trans
      (hjets.2 z is.length his)

end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
