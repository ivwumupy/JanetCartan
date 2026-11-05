module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.MatrixKernels
public import JanetCartan.Analysis.Microlocal.NormalComparison.Comparison

/-!
# Bounds for the complete matrix transport channels

The matrix normal estimate used in Step 2 of `app:ch_osc:prop:osc-normal`.
The bounds apply to the literal two-position kernels, with Frobenius bounds on
the coefficient derivatives. The final comparison theorem is conditional on
the operator derivative identity and the geometric coefficient bounds; it
discharges the channel norm estimates using `app:ch_osc:lem:osc-amplitude`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison

open AmplitudeBound

/-- The finite Hilbert direct sum of full-space scalar L² outputs used in
`app:ch_osc:prop:osc-normal`. Its norm is the fiberwise Euclidean norm. -/
abbrev NormalOutputL2 (d r : ℕ) :=
  PiLp 2 (fun _ : Fin r ↦ Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))

variable {d m r : ℕ}

/-- The coefficient hypotheses of `app:ch_osc:eq:two-position-normal-bound`
for a fixed square matrix. These are solely smoothness, support and physical
derivative assumptions; no operator bound or kernel identity is included. -/
structure MatrixNormalAmplitudeBounds
    (c : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (2 * d)) →
      Matrix (Fin r) (Fin r) ℂ) (R A : ℝ) : Prop where
  measurable : StronglyMeasurable (Function.uncurry c)
  smooth : ∀ u, ContDiff ℝ ∞ (c u)
  support : ∀ u i j, SupportedInCenteredBox R (fun z ↦ c u z i j)
  derivative : ∀ u is, is.length ≤ 2 * (d + 1) → ∀ z,
    ‖matrixAmplitudeCoordinateDerivList is (c u) z‖ ≤ A

/-- Fixed-matrix version of the full normal-kernel assertion
`app:ch_osc:eq:two-position-normal-bound`. The actual scalar input operator is
specified by its input integral, and its adjoint is derived by the scalar theorem.
Both physical positions remain independent throughout. -/
theorem exists_matrixTwoPositionNormalOperator (hd : 0 < d) (R : ℝ)
    {D : Set (EuclideanSpace ℝ (Fin m))} (hD : MeasurableSet D)
    (t : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℂ)
    (ht : ContDiff ℝ ∞ (Function.uncurry t))
    (hts : HasCompactSupport (Function.uncurry t))
    (T : Lp ℂ 2 (volume.restrict D) →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (hT : ∀ h, T h =ᵐ[volume] fun x ↦ ∫ u, t x u * h u ∂volume.restrict D)
    (c : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (2 * d)) →
      Matrix (Fin r) (Fin r) ℂ) (A : ℝ)
    (hc : MatrixNormalAmplitudeBounds c R A) (g : Lp ℂ ∞ (volume.restrict D)) :
    ∃ N : NormalOutputL2 d r →L[ℂ]
        NormalOutputL2 d r,
      ‖N‖ ≤ (r : ℝ) * r * (fixedBoxAmplitudeConstant d R * A * ‖T‖ ^ 2 * ‖g‖) ∧
      ∀ f i, (N f) i =ᵐ[volume] fun x ↦ ∑ j,
        fullNormalAmplitudeKernel (μ := volume.restrict D) t
          (fun u z ↦ c u z i j) g (f j) x := by
  have hm (i j : Fin r) : StronglyMeasurable
      (Function.uncurry (fun u z ↦ c u z i j)) :=
    (matrixEntryEvaluation i j).continuous.comp_stronglyMeasurable hc.measurable
  have hf (i j : Fin r) (u) : ContDiff ℝ ∞ (fun z ↦ c u z i j) :=
    (matrixEntryEvaluation i j).contDiff.comp (hc.smooth u)
  have hb (i j : Fin r) : HasAmplitudeDerivativeBound
      (fun u z ↦ c u z i j) (2 * (d + 1)) A := by
    intro u is hi z
    exact (norm_matrixEntry_le_frobenius _ i j).trans (hc.derivative u is hi z)
  choose B hB hker using fun i j ↦ exists_twoPositionNormalOperator hd R hD t ht hts
    T hT (fun u z ↦ c u z i j) (hm i j) (hf i j)
    (fun u ↦ hc.support u i j) A (hb i j) g
  refine ⟨matrixOperator B, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using norm_matrixOperator_le_of_entry_bound B _ hB
  · exact fun f i ↦ matrixOperator_ae_kernel B _ hker f i

/-- The matrix normal bound applies to any bounded operator with the literal
kernel, by almost-everywhere uniqueness in L² (`app:ch_osc:prop:osc-normal`).
Thus later differentiation arguments need not use a particular Fourier-series
construction of the channel operator. -/
theorem norm_matrixNormalChannel_le (hd : 0 < d) (R : ℝ)
    {D : Set (EuclideanSpace ℝ (Fin m))} (hD : MeasurableSet D)
    (t : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℂ)
    (ht : ContDiff ℝ ∞ (Function.uncurry t))
    (hts : HasCompactSupport (Function.uncurry t))
    (T : Lp ℂ 2 (volume.restrict D) →L[ℂ] Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (hT : ∀ h, T h =ᵐ[volume] fun x ↦ ∫ u, t x u * h u ∂volume.restrict D)
    (c : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (2 * d)) →
      Matrix (Fin r) (Fin r) ℂ) (A : ℝ)
    (hc : MatrixNormalAmplitudeBounds c R A) (g : Lp ℂ ∞ (volume.restrict D))
    (N : NormalOutputL2 d r →L[ℂ]
        NormalOutputL2 d r)
    (hN : ∀ f i, (N f) i =ᵐ[volume] fun x ↦ ∑ j,
      fullNormalAmplitudeKernel (μ := volume.restrict D) t
        (fun u z ↦ c u z i j) g (f j) x) :
    ‖N‖ ≤ (r : ℝ) * r * (fixedBoxAmplitudeConstant d R * A * ‖T‖ ^ 2 * ‖g‖) := by
  obtain ⟨B, hB, hker⟩ := exists_matrixTwoPositionNormalOperator hd R hD t ht hts
    T hT c A hc g
  have heq : N = B := by
    ext f i
    exact (hN f i).trans (hker f i).symm
  rw [heq]
  exact hB

/-- The last analytic step of `app:ch_osc:prop:osc-normal`, now using the proved
two-position amplitude theorem to discharge all transport-channel norm bounds.
`none` indexes `c₀,m`; `some j` indexes `cⱼ,∂ⱼm`. The derivative identity, the
uniform scalar-channel bound and the coefficient derivative bounds are explicit
remaining geometric/analytic inputs. Only the displayed L∞ norms of the masks
enter, so this estimate requires no second or higher mask derivative. -/
theorem norm_sub_le_of_normal_amplitudes (hd : 0 < d) (R : ℝ)
    {D : Set (EuclideanSpace ℝ (Fin m))} (hD : MeasurableSet D)
    (t : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m) → ℂ)
    (T : ℝ → Lp ℂ 2 (volume.restrict D) →L[ℂ]
      Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)
    (c : ℝ → Option (Fin m) → EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin (2 * d)) → Matrix (Fin r) (Fin r) ℂ)
    (g : Option (Fin m) → Lp ℂ ∞ (volume.restrict D))
    (E : ℝ → NormalOutputL2 d r →L[ℂ]
      NormalOutputL2 d r)
    (N : ℝ → Option (Fin m) →
      NormalOutputL2 d r →L[ℂ]
      NormalOutputL2 d r)
    {ε h A S L : ℝ} (hε : 0 ≤ ε) (hh : 0 < h) (hh₁ : h ≤ 1) (hA : 0 ≤ A)
    (ht : ∀ s ∈ Icc 0 ε, ContDiff ℝ ∞ (Function.uncurry (t s)))
    (hts : ∀ s ∈ Icc 0 ε, HasCompactSupport (Function.uncurry (t s)))
    (hT : ∀ s ∈ Icc 0 ε, ∀ f,
      T s f =ᵐ[volume] fun x ↦ ∫ u, t s x u * f u ∂volume.restrict D)
    (hTb : ∀ s ∈ Icc 0 ε, ‖T s‖ ≤ S)
    (hc : ∀ s ∈ Icc 0 ε, ∀ k, MatrixNormalAmplitudeBounds (c s k) R A)
    (hg₀ : ‖g none‖ ≤ 1) (hg : ∀ j, ‖g (some j)‖ ≤ L / h)
    (hN : ∀ s ∈ Icc 0 ε, ∀ k f i, (N s k f) i =ᵐ[volume] fun x ↦ ∑ j,
      fullNormalAmplitudeKernel (μ := volume.restrict D) (t s)
        (fun u z ↦ c s k u z i j) (g k) (f j) x)
    (hE : ∀ s ∈ Icc 0 ε, HasDerivAt E (N s none + ∑ j, N s (some j)) s) :
    ‖E ε - E 0‖ ≤
      ((r : ℝ) * r * (fixedBoxAmplitudeConstant d R * A * S ^ 2)) *
        (1 + (m : ℝ) * L) * ε / h := by
  let B := (r : ℝ) * r * (fixedBoxAmplitudeConstant d R * A * S ^ 2)
  have hC : 0 ≤ fixedBoxAmplitudeConstant d R := fixedBoxAmplitudeConstant_nonneg d R
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : ∀ s ∈ Icc 0 ε, ∀ k, ‖N s k‖ ≤ B * ‖g k‖ := by
    intro s hs k
    have hsq : ‖T s‖ ^ 2 ≤ S ^ 2 := by
      nlinarith [hTb s hs, norm_nonneg (T s)]
    calc
      ‖N s k‖ ≤ (r : ℝ) * r *
          (fixedBoxAmplitudeConstant d R * A * ‖T s‖ ^ 2 * ‖g k‖) :=
        norm_matrixNormalChannel_le hd R hD (t s) (ht s hs) (hts s hs)
          (T s) (hT s hs) (c s k) A (hc s hs k) (g k) (N s k) (hN s hs k)
      _ ≤ (r : ℝ) * r * (fixedBoxAmplitudeConstant d R * A * S ^ 2 * ‖g k‖) := by
        gcongr
      _ = B * ‖g k‖ := by dsimp [B]; ring
  apply norm_sub_le_of_transport_channels E (fun s ↦ N s none)
    (fun s j ↦ N s (some j)) hε hh hh₁ hB hE
  · intro s hs
    exact (hbound s hs none).trans ((mul_le_mul_of_nonneg_left hg₀ hB).trans_eq
      (mul_one B))
  · intro s hs j
    exact (hbound s hs (some j)).trans ((mul_le_mul_of_nonneg_left (hg j) hB).trans_eq
      (mul_div_assoc B L h).symm)

end JanetCartan.NormalComparison
