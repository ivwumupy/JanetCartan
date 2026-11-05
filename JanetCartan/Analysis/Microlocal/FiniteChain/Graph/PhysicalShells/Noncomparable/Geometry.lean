module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelEstimates.PhysicalPhase
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Identities
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Noncomparable.Majorants

/-!
# Support regimes for independent physical cutoff pairs

The consumer is the noncomparable part of `app:ch_regular:eq:chain-tail`.
The interval endpoints below are physical frequencies, including the complete
input shoulder. They may be supplied by `jc-graph-physical-cutoff-geometry`
for `highGraphCutoff`, `lowGraphCutoff`, and `outputCutoff`; no relation between
the two cutoff indices is required. The lower output endpoint may be zero.
-/

@[expose] public noncomputable section
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
open KernelEstimates KernelEstimates.NoncomparableGeometry

/-- Four sufficient support regimes for base integration by parts in
`app:ch_regular:eq:chain-tail`. Endpoints are physical, not normalized by the
input scale. In particular the low output ball has lower endpoint zero. -/
def SeparatedRanges (c C a b lξ uξ lζ uζ : ℝ) : Prop :=
  (2 * annulusFactor c C * uξ ≤ a ∨ 2 * annulusFactor c C * b ≤ lξ) ∨
  (2 * annulusFactor c C * uζ ≤ a ∨ 2 * annulusFactor c C * b ≤ lζ)

/-- An exact description of the complementary range regime. This lets the
parent prove exhaustive comparable/noncomparable coverage, including equality
at all four separating boundaries (`app:ch_regular:eq:chain-tail`). -/
theorem not_separatedRanges_iff (c C a b lξ uξ lζ uζ : ℝ) :
    ¬ SeparatedRanges c C a b lξ uξ lζ uζ ↔
      a < 2 * annulusFactor c C * uξ ∧ lξ < 2 * annulusFactor c C * b ∧
      a < 2 * annulusFactor c C * uζ ∧ lζ < 2 * annulusFactor c C * b := by
  simp only [SeparatedRanges, not_or, not_le]
  tauto

/-- Primitive interval support implies the existing physical covector
separation, with no restriction on the smaller frequencies
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem outsideInputAnnuli_of_separatedRanges
    {E : Type*} [NormedAddCommGroup E] {c C a b lξ uξ lζ uζ : ℝ}
    (ξ η ζ : E) (hξ : lξ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ uξ)
    (hη : a ≤ ‖η‖ ∧ ‖η‖ ≤ b) (hζ : lζ ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ uζ)
    (hsep : SeparatedRanges c C a b lξ uξ lζ uζ) :
    OutsideInputAnnuli c C ξ η ζ := by
  have hf : 0 ≤ 2 * annulusFactor c C := by
    have := two_le_annulusFactor c C
    positivity
  rcases hsep with (h | h) | (h | h)
  · exact Or.inl (Or.inl ((mul_le_mul_of_nonneg_left hξ.2 hf).trans (h.trans hη.1)))
  · exact Or.inl (Or.inr ((mul_le_mul_of_nonneg_left hη.2 hf).trans (h.trans hξ.1)))
  · exact Or.inr (Or.inl ((mul_le_mul_of_nonneg_left hζ.2 hf).trans (h.trans hη.1)))
  · exact Or.inr (Or.inr ((mul_le_mul_of_nonneg_left hη.2 hf).trans (h.trans hζ.1)))

/-- The lower endpoints bound the largest physical frequency, even for the
bounded output ball and arbitrarily small graph annuli
(`app:ch_regular:eq:chain-tail`). -/
theorem lowerEndpoints_le_largestFrequency
    {E : Type*} [NormedAddCommGroup E] {a lξ lζ : ℝ} (ξ η ζ : E)
    (hξ : lξ ≤ ‖ξ‖) (hη : a ≤ ‖η‖) (hζ : lζ ≤ ‖ζ‖) :
    max lξ (max a lζ) ≤ largestFrequency ξ η ζ := by
  exact max_le_max hξ (max_le_max hη hζ)

/-- Outside the four separated regimes, a graph annulus of width at most
four lies inside one fixed enlargement of the input annulus. Both expanding
and contracting graph cutoffs have this width. The input endpoints include
the shoulders (`app:ch_regular:eq:chain-tail`). -/
theorem graph_bounds_of_not_separatedRanges
    {E : Type*} [NormedAddCommGroup E] {c C a b lξ uξ lζ uζ : ℝ}
    (ξ : E) (hξ : lξ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ uξ) (hwidth : uξ ≤ 4 * lξ)
    (hsep : ¬ SeparatedRanges c C a b lξ uξ lζ uζ) :
    a < 8 * annulusFactor c C * ‖ξ‖ ∧ ‖ξ‖ < 8 * annulusFactor c C * b := by
  obtain ⟨h₁, h₂, _, _⟩ := (not_separatedRanges_iff ..).mp hsep
  have hf : 0 ≤ 2 * annulusFactor c C := by
    have := two_le_annulusFactor c C
    positivity
  constructor
  · have hh := mul_le_mul_of_nonneg_left (hwidth.trans
      (mul_le_mul_of_nonneg_left hξ.1 (by norm_num))) hf
    nlinarith
  · have hh := mul_lt_mul_of_pos_left h₂ (by norm_num : (0 : ℝ) < 4)
    linarith

/-- The output annuli satisfy the same exhaustive coverage statement. The
index-zero output ball is handled by its upper support bound instead of an
incorrect positive lower endpoint (`app:ch_regular:eq:chain-tail`). -/
theorem output_bounds_of_not_separatedRanges
    {E : Type*} [NormedAddCommGroup E] {c C a b lξ uξ lζ uζ : ℝ}
    (ζ : E) (hζ : lζ ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ uζ) (hwidth : uζ ≤ 4 * lζ)
    (hsep : ¬ SeparatedRanges c C a b lξ uξ lζ uζ) :
    a < 8 * annulusFactor c C * ‖ζ‖ ∧ ‖ζ‖ < 8 * annulusFactor c C * b := by
  apply graph_bounds_of_not_separatedRanges (lζ := lξ) (uζ := uξ) ζ hζ hwidth
  unfold SeparatedRanges at *
  tauto

variable {n : ℕ}

/-- The primitive lower input annulus and actual dyadic lower endpoints give
a fixed fraction of the concrete largest radius. The output index zero needs
no positive lower support bound: its unit bookkeeping radius is controlled
by `ρ ≥ 1`. This discharges `hlarge` in the actual pair estimate from support
data, even for contracting graph annuli (`app:ch_regular:eq:chain-tail`). -/
theorem fractional_pairRadius_le_lowerEndpoints {ρ inputLower lξ lζ ε : ℝ}
    (hρ : 1 ≤ ρ) (hε : 0 ≤ ε) (hεi : ε ≤ inputLower) (hεh : ε ≤ 1 / 2)
    (low : Bool) (j k : ℕ) (hξ : branchRadius low j / 2 ≤ lξ)
    (hζ : k = 0 ∨ ((2 : ℝ) ^ k) / 2 ≤ lζ) :
    ε * pairRadius ρ low j k ≤ max lξ (max (inputLower * ρ) lζ) := by
  have hi : ε * ρ ≤ inputLower * ρ :=
    mul_le_mul_of_nonneg_right hεi (zero_le_one.trans hρ)
  have hg : ε * branchRadius low j ≤ lξ := by
    have hh := mul_le_mul_of_nonneg_right hεh (branchRadius_pos low j).le
    linarith
  have ho : ε * (2 : ℝ) ^ k ≤ max lξ (max (inputLower * ρ) lζ) := by
    rcases hζ with hk | hk
    · subst k
      simp only [pow_zero, mul_one]
      exact ((by nlinarith : ε ≤ ε * ρ).trans hi).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · have hh := mul_le_mul_of_nonneg_right hεh (by positivity : (0 : ℝ) ≤ 2 ^ k)
      exact (show ε * (2 : ℝ) ^ k ≤ lζ by linarith).trans
        ((le_max_right _ _).trans (le_max_right _ _))
  rw [pairRadius, mul_max_of_nonneg _ _ hε, mul_max_of_nonneg _ _ hε]
  exact max_le (hi.trans ((le_max_left _ _).trans (le_max_right _ _)))
    (max_le (hg.trans (le_max_left _ _)) ho)

/-- The literal input-normalized phase has a uniform squared gap from
physical support intervals and primitive phase-gradient comparison. This is
the gap input of the single-pair bound, for both orientations of the weighted
full graph amplitude (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem normalizedBasePhase_gap_of_separatedRanges
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    (backward : Bool) (ρ : ℝ) {R c C a b lξ uξ lζ uζ : ℝ}
    (hR : 0 < R) (hc : 0 < c)
    (Φ φ : Euclidean n → Euclidean n → ℝ) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) (z : Euclidean n × Euclidean n)
    (g : Euclidean n) (hhom : ∀ u, Φ u (ρ • w.1) = ρ * φ u w.1)
    (hφ : DifferentiableAt ℝ (fun u => Φ u (ρ • w.1)) z.1)
    (hg : fderiv ℝ (fun u => Φ u (ρ • w.1)) z.1 = innerSL ℝ g)
    (hlow : c * ‖ρ • w.1‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ρ • w.1‖)
    (hξ : lξ ≤ ‖ρ • w.1‖ ∧ ‖ρ • w.1‖ ≤ uξ)
    (hη : a ≤ ‖ρ • w.2.1‖ ∧ ‖ρ • w.2.1‖ ≤ b)
    (hζ : lζ ≤ ‖ρ • w.2.2‖ ∧ ‖ρ • w.2.2‖ ≤ uζ)
    (hsep : SeparatedRanges c C a b lξ uξ lζ uζ)
    (hlarge : R ≤ max lξ (max a lζ)) :
    gapCoefficient c C ≤ Localization.phaseGradientSquare (baseDirections eu ez)
      (KernelEstimates.Noncomparable.normalizedBasePhase backward ρ R φ x y w) z :=
  normalizedBasePhase_gap_of_comparison eu ez backward ρ hR hc Φ φ x y w z g
    hhom hφ hg hlow hhigh
    (outsideInputAnnuli_of_separatedRanges _ _ _ hξ hη hζ hsep)
    (hlarge.trans (lowerEndpoints_le_largestFrequency _ _ _ hξ.1 hη.1 hζ.1))

/-- A fixed fraction of the largest radius suffices for the normalized gap.
Thus the integration radius may be at least one even when every frequency is
bounded and an input shoulder starts below one. The fixed factor belongs to
the gap constant, not to a scale-dependent loss
(`app:ch_regular:eq:chain-tail`). -/
theorem normalizedBasePhase_fractional_gap_of_separatedRanges
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eu : OrthonormalBasis ι ℝ (Euclidean n)) (ez : OrthonormalBasis κ ℝ (Euclidean n))
    (backward : Bool) (ρ : ℝ) {R c C a b lξ uξ lζ uζ ε : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hε : 0 ≤ ε)
    (Φ φ : Euclidean n → Euclidean n → ℝ) (x y : Euclidean n)
    (w : Euclidean n × Euclidean n × Euclidean n) (z : Euclidean n × Euclidean n)
    (g : Euclidean n) (hhom : ∀ u, Φ u (ρ • w.1) = ρ * φ u w.1)
    (hφ : DifferentiableAt ℝ (fun u => Φ u (ρ • w.1)) z.1)
    (hg : fderiv ℝ (fun u => Φ u (ρ • w.1)) z.1 = innerSL ℝ g)
    (hlow : c * ‖ρ • w.1‖ ≤ ‖g‖) (hhigh : ‖g‖ ≤ C * ‖ρ • w.1‖)
    (hξ : lξ ≤ ‖ρ • w.1‖ ∧ ‖ρ • w.1‖ ≤ uξ)
    (hη : a ≤ ‖ρ • w.2.1‖ ∧ ‖ρ • w.2.1‖ ≤ b)
    (hζ : lζ ≤ ‖ρ • w.2.2‖ ∧ ‖ρ • w.2.2‖ ≤ uζ)
    (hsep : SeparatedRanges c C a b lξ uξ lζ uζ)
    (hlarge : ε * R ≤ max lξ (max a lζ)) :
    gapCoefficient c C * ε ^ 2 ≤ Localization.phaseGradientSquare (baseDirections eu ez)
      (KernelEstimates.Noncomparable.normalizedBasePhase backward ρ R φ x y w) z := by
  rw [normalizedBasePhase_eq_physical backward ρ R Φ φ x y w hhom,
    Retarded.HalfSpace.phaseGradientSquare_frequency _ _
      (differentiableAt_basePhase backward Φ x y _ _ _ z hφ)]
  have h := mul_le_mul_of_nonneg_left
    (basePhase_scaled_gradient_gap eu ez backward Φ x y _ _ _ g z hφ hg hc
      (mul_nonneg hε hR.le) hlow hhigh
      (outsideInputAnnuli_of_separatedRanges _ _ _ hξ hη hζ hsep)
      (hlarge.trans (lowerEndpoints_le_largestFrequency _ _ _ hξ.1 hη.1 hζ.1)))
    (sq_nonneg R⁻¹)
  have he : R⁻¹ ^ 2 * (gapCoefficient c C * (ε * R) ^ 2) =
      gapCoefficient c C * ε ^ 2 := by field_simp
  rwa [he] at h

end JanetCartan.FiniteChain.Graph.PhysicalShells.Noncomparable
