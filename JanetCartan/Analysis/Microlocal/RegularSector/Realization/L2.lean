module

public import JanetCartan.Analysis.Operator.RealQuadratures
public import JanetCartan.Analysis.Microlocal.RegularSector.Conjugation

/-!
# The real structure on Euclidean-valued L²

Concrete conjugation and the existing real-part/inclusion maps for
`app:ch_regular_base:eq:real-sector-normalization`. The scoped instances use
coordinate conjugation and almost-everywhere equality, never evaluation of an
arbitrary L² class at a prescribed point. Measures are retained literally.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.RegularSector.Realization

variable {ι : Type*} [Fintype ι]

/-- Coordinate conjugation for `app:ch_regular_base:eq:signed-physical-normalization`. -/
scoped instance euclideanStarAddMonoid : StarAddMonoid (EuclideanSpace ℂ ι) where
  star z := WithLp.toLp 2 (fun i ↦ star (z i))
  star_involutive z := by ext i; exact star_star (z i)
  star_add z w := by ext i; exact star_add (z i) (w i)

/-- Coordinate conjugation is semilinear (`app:ch_regular_base:eq:signed-graph-factor`). -/
scoped instance euclideanStarModule : StarModule ℂ (EuclideanSpace ℂ ι) where
  star_smul c z := by ext i; exact map_mul (starRingEnd ℂ) c (z i)

/-- Coordinate conjugation preserves the Euclidean norm
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
scoped instance euclideanNormedStarGroup : NormedStarGroup (EuclideanSpace ℂ ι) where
  norm_star_le z := by
    have h : ‖star z‖ = ‖z‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp only [EuclideanSpace.norm_sq_eq]
      congr 1
      funext i
      exact congrArg (fun t : ℝ ↦ t ^ 2) (norm_star (z i))
    exact h.le

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The standard a.e. conjugation is additive on L²
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
scoped instance l2StarAddMonoid : StarAddMonoid (Lp (EuclideanSpace ℂ ι) 2 μ) where
  star := star
  star_involutive := star_star
  star_add f g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g,
      Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g]
      with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.star_apply] at h₁ h₄ h₅
    simp only [h₁, h₂, h₃, Pi.add_apply, h₄, h₅, star_add]

/-- L² conjugation is complex semilinear
(`app:ch_regular_base:eq:signed-graph-factor`). -/
scoped instance l2StarModule : StarModule ℂ (Lp (EuclideanSpace ℂ ι) 2 μ) where
  star_smul c f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
      Lp.coeFn_smul (star c) (star f), Lp.coeFn_star f] with x h₁ h₂ h₃ h₄
    simp only [Pi.star_apply] at h₁ h₄
    simp only [h₁, h₂, h₃, Pi.smul_apply, h₄, star_smul]

/-- L² conjugation is isometric (`app:ch_regular_base:eq:signed-physical-normalization`). -/
scoped instance l2NormedStarGroup : NormedStarGroup (Lp (EuclideanSpace ℂ ι) 2 μ) where
  norm_star_le f := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_star f] with x hx
    rw [hx, Pi.star_apply, norm_star]

/-- Real part is a left inverse of the existing inclusion
(`app:ch_regular_base:eq:real-sector-normalization`). -/
@[simp] theorem realPart_inclusion (f : Lp (EuclideanSpace ℝ ι) 2 μ) :
    l2RealPart μ (l2ComplexInclusion μ f) = f := by
  apply Lp.ext
  filter_upwards [euclideanRealPart.coeFn_compLpL (l2ComplexInclusion μ f),
    euclideanComplexInclusion.coeFn_compLpL f] with x hr hj
  simp only [l2RealPart, l2ComplexInclusion] at *
  rw [hr, hj]
  ext i
  simp

/-- Included real data are conjugation fixed
(`app:ch_regular_base:eq:real-sector-normalization`). -/
@[simp] theorem star_inclusion (f : Lp (EuclideanSpace ℝ ι) 2 μ) :
    star (l2ComplexInclusion μ f) = l2ComplexInclusion μ f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (l2ComplexInclusion μ f),
    euclideanComplexInclusion.coeFn_compLpL f] with x hs hj
  simp only [l2ComplexInclusion] at *
  rw [hs, Pi.star_apply, hj]
  ext i
  exact Complex.conj_ofReal _

/-- Conjugation-fixed L² data are recovered from their real part
(`app:ch_regular_base:eq:real-sector-normalization`). -/
theorem inclusion_realPart_of_star_eq (z : Lp (EuclideanSpace ℂ ι) 2 μ)
    (hz : star z = z) : l2ComplexInclusion μ (l2RealPart μ z) = z := by
  have hs := Lp.coeFn_star z
  rw [hz] at hs
  apply Lp.ext
  filter_upwards [hs, euclideanComplexInclusion.coeFn_compLpL (l2RealPart μ z),
    euclideanRealPart.coeFn_compLpL z] with x hx hj hr
  simp only [l2RealPart, l2ComplexInclusion] at *
  rw [hj, hr]
  ext i
  have hi := congrArg (fun v : EuclideanSpace ℂ ι ↦ (v i).im) hx
  change (z x i).im = -(z x i).im at hi
  apply Complex.ext
  · rfl
  · change 0 = (z x i).im
    linarith

/-- Both real quadratures span the literal complex L² space
(`app:ch_response:eq:response-actual-solver-formula`). -/
theorem quadrature_decomposition (z : Lp (EuclideanSpace ℂ ι) 2 μ) :
    l2ComplexInclusion μ (l2RealPart μ z) +
      Complex.I • l2ComplexInclusion μ (l2RealPart μ (-Complex.I • z)) = z := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (l2ComplexInclusion μ (l2RealPart μ z))
      (Complex.I • l2ComplexInclusion μ (l2RealPart μ (-Complex.I • z))),
    Lp.coeFn_smul Complex.I (l2ComplexInclusion μ (l2RealPart μ (-Complex.I • z))),
    euclideanComplexInclusion.coeFn_compLpL (l2RealPart μ z),
    euclideanComplexInclusion.coeFn_compLpL (l2RealPart μ (-Complex.I • z)),
    euclideanRealPart.coeFn_compLpL z,
    euclideanRealPart.coeFn_compLpL (-Complex.I • z),
    Lp.coeFn_smul (-Complex.I) z] with x ha hi hj hk hr hs hn
  simp only [l2RealPart, l2ComplexInclusion, Pi.add_apply, Pi.smul_apply] at *
  rw [ha, hi, hj, hk, hr, hs, hn]
  ext i
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

end JanetCartan.RegularSector.Realization
