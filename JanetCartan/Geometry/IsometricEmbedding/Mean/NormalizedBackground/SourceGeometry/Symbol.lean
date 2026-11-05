module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.StressScaling
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.NormalizedSymbol

/-!
# The literal determinant symbol under source dilation

The Hamilton symbol in `app:ch_background:eq:bg-Nsigma` is evaluated using the
actual projected stress frame. Only the physical argument changes; the momentum
and its normalizing factor are untouched. Full rank is assumed at the unscaled
point, as in the published stress-frame scaling theorem.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalizedBackground.SourceGeometry

/-- `app:ch_background:eq:bg-Nsigma`: exact source scaling of the literal
normalized determinant Hamiltonian, not of an assumed abstract symbol. -/
theorem normalizedSymbol_sourceDilation {n N : ℕ}
    {F : Euclidean n → Euclidean N} {ρ : ℝ}
    (hρ : 0 < ρ) (hF : ContDiff ℝ ∞ F) (x ξ : Euclidean n)
    (hrank : Set.range (normalMap F (ρ • x)) =
      (normalSpace F (ρ • x) : Set (Euclidean N))) :
    ActualCarriers.normalizedSymbol (ProjectedStressFrame.projectedStress
      (sourceDilation F ρ)) (x, ξ) =
    ActualCarriers.normalizedSymbol (ProjectedStressFrame.projectedStress F) (ρ • x, ξ) := by
  have hQ : ProjectedStressFrame.projectedStress (sourceDilation F ρ) x =
      ProjectedStressFrame.projectedStress F (ρ • x) :=
    funext fun i ↦ ProjectedStressFrame.projectedStress_sourceDilation hρ hF x hrank i
  simp only [ActualCarriers.normalizedSymbol, hQ]

end JanetCartan.NormalizedBackground.SourceGeometry
