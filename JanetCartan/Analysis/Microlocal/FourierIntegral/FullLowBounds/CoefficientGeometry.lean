module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.CoefficientOperators

/-!
# Original full-amplitude supports supply coefficient geometry

The source integration cannot enlarge the original output/frequency carrier.
This supplies the amplitude fields of the primitive normal geometry used by
`FullLowBounds.Uniform`, without asking the geometry producer to establish
coefficient smoothness or coefficient support separately.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion LowBounds NormalComparison
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Construct coefficient normal geometry from the original full-amplitude
carrier and actual inverse-chart data on the whole averaged-gradient image.
The original amplitude's smoothness supplies the coefficient smoothness field.
Consumer: `exists_fullGraphL2_of_primitive_inputs`, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem primitiveNormalGeometry_matrixCoefficient
    (ℓ : ℝ) (A : FullAmplitude n r)
    (hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    (S : E → E → ℝ) (X D : Set E)
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (W K : Set (NormalVariables n))
    (hopen : IsOpen (bufferedNormalDomain X D S))
    (hη : ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D S))
    (hmap : MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D S) W)
    (hJ : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) W)
    (hgap : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0)
    (hright : ∀ q ∈ bufferedNormalDomain X D S,
      normalForwardCoordinates S (normalInverseCoordinates η q) = q)
    (hcarrier : ∀ q ∈ W, (∃ y, A q.1 y q.2.2 ≠ 0) →
      (∃ y, A q.2.1 y q.2.2 ≠ 0) → q ∈ K)
    (hclosed : IsClosed (normalForwardCoordinates S '' K))
    (hbuffer : normalForwardCoordinates S '' K ⊆ bufferedNormalDomain X D S)
    (hs : ∀ x y ξ, x ∉ X ∨ ξ ∉ D → A x y ξ = 0)
    (k : Fin n → ℤ) :
    PrimitiveNormalGeometry X D S (matrixCoefficient ℓ A k)
      (matrixCoefficient ℓ A k) η J W K := by
  have ha := contDiff_matrixCoefficient A hA ℓ k
  have hnonzero (x ξ : E) (h : matrixCoefficient ℓ A k x ξ ≠ 0) :
      ∃ y, A x y ξ ≠ 0 := by
    by_contra hh
    push Not at hh
    exact h (matrixCoefficient_eq_zero_of_fiber ℓ A k x ξ hh)
  have hout (x ξ : E) (hx : x ∉ X) : matrixCoefficient ℓ A k x ξ = 0 :=
    matrixCoefficient_eq_zero_of_fiber ℓ A k x ξ (fun y ↦ hs x y ξ (Or.inl hx))
  refine ⟨hopen, hη, hmap, ?_, hgap, hright, ?_, hclosed, hbuffer, hout, hout⟩
  · exact hJ.prodMk (((ha.comp (contDiff_fst.prodMk contDiff_snd.snd)).contDiffOn).prodMk
      ((ha.comp (contDiff_snd.fst.prodMk contDiff_snd.snd)).contDiffOn))
  · intro q hq hl hr
    exact hcarrier q hq (hnonzero _ _ hl) (hnonzero _ _ hr)

end JanetCartan.FourierIntegral.FullLowBounds
