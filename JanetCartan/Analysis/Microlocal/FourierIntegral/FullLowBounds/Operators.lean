module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ReverseRegularized.Cutoff
public import JanetCartan.Analysis.Microlocal.FourierIntegral.L2Realization.Tests
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.ForwardRegularized.Admissibility

/-!
# One operator family for all complete modified amplitudes

The bounded test realization, when it exists, is unique by density. This fixes
one family for the low reserve in `SobolevBounds.IntegerBounds`. Its existence
and estimates on admissible symbols are proved by `FullLowBounds.Family` from
primitive geometry and original jets. No boundedness is asserted by the
choice definition alone. The reverse family uses literal Hilbert adjoints.
Source: `app:ch_regular_base:thm:actual-calculus`, Steps 1 and 3.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The unique bounded literal full graph when it exists, and zero otherwise.
`exists_fullGraphFamily_of_primitive_inputs` proves existence on every supported
symbol with the fixed low reserve, including budget zero. This same family
serves all modified amplitudes in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
def fullGraphOperator (S : E → E → ℝ) (A : FullAmplitude n r) : H →L[ℂ] H := by
  classical
  exact if h : ∃ T : H →L[ℂ] H, ∀ u : graphTestSpace n r,
      T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u then h.choose else 0

/-- Density identifies the chosen operator with any constructed literal test
realization. Consumer: `exists_fullGraphFamily_of_primitive_inputs`, for
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem fullGraphOperator_eq_of_realizes (S : E → E → ℝ) (A : FullAmplitude n r)
    (T : H →L[ℂ] H)
    (hT : ∀ u : graphTestSpace n r, T (graphTestToLp u) =ᵐ[volume]
      graphTestOutput S A u) : fullGraphOperator S A = T := by
  classical
  have h : ∃ T : H →L[ℂ] H, ∀ u : graphTestSpace n r,
      T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u := ⟨T, hT⟩
  rw [fullGraphOperator, dite_eq_left h]
  apply DFunLike.coe_injective
  apply denseRange_graphTestToLp.equalizer h.choose.continuous T.continuous
  funext u
  exact Lp.ext ((h.choose_spec u).trans (hT u).symm)

/-- The reverse full-amplitude family in the original `(x,y,η)` order.
For the conjugate transpose of the original amplitude this is exactly the
Hilbert adjoint of its forward graph, as required by
`app:ch_regular_base:eq:actual-adjoint-trade`. -/
def reverseFullGraphOperator (S : E → E → ℝ) (A : FullAmplitude n r) : H →L[ℂ] H :=
  (fullGraphOperator S (fun x y η ↦ (A x y η).conjTranspose)).adjoint

/-- Literal adjunction identifies the initial reverse operator without changing
physical variable order. Source: `app:ch_regular_base:eq:actual-adjoint-trade`. -/
theorem reverseFullGraphOperator_conjTranspose (S : E → E → ℝ) (A : FullAmplitude n r) :
    reverseFullGraphOperator S (fun x y η ↦ (A x y η).conjTranspose) =
      (fullGraphOperator S A).adjoint := by
  simp only [reverseFullGraphOperator, Matrix.conjTranspose_conjTranspose]

/-- Conjugate transpose preserves global smoothness and all fixed supports.
Consumer: the reverse low reserve in `SobolevBounds.IntegerBounds`, from
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem forwardAmplitudeAdmissible_conjTranspose {X Y F : Set E} {A : FullAmplitude n r}
    (hA : ForwardAmplitudeAdmissible X Y F A) :
    ForwardAmplitudeAdmissible X Y F (fun x y η ↦ (A x y η).conjTranspose) := by
  refine ⟨(starL ℝ : Mat ≃L[ℝ] Mat).contDiff.comp hA.smooth, ?_⟩
  intro x y η h
  simp only [hA.support x y η h, Matrix.conjTranspose_zero]

/-- A reverse-admissible amplitude on the fixed closed carrier avoiding zero
is globally smooth and has the same rectangular physical supports. Thus the
actual forward construction can be applied to its conjugate transpose.
Consumer: `exists_fullGraphFamily_of_primitive_inputs` for the reverse modified
amplitudes in `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem forwardAmplitudeAdmissible_of_reverse {X Y F : Set E} {A : FullAmplitude n r}
    (hA : ReverseAmplitudeAdmissible (X ×ˢ Y) A)
    (hF : IsClosed F) (hzero : (0 : E) ∉ F)
    (hsF : ∀ x y η, η ∉ F → A x y η = 0) :
    ForwardAmplitudeAdmissible X Y F A := by
  obtain ⟨m, hm, hmone, hmzero, _⟩ := exists_frequencyMask hF hzero
  have he : frequencyCutFullAmplitude m A = A := by
    funext x y η
    by_cases hη : η ∈ F
    · simp [frequencyCutFullAmplitude, hmone η hη]
    · simp [frequencyCutFullAmplitude, hsF x y η hη]
  have ha := hA.contDiff_frequencyCut m hm hmzero
  rw [he] at ha
  refine ⟨ha.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd), ?_⟩
  intro x y η hs
  rcases hs with hx | hy | hη
  · apply image_eq_zero_of_notMem_tsupport (x := ((x, y), η))
      (f := fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2)
    exact fun hp ↦ hx (hA.support hp).1
  · apply image_eq_zero_of_notMem_tsupport (x := ((x, y), η))
      (f := fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2)
    exact fun hp ↦ hy (hA.support hp).2
  · exact hsF x y η hη

end JanetCartan.FourierIntegral.FullLowBounds
