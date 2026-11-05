module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.SourceTests

/-!
# Original datum words in the Euclidean fiber

The weak kernel identities use matrix coordinates, while the Fourier Sobolev
estimates use the Euclidean fiber. This bridge preserves the actual mixed
derivatives of the original datum in `new:eq:carrier-ibp`; its consumer is
the primitive annular Sobolev assembly of
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open Pseudodifferential FourierIntegral CompactTransfer WeakTransfer
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)

private theorem datumWord_ofLp (ds : List (E × P)) (a : E × P → V) :
    originalDatumDerivative ds (fun q => (a q).ofLp) =
      fun q => (originalDatumDerivative ds a q).ofLp := by
  induction ds with
  | nil => rfl
  | cons e ds ih =>
    change (fun q => fderiv ℝ (originalDatumDerivative ds (fun q => (a q).ofLp)) q e) = _
    rw [ih]
    funext q
    exact congrArg (fun L : (E × P) →L[ℝ] (Fin r → ℂ) => L e)
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).comp_fderiv)

/-- The SAME compact original datum word in the Euclidean fiber. No bounds
or differentiated-envelope data are stored here (`new:eq:carrier-ibp`). -/
def vectorOriginalDatumTest (a : E × P → V) (ha : ContDiff ℝ ∞ a)
    {K : Set E} (hK : IsCompact K) (hs : ∀ q, q.1 ∉ K → a q = 0)
    (ds : List (E × P)) (c : P) : graphTestSpace n r :=
  originalDatumTest (fun q => (a q).ofLp)
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).contDiff.comp ha)
    hK (fun q hq => congrArg WithLp.ofLp (hs q hq)) ds c

/-- Fiber conversion commutes with every recorded original mixed derivative.
This discharges the original-datum premise of the joint Sobolev deduction
following `new:eq:carrier-ibp`. -/
@[simp] theorem vectorOriginalDatumTest_val (a : E × P → V) (ha : ContDiff ℝ ∞ a)
    {K : Set E} (hK : IsCompact K) (hs : ∀ q, q.1 ∉ K → a q = 0)
    (ds : List (E × P)) (c : P) (x : E) :
    (vectorOriginalDatumTest a ha hK hs ds c).val x =
      originalDatumDerivative ds a (x, c) := by
  change WithLp.toLp 2 (originalDatumDerivative ds (fun q => (a q).ofLp) (x, c)) = _
  rw [datumWord_ofLp]

/-- The low-calculus input class is the actual original datum derivative,
not an auxiliary envelope. Consumer: `annular_joint_sobolev_of_expansion`
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem vectorOriginalDatumTest_toLp_ae (a : E × P → V) (ha : ContDiff ℝ ∞ a)
    {K : Set E} (hK : IsCompact K) (hs : ∀ q, q.1 ∉ K → a q = 0)
    (ds : List (E × P)) (c : P) :
    (graphTestToLp (vectorOriginalDatumTest a ha hK hs ds c) : E → V) =ᵐ[volume]
      fun x => originalDatumDerivative ds a (x, c) := by
  exact (graphTest_memLp _).coeFn_toLp.trans
    (Filter.Eventually.of_forall (vectorOriginalDatumTest_val a ha hK hs ds c))

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
