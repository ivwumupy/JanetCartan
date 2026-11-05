module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.Compact

/-!
# The original datum derivatives as compact smooth graph tests

Every source/parameter word in `new:eq:carrier-ibp` differentiates the original
joint datum. A common compact spatial support is preserved by these words,
including parameter directions. This supplies the actual test inputs to the
annular branch realizations without postulating their regularity.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
open Pseudodifferential FourierIntegral CompactTransfer
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "V" => Fin r → ℂ

/-- Mixed derivatives preserve the SAME original spatial support, although
no compactness in the parameter is assumed (`new:eq:carrier-ibp`). -/
theorem tsupport_originalDatumDerivative_source
    {a : E × P → V} {K : Set E} (hK : IsClosed K)
    (hs : ∀ q, q.1 ∉ K → a q = 0) (ds : List (E × P)) :
    tsupport (originalDatumDerivative ds a) ⊆ {q | q.1 ∈ K} := by
  induction ds with
  | nil =>
    apply closure_minimal _ (hK.preimage continuous_fst)
    intro q hq
    by_contra hn
    exact hq (hs q hn)
  | cons e ds ih =>
    exact (tsupport_fderiv_apply_subset ℝ e).trans ih

/-- The Euclidean-fiber source slice of each actual datum word retains the
original compact support. Consumer: `originalDatumTest` (`new:eq:carrier-ibp`). -/
theorem tsupport_originalDatumDerivative_slice
    {a : E × P → V} {K : Set E} (hK : IsClosed K)
    (hs : ∀ q, q.1 ∉ K → a q = 0) (ds : List (E × P)) (c : P) :
    tsupport (fun z => (WithLp.toLp 2
      (originalDatumDerivative ds a (z, c)) : EuclideanSpace ℂ (Fin r))) ⊆ K := by
  apply closure_minimal _ hK
  intro z hz
  by_contra hn
  have hnot : (z, c) ∉ tsupport (originalDatumDerivative ds a) :=
    fun h => hn (tsupport_originalDatumDerivative_source hK hs ds h)
  exact hz (by change WithLp.toLp 2 (originalDatumDerivative ds a (z, c)) = 0
               rw [image_eq_zero_of_notMem_tsupport hnot, WithLp.toLp_zero])

/-- The actual source/parameter derivative in the original graph test space.
Smoothness and compact support are conclusions from the original datum,
not additional hypotheses on its differentiated versions (`new:eq:carrier-ibp`). -/
def originalDatumTest (a : E × P → V) (ha : ContDiff ℝ ∞ a)
    {K : Set E} (hK : IsCompact K) (hs : ∀ q, q.1 ∉ K → a q = 0)
    (ds : List (E × P)) (c : P) : graphTestSpace n r :=
  ⟨fun z => WithLp.toLp 2 (originalDatumDerivative ds a (z, c)),
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).symm.contDiff.comp
      ((contDiff_originalDatumDerivative ha ds).comp (contDiff_id.prodMk contDiff_const)),
    hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_originalDatumDerivative_slice hK.isClosed hs ds c)⟩

/-- Coordinates of the original datum test are precisely its ordered source
and parameter derivatives (`new:eq:carrier-ibp`). -/
@[simp] theorem originalDatumTest_apply (a : E × P → V) (ha : ContDiff ℝ ∞ a)
    {K : Set E} (hK : IsCompact K) (hs : ∀ q, q.1 ∉ K → a q = 0)
    (ds : List (E × P)) (c : P) (z : E) :
    ((originalDatumTest a ha hK hs ds c).val z).ofLp =
      originalDatumDerivative ds a (z, c) := rfl

/-- No new source cutoff is inserted when feeding an actual derivative to a
branch. The original support is retained (`new:eq:carrier-ibp`). -/
theorem originalDatumTest_support (a : E × P → V) (ha : ContDiff ℝ ∞ a)
    {K : Set E} (hK : IsCompact K) (hs : ∀ q, q.1 ∉ K → a q = 0)
    (ds : List (E × P)) (c : P) :
    tsupport (originalDatumTest a ha hK hs ds c).val ⊆ K :=
  tsupport_originalDatumDerivative_slice hK.isClosed hs ds c

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev.WeakTransfer
