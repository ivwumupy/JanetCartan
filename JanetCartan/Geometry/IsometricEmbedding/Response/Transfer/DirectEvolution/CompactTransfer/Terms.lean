module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Expressions
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.SourceDatum

/-!
# Ordered compact carrier transfer terms

A refinement of the shared `orderedTransferTerms` enumeration for
`paper-v2.tex`, `new:eq:carrier-ibp`: an input derivative is either a parameter
derivative or one of the source components of the integration vector field.
The datum words act on the original `a_c(z)` and never on a new envelope.
The derivative budget is proved from the expressions, not stored as an input.
-/

@[expose] public noncomputable section
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
open Pseudodifferential IsometricEmbedding.Response.NearCarrier

variable {n : ℕ} {P M V ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- A literal amplitude and an ordered word of derivatives of the original
source/parameter datum. `allocation` records the corresponding branch of the
published binary enumeration (`new:eq:carrier-ibp`). It stores no analytic premise. -/
structure JointTransferTerm (n : ℕ) (P M ι : Type)
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup M] [NormedSpace ℝ M] where
  amplitude : AmplitudeExpression ((Euclidean n × P) × CarrierVariables n)
    (M × ℝ) (Option ((Euclidean n × P) × ι))
  datumWord : List (Euclidean n × P)
  allocation : List (Euclidean n × P) × List (Euclidean n × P)

/-- The undifferentiated full masked amplitude and original input, before
`new:eq:carrier-ibp`. -/
def initialJointTransferTerm : JointTransferTerm n P M ι :=
  ⟨.primitive none, [], ([], [])⟩

/-- The actual alternatives for one output/parameter derivative. The
normalized covector component never differentiates the datum: source words
use only `(b i).fst`. Source: the four terms of `new:eq:carrier-ibp`. -/
def jointTransferChildren (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (e : Euclidean n × P) (t : JointTransferTerm n P M ι) :
    List (JointTransferTerm n P M ι) :=
  ⟨t.amplitude.divergenceTransfer (e, 0) (jointDivergenceTerms b e),
    t.datumWord, (e :: t.allocation.1, t.allocation.2)⟩ ::
  ⟨t.amplitude, (0, e.2) :: t.datumWord,
    (t.allocation.1, e :: t.allocation.2)⟩ ::
  (Finset.univ.toList : List ι).map fun i =>
    ⟨t.amplitude.coefficientProduct scalarAmplitudeProduct (some (e, i)),
      ((b i).fst, 0) :: t.datumWord, (t.allocation.1, e :: t.allocation.2)⟩

/-- Finite ordered transfer with multiplicities, using the published ordered
action convention. All coefficient insertions retain their original order.
Source: the iteration following `new:eq:carrier-ibp`. -/
def jointTransferTerms (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (es : List (Euclidean n × P)) : List (JointTransferTerm n P M ι) :=
  orderedTransferAction (fun e ts => ts.flatMap (jointTransferChildren b e)) es
    [initialJointTransferTerm]

/-- Every actual branch refines the shared ordered enumeration, and its
amplitude cost and original-datum order agree with that enumeration.
Source: the count `k+j=q` following `new:eq:carrier-ibp`. -/
theorem jointTransferTerms_spec
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) :
    t.allocation ∈ orderedTransferTerms es ∧
      t.amplitude.derivativeCost = t.allocation.1.length ∧
      t.datumWord.length = t.allocation.2.length := by
  induction es generalizing t with
  | nil =>
    simp only [jointTransferTerms, orderedTransferAction, List.mem_singleton] at ht
    subst t
    simp [initialJointTransferTerm, orderedTransferTerms, AmplitudeExpression.derivativeCost]
  | cons e es ih =>
    change t ∈ (jointTransferTerms b es).flatMap (jointTransferChildren b e) at ht
    obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨ha, hc, hd⟩ := ih u hu
    have hleft : (e :: u.allocation.1, u.allocation.2) ∈ orderedTransferTerms (e :: es) := by
      simp only [orderedTransferTerms, List.mem_append, List.mem_map]
      exact Or.inl ⟨u.allocation, ha, rfl⟩
    have hright : (u.allocation.1, e :: u.allocation.2) ∈ orderedTransferTerms (e :: es) := by
      simp only [orderedTransferTerms, List.mem_append, List.mem_map]
      exact Or.inr ⟨u.allocation, ha, rfl⟩
    simp only [jointTransferChildren, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | rfl | ⟨i, _, rfl⟩
    · exact ⟨hleft, by simpa using hc, hd⟩
    · exact ⟨hright, hc, by simpa using hd⟩
    · exact ⟨hright, by simpa using hc, by simpa using hd⟩

/-- The exact shared coefficient/input derivative budget, derived for each
actual branch. No power of frequency is introduced. Source: `k+j=q` after
`new:eq:carrier-ibp`, consumed by `app:ch_response:eq:direct-envelope-profile`. -/
theorem jointTransferTerms_order_budget
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (es : List (Euclidean n × P)) (t : JointTransferTerm n P M ι)
    (ht : t ∈ jointTransferTerms b es) :
    t.amplitude.derivativeCost + t.datumWord.length = es.length := by
  obtain ⟨ha, hc, hd⟩ := jointTransferTerms_spec b es t ht
  rw [hc, hd]
  exact (orderedTransferTerms_spec es t.allocation ha).2.2

/-- Actual ordered derivatives of the original input, with source and
parameter directions in their original order (`new:eq:carrier-ibp`). -/
def originalDatumDerivative (ds : List (Euclidean n × P))
    (a : Euclidean n × P → V) : Euclidean n × P → V :=
  orderedTransferAction (fun v a p => fderiv ℝ a p v) ds a

/-- Smooth original data have smooth ordered source/parameter derivatives;
this supplies the input for every finite compact IBP step (`new:eq:carrier-ibp`). -/
theorem contDiff_originalDatumDerivative
    {a : Euclidean n × P → V} (ha : ContDiff ℝ ∞ a) (ds : List (Euclidean n × P)) :
    ContDiff ℝ ∞ (originalDatumDerivative ds a) := by
  apply orderedTransferAction_preserves _ (ContDiff ℝ ∞) _ ds ha
  intro v g hg
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
