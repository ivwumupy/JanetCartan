module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.DatumTests

/-!
# Bounds for the actual mixed original-datum derivatives

The joint count in `new:eq:carrier-ibp` uses a single total order for source and
parameter derivatives. These lemmas identify each stored original word with
the actual Fréchet jet and deduce its L² bound from that jet of the original
family. No bound on an output or a transferred envelope is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open CompactTransfer Pseudodifferential
variable {n r : ℕ} {P M ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [Fintype ι]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- Every mixed original-datum direction is unit bounded when the external
parameter directions are; the source directions come from the fixed
orthonormal basis. Source: the four literal terms of `new:eq:carrier-ibp`. -/
theorem jointTransferTerms_mixed_datum_directions
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (es : List (E × P)) (he : ∀ e ∈ es, ‖e.2‖ ≤ 1)
    (t : JointTransferTerm n P M ι) (ht : t ∈ jointTransferTerms b es) :
    ∀ v ∈ t.datumWord, ‖v‖ ≤ 1 := by
  induction es generalizing t with
  | nil =>
    simp only [jointTransferTerms, orderedTransferAction, List.mem_singleton] at ht
    subst t
    simp [initialJointTransferTerm]
  | cons e es ih =>
    change t ∈ (jointTransferTerms b es).flatMap (jointTransferChildren b e) at ht
    obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
    have hu' := ih (fun v hv => he v (List.mem_cons_of_mem e hv)) u hu
    simp only [jointTransferChildren, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | rfl | ⟨i, _, rfl⟩
    · exact hu'
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · simpa using he e List.mem_cons_self
      · exact hu' v hv
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · simpa using (WithLp.norm_fst_le _ (b i)).trans (b.norm_eq_one i).le
      · exact hu' v hv

/-- The original mixed word is exactly the original Fréchet jet evaluated on
its ordered directions. Consumer: the datum estimate in the joint version of
`app:ch_response:eq:direct-envelope-profile`. -/
theorem originalDatumDerivative_ofFn_eq_iteratedFDeriv {k : ℕ}
    {a : E × P → V} (ha : ContDiff ℝ ∞ a) (v : Fin k → E × P) (q : E × P) :
    originalDatumDerivative (List.ofFn v) a q = iteratedFDeriv ℝ k a q v := by
  induction k generalizing q with
  | zero => simp [originalDatumDerivative, orderedTransferAction, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (originalDatumDerivative (List.ofFn (fun i => v i.succ)) a) q (v 0) = _
    rw [show originalDatumDerivative (List.ofFn (fun i => v i.succ)) a =
      (fun y => iteratedFDeriv ℝ k a y (fun i => v i.succ)) from funext (fun y => ih _ y)]
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left']
    · rfl
    · exact (ContDiff.differentiable_iteratedFDeriv (n := ∞) (m := k)
        (by exact_mod_cast ENat.natCast_lt_top k) ha).differentiableAt

/-- Unit bounded mixed directions do not increase the norm of the actual
original jet (`new:eq:carrier-ibp`). -/
theorem norm_originalDatumDerivative_le_iteratedFDeriv
    {a : E × P → V} (ha : ContDiff ℝ ∞ a) (ds : List (E × P))
    (hds : ∀ v ∈ ds, ‖v‖ ≤ 1) (q : E × P) :
    ‖originalDatumDerivative ds a q‖ ≤ ‖iteratedFDeriv ℝ ds.length a q‖ := by
  have h := originalDatumDerivative_ofFn_eq_iteratedFDeriv ha ds.get q
  rw [List.ofFn_get] at h
  rw [h]
  exact (iteratedFDeriv ℝ ds.length a q).unit_le_opNorm
    (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr (fun i => hds _ (List.get_mem ..)))

/-- L² membership and norm of every actual mixed original-datum word follow
from the original family's mixed jet on the SAME parameter slice. Consumer:
`annular_joint_sobolev_of_expansion`. Source: the joint-order assertion after
`app:ch_response:eq:direct-envelope-profile`. -/
theorem originalDatumDerivative_memLp_norm_le
    {a : E × P → V} (ha : ContDiff ℝ ∞ a) (ds : List (E × P))
    (hds : ∀ v ∈ ds, ‖v‖ ≤ 1) (c : P)
    (hj : MemLp (fun x : E => iteratedFDeriv ℝ ds.length a (x, c)) 2 volume) :
    ∃ hd : MemLp (fun x : E => originalDatumDerivative ds a (x, c)) 2 volume,
      ‖hd.toLp (fun x : E => originalDatumDerivative ds a (x, c))‖ ≤
        ‖hj.toLp (fun x : E => iteratedFDeriv ℝ ds.length a (x, c))‖ := by
  have hm : AEStronglyMeasurable (fun x : E => originalDatumDerivative ds a (x, c)) volume :=
    ((contDiff_originalDatumDerivative ha ds).comp
      (contDiff_id.prodMk contDiff_const)).continuous.aestronglyMeasurable
  have hb := fun x : E => norm_originalDatumDerivative_le_iteratedFDeriv ha ds hds (x, c)
  have hd := hj.of_le hm (Filter.Eventually.of_forall hb)
  refine ⟨hd, ?_⟩
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono hj.eLpNorm_ne_top (eLpNorm_mono hm hb)

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
