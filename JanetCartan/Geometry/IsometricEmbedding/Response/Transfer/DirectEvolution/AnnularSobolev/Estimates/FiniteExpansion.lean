module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.DatumTests
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.FourierAssembly.Words
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.FiniteFiber.Bounds

/-!
# Weighted Sobolev assembly of the literal annular expansion

The independent analytic inputs are the finite weak identity from the annular
weak-transfer construction and the L² norms of its actual realized branches.
Forward norms are produced by `exists_annularBranchElapsedGraph_of_primitive_jets`
and `norm_demodulatedL2Operator_le`; reverse norms use the literal adjoint branch
construction. The parent must instantiate these inputs for the SAME operator.
This module proves a conditional deduction, not existence of the annular graph.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped SchwartzMap
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open CompactTransfer FourierIntegral Pseudodifferential
open IsometricEmbedding.Response.NearCarrier.FiniteFiber
variable {n r : ℕ} {P M ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [Fintype ι]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

private theorem list_norm_sum_le {J : Type*} (l : List J) (f : J → H) (A : ℝ)
    (h : ∀ t ∈ l, ‖f t‖ ≤ A) : ‖(l.map f).sum‖ ≤ (l.length : ℝ) * A := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖f t‖ + ‖(ts.map f).sum‖ := norm_add_le _ _
      _ ≤ A + (ts.length : ℝ) * A :=
        add_le_add (h t (by simp)) (ih (fun v hv => h v (by simp [hv])))
      _ = _ := by ring

/-- A single order in the weighted sum of
`app:ch_response:eq:direct-envelope-profile`. The coefficient scale stays `L`. -/
theorem annular_weighted_term_le (s j q : ℕ) (hj : j ≤ q) (hq : q ≤ s)
    {L : ℝ} (hL : 1 ≤ L) (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k) :
    L ^ (q - j) * A j ≤ ∑ k ∈ Finset.range (s + 1), L ^ (s - k) * A k := by
  apply le_trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hL (Nat.sub_le_sub_right hq j)) (hA j))
  exact Finset.single_le_sum (fun k _ => mul_nonneg (pow_nonneg (by linarith) _) (hA k))
    (Finset.mem_range.mpr (by omega))

/-- The actual finite branch list sends a supplied ORIGINAL datum jet profile
to its weighted L² sum. This also applies to mixed source/parameter words;
no derivative is relabelled as a derivative of a different datum.
Source: the shared order count after `new:eq:carrier-ibp`. -/
theorem jointTransferTerms_norm_sum_le
    (b : OrthonormalBasis ι ℝ (CarrierVariables n)) (es : List (E × P))
    (N : ℕ) (he : es.length ≤ N) (T : JointTransferTerm n P M ι → H →L[ℂ] H)
    (a : E × P → V) (c : P)
    (ha : ∀ t ∈ jointTransferTerms (M := M) b es,
      MemLp (fun x => originalDatumDerivative t.datumWord a (x, c)) 2 volume)
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j) {C L lam : ℝ} (p : ℤ)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hlam : 0 < lam)
    (hb : ∀ t ∈ jointTransferTerms b es,
      ‖T t‖ ≤ C * lam ^ p * L ^ (es.length - t.datumWord.length))
    (hd : ∀ t (ht : t ∈ jointTransferTerms b es),
      ‖(ha t ht).toLp (fun x => originalDatumDerivative t.datumWord a (x, c))‖ ≤
        D t.datumWord.length) :
    ‖((jointTransferTerms (M := M) b es).attach.map fun t =>
      T t.val ((ha t.val t.property).toLp
        (fun x => originalDatumDerivative t.val.datumWord a (x, c)))).sum‖ ≤
      ((Fintype.card ι + 2 : ℕ) : ℝ) ^ N * C * lam ^ p *
        (∑ j ∈ Finset.range (N + 1), L ^ (N - j) * D j) := by
  let S := ∑ j ∈ Finset.range (N + 1), L ^ (N - j) * D j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    mul_nonneg (pow_nonneg (by linarith) _) (hD j)
  have ht (t : {t // t ∈ jointTransferTerms (M := M) b es}) :
      ‖T t.val ((ha t.val t.property).toLp
        (fun x => originalDatumDerivative t.val.datumWord a (x, c)))‖ ≤ C * lam ^ p * S := by
    calc
      _ ≤ ‖T t.val‖ * ‖(ha t.val t.property).toLp
          (fun x => originalDatumDerivative t.val.datumWord a (x, c))‖ :=
        (T t.val).le_opNorm _
      _ ≤ (C * lam ^ p * L ^ (es.length - t.val.datumWord.length)) *
          D t.val.datumWord.length :=
        mul_le_mul (hb _ t.property) (hd _ t.property) (norm_nonneg _) (by positivity)
      _ = C * lam ^ p * (L ^ (es.length - t.val.datumWord.length) *
          D t.val.datumWord.length) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (annular_weighted_term_le N _ es.length
          (jointTransferTerms_datum_length_le b es t.val t.property) he hL D hD) (by positivity)
  apply (list_norm_sum_le _ _ _ (fun t _ => ht t)).trans
  rw [List.length_attach, jointTransferTerms_length, Nat.cast_pow]
  calc
    _ ≤ ((Fintype.card ι + 2 : ℕ) : ℝ) ^ N * (C * lam ^ p * S) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_cast; omega) he) (by positivity)
    _ = _ := by ring

/-- Spatial compact-test deduction from the literal `jointTransferTerms` weak
identity and branch L² bounds. The datum derivative norm is PROVED above;
output membership is reconstructed from its actual distributional derivatives.
The coefficient/input budget is the proved exact branch identity.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem annular_sobolev_of_compact_expansion
    (s : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (T : JointTransferTerm n P M ι → H →L[ℂ] H)
    (L lam : ℝ) (p : ℤ) (hL : 1 ≤ L) (hlam : 0 < lam)
    (u : graphTestSpace n r) (w : H)
    (hw : ∀ is : List (Fin n), is.length ≤ s →
      orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (w : 𝓢'(E, V)) =
      ((jointTransferTerms (M := M) b (is.map fun i => (EuclideanSpace.single i 1, (0 : P)))).map
        fun t => (T t (graphTestToLp (annularTestDatumWord t.datumWord u)) : 𝓢'(E, V))).sum)
    (hb : ∀ is : List (Fin n), is.length ≤ s →
      ∀ t ∈ jointTransferTerms b (is.map fun i => (EuclideanSpace.single i 1, (0 : P))),
        ‖T t‖ ≤ C * lam ^ p * L ^ (is.length - t.datumWord.length)) :
    MemVectorFourierSobolev (s : ℝ) w ∧
      vectorFourierSobolevNorm (s : ℝ) w ≤
        (((r : ℝ) * (n + 1 : ℝ) ^ s) *
          (((Fintype.card ι + 2 : ℕ) : ℝ) ^ s * C *
            ((r : ℝ) * (1 + (n : ℝ) * (2 * Real.pi)) ^ s))) * lam ^ p *
          vectorSpatialEnvelopeProfile s L (graphTestToLp u) := by
  let S := vectorSpatialEnvelopeProfile s L (graphTestToLp u)
  let D := (r : ℝ) * (1 + (n : ℝ) * (2 * Real.pi)) ^ s
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)
  let es := fun is : List (Fin n) => is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))
  let v := fun is => ((jointTransferTerms (M := M) b (es is)).map fun t =>
    T t (graphTestToLp (annularTestDatumWord t.datumWord u))).sum
  have hword (is : List (Fin n)) (hi : is.length ≤ s) :
      ‖v is‖ ≤ (((Fintype.card ι + 2 : ℕ) : ℝ) ^ s * C * D) * lam ^ p * S := by
    have hterm (t : JointTransferTerm n P M ι) (ht : t ∈ jointTransferTerms b (es is)) :
        ‖T t (graphTestToLp (annularTestDatumWord t.datumWord u))‖ ≤
          C * lam ^ p * D * S := by
      have hj : t.datumWord.length ≤ is.length := by
        simpa [es] using jointTransferTerms_datum_length_le b (es is) t ht
      have hds := jointTransferTerms_spatial_datum_directions b (es is)
        (by intro e he; obtain ⟨i, _, rfl⟩ := List.mem_map.mp he; rfl) t ht
      have hd := annularTestDatumWord_norm_le t.datumWord (fun e he => (hds e he).1) u
      have hp : ((r : ℝ) * ((n : ℝ) * (2 * Real.pi)) ^ t.datumWord.length) ≤ D := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hbase : 0 ≤ (n : ℝ) * (2 * Real.pi) := by positivity
        exact (pow_le_pow_left₀ hbase (show (n : ℝ) * (2 * Real.pi) ≤
          1 + (n : ℝ) * (2 * Real.pi) by linarith) _).trans
          (pow_le_pow_right₀ (by linarith) (hj.trans hi))
      have hd' := hd.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      calc
        _ ≤ ‖T t‖ * ‖graphTestToLp (annularTestDatumWord t.datumWord u)‖ := (T t).le_opNorm _
        _ ≤ (C * lam ^ p * L ^ (is.length - t.datumWord.length)) *
            (D * vectorFourierSobolevNorm (t.datumWord.length : ℝ) (graphTestToLp u)) :=
          mul_le_mul (hb is hi t ht) hd' (norm_nonneg _) (by positivity)
        _ = C * lam ^ p * D * (L ^ (is.length - t.datumWord.length) *
            vectorFourierSobolevNorm (t.datumWord.length : ℝ) (graphTestToLp u)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (annular_weighted_term_le s _ is.length hj hi hL
            (fun j => vectorFourierSobolevNorm (j : ℝ) (graphTestToLp u))
            (fun _ => norm_nonneg _)) (by positivity)
    apply (list_norm_sum_le _ _ _ hterm).trans
    rw [jointTransferTerms_length, List.length_map, Nat.cast_pow]
    calc
      _ ≤ ((Fintype.card ι + 2 : ℕ) : ℝ) ^ s * (C * lam ^ p * D * S) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_cast; omega) hi) (by positivity)
      _ = _ := by ring
  have hweak (is : List (Fin n)) (hi : is.length ≤ s) :
      orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (w : 𝓢'(E, V)) = (v is : 𝓢'(E, V)) := by
    rw [hw is hi]
    change _ = (Lp.toTemperedDistributionCLM V volume 2) _
    rw [map_list_sum]
    simp only [List.map_map, Function.comp_def, Lp.toTemperedDistributionCLM_apply]
    rfl
  have h := graph_vector_sobolev_of_weak_words s w v
    ((((Fintype.card ι + 2 : ℕ) : ℝ) ^ s * C * D) * lam ^ p * S) hweak hword
  simpa only [D, S, mul_assoc] using h

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
