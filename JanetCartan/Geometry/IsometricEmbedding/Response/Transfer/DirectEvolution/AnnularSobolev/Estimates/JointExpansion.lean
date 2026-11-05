module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.FiniteExpansion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Estimates.JointDatum

/-!
# Joint output/parameter Sobolev deduction

Spatial and parameter derivatives share the total order `s + ps.length` in
`new:eq:carrier-ibp`. The datum representatives below are required to equal
actual `originalDatumDerivative` words almost everywhere. Their bounds are
proved from the ORIGINAL mixed jets, not supplied as transferred-envelope
bounds. The weak-transfer producer identifies `output` with the actual
parameter derivative distribution; the displayed weak expansion is that producer's
precise independent input. The parent retains this instantiation obligation.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped SchwartzMap ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open CompactTransfer FourierIntegral Pseudodifferential
variable {n r : ℕ} {P M ι : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup M] [NormedSpace ℝ M] [Fintype ι]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- Joint Sobolev reconstruction for the actual mixed original-datum words.
`output` is the parameter derivative distribution supplied by weak transfer.
Its L² representative and Sobolev membership are CONSTRUCTED. Only the literal
weak identities and branch operator bounds are
assumed for the output. Datum-word bounds follow from the original mixed
Fréchet jets on the fixed parameter slice, using only total orders at most
`s + ps.length`. Source: `new:eq:carrier-ibp` and the joint assertion after
`app:ch_response:eq:direct-envelope-profile`. -/
theorem annular_joint_sobolev_of_expansion
    (s : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (b : OrthonormalBasis ι ℝ (CarrierVariables n))
    (ps : List P) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1)
    (T : JointTransferTerm n P M ι → H →L[ℂ] H)
    (L lam : ℝ) (p : ℤ) (hL : 1 ≤ L) (hlam : 0 < lam)
    (a : E × P → V) (ha : ContDiff ℝ ∞ a) (c : P)
    (da : List (E × P) → H)
    (hda : ∀ ds, ds.length ≤ s + ps.length → (∀ v ∈ ds, ‖v‖ ≤ 1) →
      (da ds : E → V) =ᵐ[volume] fun x => originalDatumDerivative ds a (x, c))
    (D : ℕ → ℝ) (hD : ∀ j, 0 ≤ D j)
    (hj : ∀ j, j ≤ s + ps.length →
      ∃ hm : MemLp (fun x : E => iteratedFDeriv ℝ j a (x, c)) 2 volume,
        ‖hm.toLp (fun x : E => iteratedFDeriv ℝ j a (x, c))‖ ≤ D j)
    (output : 𝓢'(E, V))
    (hw : ∀ is : List (Fin n), is.length ≤ s →
      orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        output =
      ((jointTransferTerms (M := M) b
        ((is.map fun i => (EuclideanSpace.single i 1, (0 : P))) ++
          ps.map (fun v => ((0 : E), v)))).map
        fun t => (T t (da t.datumWord) : 𝓢'(E, V))).sum)
    (hb : ∀ is : List (Fin n), is.length ≤ s →
      ∀ t ∈ jointTransferTerms b
        ((is.map fun i => (EuclideanSpace.single i 1, (0 : P))) ++
          ps.map (fun v => ((0 : E), v))),
        ‖T t‖ ≤ C * lam ^ p * L ^ (is.length + ps.length - t.datumWord.length)) :
    ∃ w : H, (w : 𝓢'(E, V)) = output ∧
      MemVectorFourierSobolev (s : ℝ) w ∧
      vectorFourierSobolevNorm (s : ℝ) w ≤
        (((r : ℝ) * (n + 1 : ℝ) ^ s) *
          (((Fintype.card ι + 2 : ℕ) : ℝ) ^ (s + ps.length) * C)) * lam ^ p *
          (∑ j ∈ Finset.range (s + ps.length + 1), L ^ (s + ps.length - j) * D j) := by
  let w : H := ((jointTransferTerms (M := M) b
    (ps.map fun v => ((0 : E), v))).map fun t => T t (da t.datumWord)).sum
  have hroot : (w : 𝓢'(E, V)) = output := by
    have h := hw [] (by simp)
    simp only [orderedTransferAction, List.map_nil, List.nil_append] at h
    rw [h]
    change (Lp.toTemperedDistributionCLM V volume 2) _ = _
    rw [map_list_sum]
    simp only [List.map_map, Function.comp_def, Lp.toTemperedDistributionCLM_apply]
  let N := s + ps.length
  let es := fun is : List (Fin n) =>
    (is.map fun i => (EuclideanSpace.single i (1 : ℝ), (0 : P))) ++
      ps.map (fun v => ((0 : E), v))
  have hlen (is : List (Fin n)) : (es is).length = is.length + ps.length := by simp [es]
  have hdirs (is : List (Fin n)) : ∀ e ∈ es is, ‖e.2‖ ≤ 1 := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      simp
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
      exact hps v hv
  let v := fun is => ((jointTransferTerms (M := M) b (es is)).map fun t => T t (da t.datumWord)).sum
  have hword (is : List (Fin n)) (hi : is.length ≤ s) :
      ‖v is‖ ≤ (((Fintype.card ι + 2 : ℕ) : ℝ) ^ N * C) * lam ^ p *
        (∑ j ∈ Finset.range (N + 1), L ^ (N - j) * D j) := by
    have hn : (es is).length ≤ N := by rw [hlen]; exact Nat.add_le_add_right hi _
    have hd (t : JointTransferTerm n P M ι) (ht : t ∈ jointTransferTerms b (es is)) :
        ∃ hm : MemLp (fun x : E => originalDatumDerivative t.datumWord a (x, c)) 2 volume,
          ‖hm.toLp (fun x : E => originalDatumDerivative t.datumWord a (x, c))‖ ≤
            D t.datumWord.length := by
      have hjn := (jointTransferTerms_datum_length_le b (es is) t ht).trans hn
      obtain ⟨hm, hbound⟩ := hj t.datumWord.length hjn
      obtain ⟨hm', hn'⟩ := originalDatumDerivative_memLp_norm_le ha t.datumWord
        (jointTransferTerms_mixed_datum_directions b (es is) (hdirs is) t ht) c hm
      exact ⟨hm', hn'.trans hbound⟩
    choose hm hmBound using hd
    have heq (t : JointTransferTerm n P M ι) (ht : t ∈ jointTransferTerms b (es is)) :
        (hm t ht).toLp (fun x : E => originalDatumDerivative t.datumWord a (x, c)) =
          da t.datumWord := by
      apply Lp.ext
      exact (hm t ht).coeFn_toLp.trans
        (hda t.datumWord
          ((jointTransferTerms_datum_length_le b (es is) t ht).trans hn)
          (jointTransferTerms_mixed_datum_directions b (es is) (hdirs is) t ht)).symm
    have h := jointTransferTerms_norm_sum_le b (es is) N hn T a c hm D hD p hC hL hlam
      (fun t ht => by simpa only [hlen] using hb is hi t ht) hmBound
    have he : ((jointTransferTerms (M := M) b (es is)).attach.map fun t =>
        T t.val ((hm t.val t.property).toLp
          (fun x => originalDatumDerivative t.val.datumWord a (x, c)))).sum = v is := by
      change _ = ((jointTransferTerms (M := M) b (es is)).map
        (fun t => T t (da t.datumWord))).sum
      rw [← List.attach_map_val (l := jointTransferTerms (M := M) b (es is))
        (f := fun t => T t (da t.datumWord))]
      congr 1
      apply List.map_congr_left
      intro t _
      rw [heq t.val t.property]
    simpa only [he] using h
  have hweak (is : List (Fin n)) (hi : is.length ≤ s) :
      orderedTransferAction (fun i => lineDerivOp (EuclideanSpace.single i (1 : ℝ))) is
        (w : 𝓢'(E, V)) = (v is : 𝓢'(E, V)) := by
    rw [hroot, hw is hi]
    change _ = (Lp.toTemperedDistributionCLM V volume 2) _
    rw [map_list_sum]
    simp only [List.map_map, Function.comp_def, Lp.toTemperedDistributionCLM_apply]
    rfl
  have h := graph_vector_sobolev_of_weak_words s w v
    ((((Fintype.card ι + 2 : ℕ) : ℝ) ^ N * C) * lam ^ p *
      (∑ j ∈ Finset.range (N + 1), L ^ (N - j) * D j)) hweak hword
  exact ⟨w, hroot, by simpa only [N, mul_assoc] using h⟩

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
