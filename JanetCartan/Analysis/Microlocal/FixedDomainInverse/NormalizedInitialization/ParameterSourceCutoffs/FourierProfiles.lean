module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ParameterSourceCutoffs.Jets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphDecay.Normalization

/-!
# Reserved source profiles after the fixed parameter split

Each Leibniz term differentiates the original source no more often than the
complete parameter word. For frequency at least one, its natural reserved
weight is therefore no greater than the original weight. Finite summation
changes only a constant, uniformly in all histories and unit direction tuples.
The consumers are the selected characteristic and inactive graph estimates in
`app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ParameterSourceCutoffs

open Pseudodifferential ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open ResponseTransfer.Complement.ParameterDerivatives.UniformJetLimit

variable {n r : ℕ} {I P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

private theorem reserved_source_list_sum_bound {J : Type*}
    (ss : List J) (f : J → E → F) (s : ℕ) (C : ℝ)
    (hf : ∀ j ∈ ss, ∃ hm : MemLp (f j) 2 volume,
      MemVectorFourierSobolev (s : ℝ) (hm.toLp (f j)) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp (f j)) ≤ C) :
    let g := fun y ↦ (ss.map (fun j ↦ f j y)).sum
    ∃ hm : MemLp g 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp g) ∧
      vectorFourierSobolevNorm (s : ℝ) (hm.toLp g) ≤ (ss.length : ℝ) * C := by
  let G : GradedScale H := vectorFourierSobolevScale
  induction ss with
  | nil =>
    refine ⟨MemLp.zero, (G.level s).zero_mem, ?_⟩
    change vectorFourierSobolevNorm (s : ℝ) (0 : H) ≤ (([] : List J).length : ℝ) * C
    simp only [List.length_nil, Nat.cast_zero]
    rw [zero_mul, ← vectorFourierSobolevScale_gradeNorm s ((G.level s).zero_mem)]
    change G.gradeNorm s 0 ≤ 0
    rw [G.gradeNorm_eq ((G.level s).zero_mem)]
    exact le_of_eq (map_zero (G.seminorm s))
  | cons j ss ih =>
    obtain ⟨hmj,hmjS,hbj⟩ := hf j (by simp)
    obtain ⟨hms,hmsS,hbs⟩ := ih (fun k hk ↦ hf k (by simp [hk]))
    let hm := hmj.add hms
    have hsum : MemVectorFourierSobolev (s : ℝ)
        (hmj.toLp (f j) + hms.toLp (fun y ↦ (ss.map (fun k ↦ f k y)).sum)) :=
      (G.level s).add_mem hmjS hmsS
    refine ⟨hm, hsum, ?_⟩
    have hb := gradeNorm_add_le G hmjS hmsS
    rw [vectorFourierSobolevScale_gradeNorm s hsum,
      vectorFourierSobolevScale_gradeNorm s hmjS,
      vectorFourierSobolevScale_gradeNorm s hmsS] at hb
    change vectorFourierSobolevNorm (s : ℝ)
      (hmj.toLp (f j) + hms.toLp (fun y ↦ (ss.map (fun k ↦ f k y)).sum)) ≤ _
    calc
      _ ≤ C + (ss.length : ℝ)*C := hb.trans (add_le_add hbj hbs)
      _ = ((j::ss).length : ℝ)*C := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- A fixed compact smooth parameter cutoff and its complement preserve the
original natural reserved source Fourier bounds. The single new constant
family works for both branches and every supplied source, parameter, history
index and unit direction tuple. The source functions are literal scalar
products; no representative or source is selected anew. This supplies the
source hypotheses of the selected active/inactive estimates in
`app:ch_response:eq:fixed-factor-transfer`. -/
theorem exists_reserved_source_fourier_profiles_cutoff_and_complement
    (χ : P → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (Csource : ℕ → ℕ → ℝ) :
    ∃ Ccut : ℕ → ℕ → ℝ, (∀ l s, 0 ≤ Ccut l s) ∧
      ∀ (a : I → E × P → F), (∀ i, ContDiff ℝ ∞ (a i)) →
      ∀ (A K : I → ℝ), (∀ i, 0 ≤ A i) → (∀ i, 1 ≤ K i) →
      ∀ (reserve : ℕ) (V : Set P),
      (∀ i c, c ∈ V → ∀ l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
            Csource l s * A i * K i ^ (s+l-reserve)) →
      ∀ inactive : Bool, ∀ i c, c ∈ V →
      ∀ l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
        let θ := if inactive then (fun b ↦ 1-χ b) else χ
        let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ θ q • a i (y,q)) c w
        ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
            Ccut l s * A i * K i ^ (s+l-reserve) := by
  classical
  obtain ⟨B,hB,hjet⟩ := exists_cutoff_and_complement_list_jet_bounds χ hχ hcχ
  let D (l s : ℕ) : ℝ := ∑ k ∈ Finset.range (l+1), |Csource k s|
  have hD l s : 0 ≤ D l s := Finset.sum_nonneg (fun k _ ↦ abs_nonneg _)
  have hCD {l k : ℕ} (hk : k ≤ l) (s : ℕ) : Csource k s ≤ D l s :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ ↦ abs_nonneg (Csource j s))
      (Finset.mem_range.mpr (by omega)))
  refine ⟨fun l s ↦ (2 : ℝ)^l * B l * D l s,
    fun l s ↦ mul_nonneg (mul_nonneg (by positivity) (hB l)) (hD l s), ?_⟩
  intro a ha A K hA hK reserve V hsource inactive i c hc l w hw s θ f
  have hθ : ContDiff ℝ ∞ θ := by
    dsimp [θ]
    split
    · exact contDiff_const.sub hχ
    · exact hχ
  have hθjet (ps : List P) (hlen : ps.length ≤ l) (hps : ∀ v ∈ ps, ‖v‖ ≤ 1) :
      ‖parameterListJet θ ps c‖ ≤ B l := by
    obtain ⟨hactive,hinactive⟩ := hjet l ps hlen hps c
    dsimp [θ]
    split
    · exact hinactive
    · exact hactive
  have hd (v : P) (hv : v ∈ List.ofFn w) : ‖v‖ ≤ 1 := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    exact hw j
  let terms (q : List P × List P) (y : E) : F :=
    parameterListJet θ q.1 c • parameterListJet (fun b ↦ a i (y,b)) q.2 c
  have hterms q (hq : q ∈ parameterLeibnizSplittings (List.ofFn w)) :
      ∃ hm : MemLp (terms q) 2 volume,
        MemVectorFourierSobolev (s : ℝ) (hm.toLp (terms q)) ∧
          vectorFourierSobolevNorm (s : ℝ) (hm.toLp (terms q)) ≤
            B l * D l s * A i * K i ^ (s+l-reserve) := by
    have horders := parameterLeibnizSplittings_orders hq
    rw [List.length_ofFn] at horders
    obtain ⟨hd₁,hd₂⟩ := parameterLeibnizSplittings_directions hq
    have hunit₁ : ∀ v ∈ q.1, ‖v‖ ≤ 1 := fun v hv ↦ hd v (hd₁ v hv)
    have hunit₂ : ∀ j, ‖q.2.get j‖ ≤ 1 :=
      fun j ↦ hd (q.2.get j) (hd₂ _ (List.get_mem q.2 j))
    obtain ⟨hm,hmS,hbound⟩ := hsource i c hc q.2.length q.2.get hunit₂ s
    have hscalar := hθjet q.1 (by omega) hunit₁
    obtain ⟨hsm,hsmnorm⟩ := vectorFourierSobolevNorm_parameter_real_smul s
      (parameterListJet θ q.1 c) hmS
    refine ⟨hm.const_smul (parameterListJet θ q.1 c), hsm, ?_⟩
    change vectorFourierSobolevNorm (s : ℝ)
      (parameterListJet θ q.1 c • hm.toLp _) ≤ _
    rw [hsmnorm, ← Real.norm_eq_abs]
    have hbase : vectorFourierSobolevNorm (s : ℝ) (hm.toLp _) ≤
        D l s * A i * K i ^ (s+l-reserve) := by
      calc
        _ ≤ Csource q.2.length s * A i * K i ^ (s+q.2.length-reserve) := hbound
        _ ≤ D l s * A i * K i ^ (s+q.2.length-reserve) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hCD (by omega) s) (hA i))
            (pow_nonneg (le_trans zero_le_one (hK i)) _)
        _ ≤ D l s * A i * K i ^ (s+l-reserve) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (hK i) (by omega)) (mul_nonneg (hD l s) (hA i))
    calc
      _ ≤ B l * (D l s * A i * K i ^ (s+l-reserve)) :=
        mul_le_mul hscalar hbase (norm_nonneg _) (hB l)
      _ = B l * D l s * A i * K i ^ (s+l-reserve) := by ring
  obtain ⟨hms,hmsS,hbs⟩ := reserved_source_list_sum_bound
    (parameterLeibnizSplittings (List.ofFn w)) terms s
      (B l * D l s * A i * K i ^ (s+l-reserve)) hterms
  have he : f = fun y ↦ ((parameterLeibnizSplittings (List.ofFn w)).map
      (fun q ↦ terms q y)).sum := by
    funext y
    dsimp [f]
    rw [← parameterListJet_ofFn]
    exact parameterListJet_real_smul θ (fun q ↦ a i (y,q)) isOpen_univ hθ.contDiffOn
      ((ha i).comp (contDiff_const.prodMk contDiff_id)).contDiffOn _ (mem_univ c)
  rw [he]
  refine ⟨hms,hmsS,?_⟩
  exact hbs.trans_eq (by
    rw [parameterLeibnizSplittings_length, List.length_ofFn, Nat.cast_pow, Nat.cast_ofNat]
    ring)

end JanetCartan.FixedDomainInverse.ParameterSourceCutoffs
