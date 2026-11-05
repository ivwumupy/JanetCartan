module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.OriginalProfiles.TermBounds

/-!
# Original annular mixed amplitude profiles

Source: `app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`.

The original elapsed symbol, masks, beta and selector produce the matrix
profile. Original supported parameter-envelope Sobolev norms produce the
envelope profile. The external Leibniz expansion spends at most `l` carrier
derivatives, independently of the subsequent source order `k`.
The only fixed loss is `n+1`, from source Sobolev embedding. No modified
amplitude, normalized jet or kernel estimate is an input.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral SymbolBudgets
open Complement.ParameterDerivatives Complement.InactiveSource JanetCartan.Pseudodifferential
variable {p d r : ℕ}
local notation "P" => Euclidean p
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Constants for the original mixed amplitude. Only dimension and the fixed
original profiles are arguments; scales, time, frequency, carrier value and
envelope data are absent. Source: `app:ch_response:lem:energy-carrier-jets`. -/
def originalMixedBudget (n r : ℕ) (O S B : ℕ → ℝ) (C : ℕ → ℕ → ℝ)
    (Mβ Mπ : ℝ) (l k : ℕ) : ℝ :=
  2 ^ l * ∑ m ∈ Finset.range (l + 1), sourceProductBudget n r
    (fun i => originalMatrixBudget O S B Mβ Mπ (i + m)) (C (l - m)) k

/-- Nonnegative mixed constants for the consuming `MixedBounds` estimate.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem originalMixedBudget_nonneg (n r : ℕ) {O S B : ℕ → ℝ} (C : ℕ → ℕ → ℝ)
    (hO : ∀ i, 0 ≤ O i) (hS : ∀ i, 0 ≤ S i) (hB : ∀ i, 0 ≤ B i)
    {Mβ Mπ : ℝ} (hβ : 0 ≤ Mβ) (hπ : 0 ≤ Mπ) (l k : ℕ) :
    0 ≤ originalMixedBudget n r O S B C Mβ Mπ l k := by
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ =>
    sourceProductBudget_nonneg _ _ (fun i => originalMatrixBudget_nonneg hO hS hB hβ hπ _) k)

private theorem norm_iteratedFDeriv_list_sum_le {ι : Type*} (l : List ι)
    (g : ι → E → F) {x : E} (hg : ∀ i ∈ l, ContDiffAt ℝ ∞ (g i) x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ (l.map (fun i ↦ g i y)).sum) x‖ ≤
      (l.map (fun i ↦ ‖iteratedFDeriv ℝ j (g i) x‖)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hsum : ContDiffAt ℝ ∞ (fun y ↦ (l.map (fun i ↦ g i y)).sum) x := by
      have hg' : ∀ a ∈ l, ContDiffAt ℝ ∞ (g a) x := fun a ha ↦ hg a (by simp [ha])
      clear ih hg
      induction l with
      | nil => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E ↦ (0 : F)) x)
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons]
        exact (hg' a (by simp)).add (ih (fun b hb ↦ hg' b (by simp [hb])))
    simp only [List.map_cons, List.sum_cons]
    change ‖iteratedFDeriv ℝ j (g i + fun y ↦ (l.map (fun i ↦ g i y)).sum) x‖ ≤ _
    rw [iteratedFDeriv_add_apply ((hg i (by simp)).of_le (by simp)) (hsum.of_le (by simp))]
    exact (norm_add_le _ _).trans (add_le_add le_rfl
      (ih (fun a ha ↦ hg a (by simp [ha]))))

/-- Original mixed annular profile in list directions. The envelope input
contains only the original carrier derivatives through `vs.length`; source
order `k` only raises their Sobolev order. Both orientations retain the
actual elapsed amplitude, masks, multiplier and fixed selector.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_sourceJet_annularExternalAmplitude_list_le
    (O S B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ Mπ : ℝ)
    (hO : ∀ i, 0 ≤ O i) (hS : ∀ i, 0 ≤ S i) (hB : ∀ i, 0 ≤ B i)
    (hβ : 0 ≤ Mβ) (hπ : 0 ≤ Mπ)
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {J : Set (TwoTimePoint d)} (hJ : IsOpen J)
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) J)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {V : Set P} {X U T : Set E} (hV : IsOpen V) (hX : IsOpen X)
    (hU : IsOpen U) (hT : IsCompact T)
    (hmap : ∀ q ∈ X ×ˢ U, elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ J)
    {a : P → E → F} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
    (has : ∀ c ∈ V, tsupport (a c) ⊆ T)
    {A₀ L K : ℝ} (hA : 0 ≤ A₀) (hL : 1 ≤ L) (hLK : L ≤ K) (hK : 1 ≤ K)
    (hβξ : ‖β ξ‖ ≤ Mβ) (hπξ : ‖π (lam⁻¹ • ξ)‖ ≤ Mπ)
    (vs : List (P × E)) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1)
    {c : P} (hc : c ∈ V) {x z : E} (hx : x ∈ X) (hz : z ∈ U)
    (hmem : ∀ (j : ℕ), j ≤ vs.length → ∀ (v : Fin j → P), (∀ i, ‖v i‖ ≤ 1) →
      ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
        ((parameterSource_memLp hT hV ha has j v hc).toLp
          (fun y => iteratedFDeriv ℝ j (fun q => a q y) c v)))
    (hprofile : ∀ (j : ℕ), j ≤ vs.length → ∀ (v : Fin j → P), (∀ i, ‖v i‖ ≤ 1) →
      ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hT hV ha has j v hc).toLp
          (fun y => iteratedFDeriv ℝ j (fun q => a q y) c v)) ≤ C j s * A₀ * K ^ (s + j))
    (k : ℕ)
    (hout : ∀ i ≤ k + vs.length,
      ‖iteratedFDeriv ℝ i χout (if adjoint then z else x)‖ ≤ O i)
    (hsource : ∀ i ≤ k + vs.length,
      ‖iteratedFDeriv ℝ i χsource (if adjoint then x else z)‖ ≤ S i)
    (hsymbol : ∀ i ≤ k + vs.length, ‖iteratedFDeriv ℝ i (jointAmplitude b)
      (elapsedPoint t ((if adjoint then (z, x) else (x, z)), ξ))‖ ≤ B i * L ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => parameterListJet (fun q =>
      annularExternalAmplitude adjoint (elapsedAmplitude b χout χsource β t)
        π lam a ξ q y) vs (c, x)) z‖ ≤
      originalMixedBudget (d + 1) r O S B C Mβ Mπ vs.length k *
        A₀ * K ^ (d + 1 + 1 + vs.length) * K ^ k := by
  let term := fun (s : List (P × E) × List (P × E)) =>
    originalAnnularLeibnizTerm adjoint b χout χsource β π t lam ξ a
      (s.1.map Prod.snd) (s.2.map Prod.fst) c x
  let D : ℝ := ∑ m ∈ Finset.range (vs.length + 1), sourceProductBudget (d + 1) r
    (fun i => originalMatrixBudget O S B Mβ Mπ (i + m)) (C (vs.length - m)) k
  have hDterm (m : ℕ) : 0 ≤ sourceProductBudget (d + 1) r
      (fun i => originalMatrixBudget O S B Mβ Mπ (i + m)) (C (vs.length - m)) k :=
    sourceProductBudget_nonneg _ _ (fun i => originalMatrixBudget_nonneg hO hS hB hβ hπ _) k
  have hscale : 0 ≤ A₀ * K ^ (d + 1 + 1 + vs.length) * K ^ k := by
    exact mul_nonneg (mul_nonneg hA (pow_nonneg (zero_le_one.trans hK) _))
      (pow_nonneg (zero_le_one.trans hK) _)
  have hterm (s : List (P × E) × List (P × E)) (hst : s ∈ parameterLeibnizSplittings vs) :
      ‖iteratedFDeriv ℝ k (term s) z‖ ≤ D * A₀ * K ^ (d + 1 + 1 + vs.length) * K ^ k := by
    have horders := parameterLeibnizSplittings_orders hst
    have hunits := parameterLeibnizSplittings_unit hv hst
    have hvs : ∀ v ∈ s.1.map Prod.snd, ‖v‖ ≤ 1 := by
      intro v hv
      rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
      exact (norm_snd_le w).trans (hunits.1 w hw)
    have hws : ∀ i : Fin (s.2.map Prod.fst).length,
        ‖(s.2.map Prod.fst).get i‖ ≤ 1 := by
      intro i
      have hv := List.get_mem (s.2.map Prod.fst) i
      rcases List.mem_map.mp hv with ⟨w, hw, he⟩
      rw [← he]
      exact (norm_fst_le w).trans (hunits.2 w hw)
    have hlen : (s.2.map Prod.fst).length ≤ vs.length := by simp only [List.length_map]; omega
    have h := norm_sourceJet_originalAnnularLeibnizTerm_le adjoint b χout χsource β π
      t lam ξ hJ hb ho hs hV hX hU hT hmap ha has hO hS hB hβ hπ hA hL hLK hK
      hβξ hπξ (s.1.map Prod.snd) (s.2.map Prod.fst) hvs hc hx hz
      (C (s.2.map Prod.fst).length)
      (hmem _ hlen _ hws) (hprofile _ hlen _ hws) k
      (fun i hi => hout i (by simp only [List.length_map] at hi; omega))
      (fun i hi => hsource i (by simp only [List.length_map] at hi; omega))
      (fun i hi => hsymbol i (by simp only [List.length_map] at hi; omega))
    have hl2 : s.2.length = vs.length - s.1.length := by omega
    simp only [List.length_map, horders] at h
    apply h.trans
    have hd : sourceProductBudget (d + 1) r
        (fun i => originalMatrixBudget O S B Mβ Mπ (i + s.1.length)) (C s.2.length) k ≤ D := by
      rw [hl2]
      exact Finset.single_le_sum (fun m _ => hDterm m)
        (Finset.mem_range_succ_iff.mpr (by omega))
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd hscale
  have hsmooth (s : List (P × E) × List (P × E)) : ContDiffAt ℝ ∞ (term s) z := by
    have hm := contDiffOn_parameterListJet_joint hX hU
      (contDiffOn_originalAnnularMatrix adjoint b χout χsource β π t lam ξ hb ho hs hmap)
      (s.1.map Prod.snd)
    have hmz : ContDiffOn ℝ ∞ (fun y => parameterListJet (fun w =>
        originalAnnularMatrix adjoint b χout χsource β π t lam ξ (w, y))
          (s.1.map Prod.snd) x) U :=
      hm.comp (s := U) (f := fun y : E => (x, y))
        (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨hx, hy⟩)
    exact ((annularMatrixAction r).contDiff.contDiffAt.comp z
      (hmz.contDiffAt (hU.mem_nhds hz))).clm_apply
        (contDiff_originalSourceListJet hV ha (s.2.map Prod.fst) hc).contDiffAt
  have he : (fun y => parameterListJet (fun q => annularExternalAmplitude adjoint
      (elapsedAmplitude b χout χsource β t) π lam a ξ q y) vs (c, x)) =ᶠ[𝓝 z]
      (fun y => ((parameterLeibnizSplittings vs).map (fun s => term s y)).sum) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact parameterListJet_annularExternalAmplitude adjoint b χout χsource β π t lam ξ
      hb ho hs hV hX hmap ha vs hc hx hy
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  apply (norm_iteratedFDeriv_list_sum_le _ term (fun s _ => hsmooth s) k).trans
  apply (List.sum_le_sum hterm).trans_eq
  simp only [List.map_const', List.sum_replicate, length_parameterLeibnizSplittings,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, originalMixedBudget]
  dsimp [D]
  ring

/-- The original mixed vector-amplitude profile in arbitrary unit external
Fréchet directions, for both orientations. The constants are literally
`originalMixedBudget`, defined before all varying data. The estimate keeps
linear `A₀`, one source factor `K^k`, and the fixed Sobolev reserve `n+1`.
Only carrier-envelope derivatives `j ≤ l` are assumed, even when `k` grows.
It holds for every `λ`; in particular for `1 ≤ L ≤ K ≤ λ^(1-ν)`.
Source: `app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_mixed_originalAnnularAmplitude_le
    (O S B : ℕ → ℝ) (C : ℕ → ℕ → ℝ) (Mβ Mπ : ℝ)
    (hO : ∀ i, 0 ≤ O i) (hS : ∀ i, 0 ≤ S i) (hB : ∀ i, 0 ≤ B i)
    (hβ : 0 ≤ Mβ) (hπ : 0 ≤ Mπ)
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {J : Set (TwoTimePoint d)} (hJ : IsOpen J)
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) J)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {V : Set P} {X U T : Set E} (hV : IsOpen V) (hX : IsOpen X)
    (hU : IsOpen U) (hT : IsCompact T)
    (hmap : ∀ q ∈ X ×ˢ U, elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ J)
    {a : P → E → F} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
    (has : ∀ c ∈ V, tsupport (a c) ⊆ T)
    {A₀ L K : ℝ} (hA : 0 ≤ A₀) (hL : 1 ≤ L) (hLK : L ≤ K) (hK : 1 ≤ K)
    (hβξ : ‖β ξ‖ ≤ Mβ) (hπξ : ‖π (lam⁻¹ • ξ)‖ ≤ Mπ)
    (l : ℕ) (v : Fin l → P × E) (hv : ∀ i, ‖v i‖ ≤ 1)
    {c : P} (hc : c ∈ V) {x z : E} (hx : x ∈ X) (hz : z ∈ U)
    (hmem : ∀ (j : ℕ), j ≤ l → ∀ (v : Fin j → P), (∀ i, ‖v i‖ ≤ 1) →
      ∀ s : ℕ, MemVectorFourierSobolev (s : ℝ)
        ((parameterSource_memLp hT hV ha has j v hc).toLp
          (fun y => iteratedFDeriv ℝ j (fun q => a q y) c v)))
    (hprofile : ∀ (j : ℕ), j ≤ l → ∀ (v : Fin j → P), (∀ i, ‖v i‖ ≤ 1) →
      ∀ s : ℕ, vectorFourierSobolevNorm (s : ℝ)
        ((parameterSource_memLp hT hV ha has j v hc).toLp
          (fun y => iteratedFDeriv ℝ j (fun q => a q y) c v)) ≤ C j s * A₀ * K ^ (s + j))
    (k : ℕ)
    (hout : ∀ i ≤ k + l,
      ‖iteratedFDeriv ℝ i χout (if adjoint then z else x)‖ ≤ O i)
    (hsource : ∀ i ≤ k + l,
      ‖iteratedFDeriv ℝ i χsource (if adjoint then x else z)‖ ≤ S i)
    (hsymbol : ∀ i ≤ k + l, ‖iteratedFDeriv ℝ i (jointAmplitude b)
      (elapsedPoint t ((if adjoint then (z, x) else (x, z)), ξ))‖ ≤ B i * L ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => iteratedFDeriv ℝ l (fun q =>
      annularExternalAmplitude adjoint (elapsedAmplitude b χout χsource β t)
        π lam a ξ q y) (c, x) v) z‖ ≤
      originalMixedBudget (d + 1) r O S B C Mβ Mπ l k *
        A₀ * K ^ (d + 1 + 1 + l) * K ^ k := by
  have hvlist : ∀ w ∈ List.ofFn v, ‖w‖ ≤ 1 := by
    intro w hw
    rcases List.mem_ofFn.mp hw with ⟨i, rfl⟩
    exact hv i
  have h := norm_sourceJet_annularExternalAmplitude_list_le O S B C Mβ Mπ hO hS hB hβ hπ
    adjoint b χout χsource β π t lam ξ hJ hb ho hs hV hX hU hT hmap ha has
    hA hL hLK hK hβξ hπξ (List.ofFn v) hvlist hc hx hz
    (by simpa only [List.length_ofFn] using hmem)
    (by simpa only [List.length_ofFn] using hprofile) k
    (by simpa only [List.length_ofFn] using hout)
    (by simpa only [List.length_ofFn] using hsource)
    (by simpa only [List.length_ofFn] using hsymbol)
  simpa only [List.length_ofFn, parameterListJet_ofFn] using h

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
