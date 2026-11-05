module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.MixedBounds.Expansion

/-!
# Normalized source jets from finite external-order mixed profiles

The scalar phase / original amplitude Leibniz splitting preserves the original
amplitude's external order cap `j`, independently of the source order `k`.
The fixed loss is `ρ^j K^(b+j)` and the source loss is exactly `K^k`.

Source: `app:ch_response:lem:energy-carrier-jets`.
Consumer: the parent assembly into `SourceBounds.norm_annularSourceIntegral_le`.
The explicit mixed input is produced by task `jc-annular-original-amplitude-profile`;
the parent must instantiate it for the literal physical/demodulated amplitude.
No profile of a normalized jet is assumed here.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
open Complement.ParameterDerivatives Complement.ParameterDerivatives.UniformJetLimit
open JanetCartan.Localization
variable {P Z F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A finite constant fixed before frequency, scale, amplitude size, functions
and unit directions. Only amplitude external orders through `j` occur.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
def mixedExternalJetBudget (H : ℕ → ℝ) (Q : ℕ → ℕ → ℝ) (j k : ℕ) : ℝ :=
  (2 : ℝ) ^ j * ∑ a ∈ Finset.range (j + 1), ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * externalJetBudget H (fun m => if m = 0 then 1 else 0) a i *
      Q (j - a) (k - i)

/-- Nonnegativity of the finite mixed budget in the annular source estimate.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem mixedExternalJetBudget_nonneg {H : ℕ → ℝ} {Q : ℕ → ℕ → ℝ}
    (hH : ∀ m, 0 ≤ H m) (hQ : ∀ l q, 0 ≤ Q l q) (j k : ℕ) :
    0 ≤ mixedExternalJetBudget H Q j k := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (externalJetBudget_nonneg hH (fun m => by split_ifs <;> positivity) a i)) (hQ _ _)

private theorem norm_iteratedFDeriv_list_sum_le {ι : Type} (l : List ι)
    (g : ι → Z → F) {z : Z} (hg : ∀ i ∈ l, ContDiffAt ℝ ∞ (g i) z) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => (l.map (fun i => g i y)).sum) z‖ ≤
      (l.map (fun i => ‖iteratedFDeriv ℝ k (g i) z‖)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hsum : ContDiffAt ℝ ∞ (fun y => (l.map (fun i => g i y)).sum) z := by
      have hg' : ∀ a ∈ l, ContDiffAt ℝ ∞ (g a) z := fun a ha => hg a (by simp [ha])
      clear ih hg
      induction l with
      | nil => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Z => (0 : F)) z)
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons]
        exact (hg' a (by simp)).add (ih (fun b hb => hg' b (by simp [hb])))
    simp only [List.map_cons, List.sum_cons]
    change ‖iteratedFDeriv ℝ k (g i + fun y => (l.map (fun i => g i y)).sum) z‖ ≤ _
    rw [iteratedFDeriv_add_apply ((hg i (by simp)).of_le (by simp)) (hsum.of_le (by simp))]
    exact (norm_add_le _ _).trans (add_le_add le_rfl
      (ih (fun a ha => hg a (by simp [ha]))))

/-- Quantitative source estimate for the actual normalized external jet from
the ORIGINAL mixed amplitude profile. Amplitude external orders are at most
`j`, amplitude source orders at most `k`, and joint phase orders at most `k+j`.
The fixed exponent `b` is chosen before source order; neither the frequency
degree `j` nor the external loss `b+j` grows with that source order.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_normalizedExternalJet_source_le_mixed
    {V : Set P} {U : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    {φ : P → Z → ℝ} {u : P → Z → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (H : ℕ → ℝ) (Q : ℕ → ℕ → ℝ)
    (hH : ∀ m, 0 ≤ H m) (hQ : ∀ l q, 0 ≤ Q l q)
    {K A ρ : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hρ : 1 ≤ ρ)
    (b j : ℕ) (v : Fin j → P) (hv : ∀ i, ‖v i‖ ≤ 1)
    {p : P} (hp : p ∈ V) {z : Z} (hz : z ∈ U) (k : ℕ)
    (hphase : ∀ m ≤ k + j,
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (p, z)‖ ≤ H m * K ^ m)
    (hamplitude : ∀ l ≤ j, ∀ w : Fin l → P, (∀ i, ‖w i‖ ≤ 1) → ∀ q ≤ k,
      ‖iteratedFDeriv ℝ q (fun y => iteratedFDeriv ℝ l (fun a => u a y) p w) z‖ ≤
        Q l q * A * K ^ (b + l) * K ^ q) :
    ‖iteratedFDeriv ℝ k (normalizedExternalJet (fun q y => ρ * φ q y) u j v p) z‖ ≤
      mixedExternalJetBudget H Q j k * (A * ρ ^ j * K ^ (b + j)) * K ^ k := by
  let ψ : P → Z → ℝ := fun q y => ρ * φ q y
  let c : List P → Z → ℂ := fun ws =>
    normalizedExternalJet ψ (fun _ _ => (1 : ℂ)) ws.length ws.get p
  let g : List P → Z → F := fun ws y => parameterListJet (fun q => u q y) ws p
  let T : (List P × List P) → Z → F := fun s y => c s.1 y • g s.2 y
  let B : ℝ := ∑ a ∈ Finset.range (j + 1), ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * externalJetBudget H (fun m => if m = 0 then 1 else 0) a i *
      Q (j - a) (k - i)
  have hψ : ContDiffOn ℝ ∞ (Function.uncurry ψ) (V ×ˢ U) := contDiffOn_const.mul hφ
  have hc (ws : List P) : ContDiffOn ℝ ∞ (c ws) U :=
    contDiffOn_normalizedExternalJet_source hV hU hψ contDiffOn_const _ _ hp
  have hg (ws : List P) : ContDiffOn ℝ ∞ (g ws) U :=
    contDiffOn_originalExternalJet_source hV hU hu _ _ hp
  have he : normalizedExternalJet ψ u j v p =ᶠ[𝓝 z]
      fun y => ((parameterLeibnizSplittings (List.ofFn v)).map (fun s => T s y)).sum := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact normalizedExternalJet_eq_scalar_leibniz hV y
      (hψ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hq => ⟨hq, hy⟩))
      (hu.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hq => ⟨hq, hy⟩)) j v hp
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  apply (norm_iteratedFDeriv_list_sum_le _ T
    (fun s _ => ((hc s.1).smul (hg s.2)).contDiffAt (hU.mem_nhds hz)) k).trans
  have hterm (s : List P × List P) (hs : s ∈ parameterLeibnizSplittings (List.ofFn v)) :
      ‖iteratedFDeriv ℝ k (T s) z‖ ≤ B * (A * ρ ^ j * K ^ (b + j)) * K ^ k := by
    have horder := parameterLeibnizSplittings_orders hs
    rw [List.length_ofFn] at horder
    have hdirs := parameterLeibnizSplittings_directions hs
    have hvs : ∀ w ∈ List.ofFn v, ‖w‖ ≤ 1 := by simpa using hv
    have h1 : ∀ i, ‖s.1.get i‖ ≤ 1 :=
      fun i => hvs _ (hdirs.1 _ (List.get_mem ..))
    have h2 : ∀ i, ‖s.2.get i‖ ≤ 1 :=
      fun i => hvs _ (hdirs.2 _ (List.get_mem ..))
    have hprod := norm_iteratedFDerivWithin_smul_le (hc s.1) (hg s.2)
      hU.uniqueDiffOn hz (n := k) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hU hz] at hprod
    apply hprod.trans
    have hbranch :
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (c s.1) z‖ * ‖iteratedFDeriv ℝ (k - i) (g s.2) z‖) ≤
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          externalJetBudget H (fun m => if m = 0 then 1 else 0) s.1.length i *
            Q s.2.length (k - i)) * (A * ρ ^ j * K ^ (b + j)) * K ^ k := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
      have hscalar := norm_normalizedExternalJet_source_le hV hU hφ
        (u := fun _ _ => (1 : ℂ)) contDiffOn_const
        H (fun m => if m = 0 then 1 else 0) hH (fun m => by split_ifs <;> positivity)
        hK (A := 1) zero_le_one hρ s.1.length s.1.get h1 hp hz i
        (fun m hm => hphase m (by omega))
        (fun m _ => by cases m <;> simp [Function.uncurry_def, iteratedFDeriv_succ_const])
      have hamp := hamplitude s.2.length (by omega) s.2.get h2 (k - i) (by omega)
      have hQi := hQ s.2.length (k - i)
      have hE := externalJetBudget_nonneg hH
        (fun m => show 0 ≤ (if m = 0 then (1 : ℝ) else 0) by split_ifs <;> positivity)
        s.1.length i
      have hpower : ρ ^ s.1.length ≤ ρ ^ j := pow_le_pow_right₀ hρ (by omega)
      calc
        _ ≤ (k.choose i : ℝ) *
            (externalJetBudget H (fun m => if m = 0 then 1 else 0) s.1.length i *
              (1 * ρ ^ s.1.length * K ^ s.1.length) * K ^ i) *
            (Q s.2.length (k - i) * A * K ^ (b + s.2.length) * K ^ (k - i)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg _)) hamp
            (norm_nonneg _) (by positivity)
        _ = ((k.choose i : ℝ) *
            externalJetBudget H (fun m => if m = 0 then 1 else 0) s.1.length i *
              Q s.2.length (k - i) * A * K ^ (b + j) * K ^ k) * ρ ^ s.1.length := by
          have hexp : s.1.length + i + (b + s.2.length) + (k - i) = b + j + k := by omega
          calc
            _ = ((k.choose i : ℝ) *
                externalJetBudget H (fun m => if m = 0 then 1 else 0) s.1.length i *
                  Q s.2.length (k - i) * A) *
                K ^ (s.1.length + i + (b + s.2.length) + (k - i)) * ρ ^ s.1.length := by
              simp only [pow_add]; ring
            _ = _ := by rw [hexp, pow_add]; ring
        _ ≤ ((k.choose i : ℝ) *
            externalJetBudget H (fun m => if m = 0 then 1 else 0) s.1.length i *
              Q s.2.length (k - i) * A * K ^ (b + j) * K ^ k) * ρ ^ j :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring
    apply hbranch.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have heq : s.2.length = j - s.1.length := by omega
    rw [heq]
    dsimp only [B]
    apply Finset.single_le_sum (a := s.1.length)
      (f := fun a => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        externalJetBudget H (fun m => if m = 0 then 1 else 0) a i * Q (j - a) (k - i)) _
      (Finset.mem_range_succ_iff.mpr (show s.1.length ≤ j by omega))
    intro a _
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (externalJetBudget_nonneg hH
        (fun m => by split_ifs <;> positivity) a i)) (hQ _ _)
  calc
    _ ≤ ((parameterLeibnizSplittings (List.ofFn v)).map
        (fun _ => B * (A * ρ ^ j * K ^ (b + j)) * K ^ k)).sum := List.sum_le_sum hterm
    _ = _ := by
      simp [List.map_const', parameterLeibnizSplittings_length, nsmul_eq_mul,
        mixedExternalJetBudget, B, mul_assoc]

/-- The mixed source bound holds everywhere, with original profiles required
only on the common closed support and original smoothness only on its open
neighborhood. This supplies the pointwise source profile for the parent's
`norm_annularSourceIntegral_le` assembly.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_normalizedExternalJet_source_le_mixed_of_support
    {V : Set P} {U S : Set Z} (hV : IsOpen V) (hU : IsOpen U)
    (hS : IsClosed S) (hSU : S ⊆ U)
    {φ : P → Z → ℝ} {u : P → Z → F}
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ U))
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (V ×ˢ U))
    (hs : ∀ q ∈ V, tsupport (u q) ⊆ S)
    (H : ℕ → ℝ) (Q : ℕ → ℕ → ℝ)
    (hH : ∀ m, 0 ≤ H m) (hQ : ∀ l q, 0 ≤ Q l q)
    {K A ρ : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hρ : 1 ≤ ρ)
    (b j : ℕ) (v : Fin j → P) (hv : ∀ i, ‖v i‖ ≤ 1)
    {p : P} (hp : p ∈ V) (k : ℕ)
    (hphase : ∀ z ∈ S, ∀ m ≤ k + j,
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (p, z)‖ ≤ H m * K ^ m)
    (hamplitude : ∀ z ∈ S, ∀ l ≤ j, ∀ w : Fin l → P,
      (∀ i, ‖w i‖ ≤ 1) → ∀ q ≤ k,
      ‖iteratedFDeriv ℝ q (fun y => iteratedFDeriv ℝ l (fun a => u a y) p w) z‖ ≤
        Q l q * A * K ^ (b + l) * K ^ q)
    (z : Z) :
    ‖iteratedFDeriv ℝ k (normalizedExternalJet (fun q y => ρ * φ q y) u j v p) z‖ ≤
      mixedExternalJetBudget H Q j k * (A * ρ ^ j * K ^ (b + j)) * K ^ k := by
  by_cases hz : z ∈ S
  · exact norm_normalizedExternalJet_source_le_mixed hV hU hφ hu H Q hH hQ hK hA hρ
      b j v hv hp (hSU hz) k (hphase z hz) (hamplitude z hz)
  · have he : iteratedFDeriv ℝ k
        (normalizedExternalJet (fun q y => ρ * φ q y) u j v p) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz
        (tsupport_iteratedFDeriv_normalizedExternalJet_subset hV hS _ u hs j v hp k h))
    rw [he, norm_zero]
    have hD := mixedExternalJetBudget_nonneg hH hQ j k
    positivity

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets
