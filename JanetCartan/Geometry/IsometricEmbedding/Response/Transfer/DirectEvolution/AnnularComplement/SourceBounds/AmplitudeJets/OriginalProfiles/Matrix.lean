module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.AmplitudeJets.Products
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.Amplitude
public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.Masks
public import JanetCartan.Analysis.Microlocal.FourierIntegral.TransportSymbolBounds.OneHigh
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.OrderedSpatial

/-!
# Original elapsed matrix profiles at fixed physical frequency

The matrix input to `app:ch_response:lem:energy-carrier-jets` is produced
from the original joint two-time symbol, both original masks, beta and the
fixed selector. The elapsed pullback is a contraction. One shared Leibniz
budget gives `L^j`, including the literal conjugate transpose.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
open FourierIntegral RegularSector.Characteristic.EvolutionIntegral
open SymbolBudgets Complement.ParameterDerivatives.MixedGrades
variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "M" => Matrix (Fin r) (Fin r) ℂ

private theorem norm_smul_profile {D G : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
    [IsScalarTower ℝ ℂ G]
    {U : Set D} (hU : IsOpen U) {f : D → ℂ} {g : D → G}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : D} (hx : x ∈ U) {B C : ℕ → ℝ} (hB : ∀ i, 0 ≤ B i)
    {L : ℝ} (hL : 0 ≤ L) (k : ℕ)
    (hfb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i f x‖ ≤ B i * L ^ i)
    (hgb : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g x‖ ≤ C i * L ^ i) :
    ‖iteratedFDeriv ℝ k (fun y => f y • g y) x‖ ≤
      transportLeibnizBound B C k * L ^ k := by
  apply (norm_iteratedFDeriv_smul_on_open_le hU hf hg hx k).trans
  unfold transportLeibnizBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hik := Finset.mem_range_succ_iff.mp hi
  have hBi := hB i
  calc
    _ ≤ (k.choose i : ℝ) * (B i * L ^ i) * (C (k - i) * L ^ (k - i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfb i hik) (Nat.cast_nonneg _))
        (hgb (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = (k.choose i : ℝ) * B i * C (k - i) * L ^ (i + (k - i)) := by
      rw [pow_add]; ring
    _ = _ := by rw [Nat.add_sub_of_le hik]

/-- The linear part of the original elapsed substitution with physical
frequency held fixed (`app:ch_response:lem:energy-carrier-jets`). -/
def fixedFrequencyElapsedLinear (d : ℕ) :
    (Euclidean (d + 1) × Euclidean (d + 1)) →L[ℝ] TwoTimePoint d :=
  elapsedLinear.comp (ContinuousLinearMap.inl ℝ _ _)

/-- No derivative or scale loss in the actual elapsed pullback. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_fixedFrequencyElapsedLinear_le :
    ‖fixedFrequencyElapsedLinear d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖elapsedLinear (q, 0)‖ ≤ 1 * ‖q‖
  exact (elapsedLinear.le_opNorm _).trans (by
    simpa using mul_le_mul_of_nonneg_right norm_elapsedLinear_le
      (norm_nonneg (q, (0 : E))))

/-- Literal coordinates of the pullback; the lower time remains `x₀-t`.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem fixedFrequencyElapsedLinear_add (t : ℝ) (ξ : E) (q : E × E) :
    fixedFrequencyElapsedLinear d q + ((0, -t, 0), spatialPart ξ) =
      elapsedPoint t (q, ξ) := by
  simp [fixedFrequencyElapsedLinear, elapsedLinear, elapsedPoint_eq, sub_eq_add_neg]
  ext i
  rfl

/-- The actual matrix multiplying the original source, with the two
orientations in their original physical positions. It is used only to expose
the existing `annularExternalAmplitude`, not to replace that function.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
def originalAnnularMatrix (adjoint : Bool) (b : TwoTimeAmplitude d r)
    (χout χsource β π : E → ℂ) (t lam : ℝ) (ξ : E) (q : E × E) : M :=
  if adjoint then
    (annularComplementAmplitude π lam (elapsedAmplitude b χout χsource β t)
      q.2 q.1 ξ).conjTranspose
  else annularComplementAmplitude π lam (elapsedAmplitude b χout χsource β t)
    q.1 q.2 ξ

/-- Literal equality to the published vector amplitude, including matrix
action and the original envelope. Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem annularExternalAmplitude_eq_originalAnnularMatrix {C : Type}
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (a : C → E → EuclideanSpace ℂ (Fin r))
    (ξ : E) (p : C × E) (z : E) :
    annularExternalAmplitude adjoint (elapsedAmplitude b χout χsource β t)
      π lam a ξ p z =
        annularMatrixAction r (originalAnnularMatrix adjoint b χout χsource β π
          t lam ξ (p.2, z)) (a p.1 z) := by
  cases adjoint <;> rfl

/-- Uniform original matrix constants, chosen before frequency, elapsed time,
scales and the envelope in `app:ch_response:lem:energy-carrier-jets`. -/
def originalMatrixBudget (O S B : ℕ → ℝ) (Mβ Mπ : ℝ) (j : ℕ) : ℝ :=
  ((1 + Mπ) * Mβ) * transportLeibnizBound O (transportLeibnizBound S B) j

/-- Nonnegative original matrix profile. Source:
`app:ch_response:lem:energy-carrier-jets`. -/
theorem originalMatrixBudget_nonneg {O S B : ℕ → ℝ}
    (hO : ∀ i, 0 ≤ O i) (hS : ∀ i, 0 ≤ S i) (hB : ∀ i, 0 ≤ B i)
    {Mβ Mπ : ℝ} (hβ : 0 ≤ Mβ) (hπ : 0 ≤ Mπ) (j : ℕ) :
    0 ≤ originalMatrixBudget O S B Mβ Mπ j := by
  exact mul_nonneg (mul_nonneg (by positivity) hβ)
    (transportLeibnizBound_nonneg hO (transportLeibnizBound_nonneg hS hB) j)

/-- Original forward matrix jets from the original joint symbol profile.
The profile hypotheses concern only the unmodified symbol and masks. The
source and output positions are differentiated jointly; beta, the selector
and physical frequency remain fixed. The open set can be the original
buffered supported chart (`app:ch_response:lem:energy-carrier-jets`). -/
theorem norm_iteratedFDeriv_originalAnnularMatrix_forward_le
    (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {U : Set (TwoTimePoint d)} (hU : IsOpen U)
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) U)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {O S B : ℕ → ℝ} (hO : ∀ i, 0 ≤ O i) (hS : ∀ i, 0 ≤ S i)
    (_hB : ∀ i, 0 ≤ B i) {Mβ Mπ L : ℝ}
    (hβ : 0 ≤ Mβ) (hπ : 0 ≤ Mπ) (hL : 1 ≤ L)
    (hβξ : ‖β ξ‖ ≤ Mβ) (hπξ : ‖π (lam⁻¹ • ξ)‖ ≤ Mπ)
    (q : E × E) (hq : elapsedPoint t (q, ξ) ∈ U) (j : ℕ)
    (hout : ∀ i ≤ j, ‖iteratedFDeriv ℝ i χout q.1‖ ≤ O i)
    (hsource : ∀ i ≤ j, ‖iteratedFDeriv ℝ i χsource q.2‖ ≤ S i)
    (hsymbol : ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i (jointAmplitude b) (elapsedPoint t (q, ξ))‖ ≤ B i * L ^ i) :
    ‖iteratedFDeriv ℝ j (originalAnnularMatrix false b χout χsource β π t lam ξ) q‖ ≤
      originalMatrixBudget O S B Mβ Mπ j * L ^ j := by
  let a₀ : TwoTimePoint d := ((0, -t, 0), spatialPart ξ)
  let T := fixedFrequencyElapsedLinear d
  let W : Set (E × E) := (fun p => T p + a₀) ⁻¹' U
  have hW : IsOpen W := hU.preimage (T.continuous.add continuous_const)
  have hqW : q ∈ W := by simpa only [W, mem_preimage, T, a₀,
    fixedFrequencyElapsedLinear_add] using hq
  let g : E × E → M := fun p => jointAmplitude b (T p + a₀)
  have hg : ContDiffOn ℝ ∞ g W :=
    hb.comp (T.contDiff.contDiffOn.add contDiffOn_const) (fun _ hp => hp)
  have hgj (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i g q‖ ≤ B i * L ^ i := by
    have hh := norm_iteratedFDeriv_preAffine_le T a₀ hU hb hqW i
    apply hh.trans
    have hp : ‖T‖ ^ i ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) norm_fixedFrequencyElapsedLinear_le
    simpa only [mul_one, T, a₀, fixedFrequencyElapsedLinear_add] using
      (mul_le_mul_of_nonneg_left hp (norm_nonneg
        (iteratedFDeriv ℝ i (jointAmplitude b) (T q + a₀)))).trans
        (by simpa only [mul_one, T, a₀, fixedFrequencyElapsedLinear_add] using hsymbol i hi)
  have hL0 := zero_le_one.trans hL
  have hpull (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (A : ℕ → ℝ)
      (hA : ∀ i, 0 ≤ A i) (T₀ : (E × E) →L[ℝ] E) (hT₀ : ‖T₀‖ ≤ 1)
      (hfA : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f (T₀ q)‖ ≤ A i) (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (fun p => f (T₀ p)) q‖ ≤ A i * L ^ i := by
    have ht := norm_iteratedFDeriv_affine_contraction_le T₀ hT₀ 0 isOpen_univ
      hf.contDiffOn i (x := q) (mem_univ _)
    simp only [zero_add] at ht
    exact ht.trans ((hfA i hi).trans (le_mul_of_one_le_right (hA i) (one_le_pow₀ hL)))
  have hso := hpull χsource hs S hS (ContinuousLinearMap.snd ℝ E E)
    (ContinuousLinearMap.norm_snd_le _ _ _) hsource
  have hoo := hpull χout ho O hO (ContinuousLinearMap.fst ℝ E E)
    (ContinuousLinearMap.norm_fst_le _ _ _) hout
  have hinner (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (fun p : E × E => χsource p.2 • g p) q‖ ≤
        transportLeibnizBound S B i * L ^ i :=
    norm_smul_profile hW (hs.comp contDiff_snd).contDiffOn hg hqW hS hL0 i
      (fun k hk => hso k (hk.trans hi)) (fun k hk => hgj k (hk.trans hi))
  have hprod := norm_smul_profile hW (ho.comp contDiff_fst).contDiffOn
    ((hs.comp contDiff_snd).contDiffOn.smul hg) hqW hO hL0 j hoo hinner
  have he : originalAnnularMatrix false b χout χsource β π t lam ξ =
      fun p => ((1 - π (lam⁻¹ • ξ)) * β ξ) • (χout p.1 • (χsource p.2 • g p)) := by
    funext p
    simp only [originalAnnularMatrix, Bool.false_eq_true, ite_false,
      annularComplementAmplitude, frequencyCutFullAmplitude, elapsedAmplitude,
      g, T, a₀, fixedFrequencyElapsedLinear_add, jointAmplitude, elapsedPoint_eq,
      smul_smul]
    congr 1
    ring
  have hregular : ContDiffAt ℝ j
      (fun p : E × E => χout p.1 • (χsource p.2 • g p)) q :=
    (((ho.comp contDiff_fst).contDiffOn.smul
      ((hs.comp contDiff_snd).contDiffOn.smul hg)).contDiffAt
        (hW.mem_nhds hqW)).of_le (by simp)
  rw [he, iteratedFDeriv_const_smul_apply' hregular, norm_smul]
  have hscalar : ‖(1 - π (lam⁻¹ • ξ)) * β ξ‖ ≤ (1 + Mπ) * Mβ := by
    rw [norm_mul]
    apply mul_le_mul _ hβξ (norm_nonneg _) (by positivity)
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left hπξ 1)
  exact (mul_le_mul hscalar hprod (norm_nonneg _) (by positivity)).trans_eq (by
    simp only [originalMatrixBudget]; ring)

/-- Swapping the physical positions and taking the literal adjoint preserves
every matrix derivative norm. All mask and beta conjugations are included.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_originalAnnularMatrix_adjoint
    (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) (q : E × E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (originalAnnularMatrix true b χout χsource β π t lam ξ) q‖ =
      ‖iteratedFDeriv ℝ j (originalAnnularMatrix false b χout χsource β π t lam ξ)
        q.swap‖ := by
  change ‖iteratedFDeriv ℝ j (fun p : E × E =>
    (originalAnnularMatrix false b χout χsource β π t lam ξ p.swap).conjTranspose) q‖ = _
  rw [norm_iteratedFDeriv_transport_conjTranspose]
  exact (LinearIsometryEquiv.prodComm ℝ E E).norm_iteratedFDeriv_comp_right
    (originalAnnularMatrix false b χout χsource β π t lam ξ) q j

/-- Both orientations of the original elapsed matrix have the same profile.
The only symbol input is the original joint two-time symbol on its buffered
chart. No profile of the masked or adjointed amplitude is assumed.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_iteratedFDeriv_originalAnnularMatrix_le
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {U : Set (TwoTimePoint d)} (hU : IsOpen U)
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) U)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {O S B : ℕ → ℝ} (hO : ∀ i, 0 ≤ O i) (hS : ∀ i, 0 ≤ S i)
    (hB : ∀ i, 0 ≤ B i) {Mβ Mπ L : ℝ}
    (hβ : 0 ≤ Mβ) (hπ : 0 ≤ Mπ) (hL : 1 ≤ L)
    (hβξ : ‖β ξ‖ ≤ Mβ) (hπξ : ‖π (lam⁻¹ • ξ)‖ ≤ Mπ)
    (q : E × E) (j : ℕ)
    (hq : elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ U)
    (hout : ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i χout (if adjoint then q.2 else q.1)‖ ≤ O i)
    (hsource : ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i χsource (if adjoint then q.1 else q.2)‖ ≤ S i)
    (hsymbol : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (jointAmplitude b)
      (elapsedPoint t ((if adjoint then q.swap else q), ξ))‖ ≤ B i * L ^ i) :
    ‖iteratedFDeriv ℝ j (originalAnnularMatrix adjoint b χout χsource β π t lam ξ) q‖ ≤
      originalMatrixBudget O S B Mβ Mπ j * L ^ j := by
  cases adjoint with
  | false =>
    exact norm_iteratedFDeriv_originalAnnularMatrix_forward_le b χout χsource β π
      t lam ξ hU hb ho hs hO hS hB hβ hπ hL hβξ hπξ q hq j hout hsource hsymbol
  | true =>
    rw [norm_iteratedFDeriv_originalAnnularMatrix_adjoint]
    exact norm_iteratedFDeriv_originalAnnularMatrix_forward_le b χout χsource β π
      t lam ξ hU hb ho hs hO hS hB hβ hπ hL hβξ hπξ q.swap hq j hout hsource hsymbol

/-- Local smoothness on the original supported chart, with physical frequency
fixed. This does not require global smoothness of the symbol across zero
frequency or outside its chart (`app:ch_response:lem:energy-carrier-jets`). -/
theorem contDiffOn_originalAnnularMatrix
    (adjoint : Bool) (b : TwoTimeAmplitude d r) (χout χsource β π : E → ℂ)
    (t lam : ℝ) (ξ : E) {U : Set (TwoTimePoint d)} {W : Set (E × E)}
    (hb : ContDiffOn ℝ ∞ (jointAmplitude b) U)
    (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hmap : ∀ q ∈ W, elapsedPoint t ((if adjoint then q.swap else q), ξ) ∈ U) :
    ContDiffOn ℝ ∞ (originalAnnularMatrix adjoint b χout χsource β π t lam ξ) W := by
  have hforward {W₀ : Set (E × E)}
      (hm : ∀ q ∈ W₀, elapsedPoint t (q, ξ) ∈ U) :
      ContDiffOn ℝ ∞ (originalAnnularMatrix false b χout χsource β π t lam ξ) W₀ := by
    have hpoint : ContDiff ℝ ∞ (fun q : E × E => elapsedPoint t (q, ξ)) := by
      simp_rw [← fixedFrequencyElapsedLinear_add]
      exact (fixedFrequencyElapsedLinear d).contDiff.add contDiff_const
    have hg := hb.comp hpoint.contDiffOn hm
    have hh := (((ho.comp contDiff_fst).contDiffOn.mul
      (hs.comp contDiff_snd).contDiffOn).mul (contDiffOn_const (c := β ξ))).smul hg
    convert hh.const_smul (1 - π (lam⁻¹ • ξ)) using 1
    funext p
    simp [originalAnnularMatrix, annularComplementAmplitude, frequencyCutFullAmplitude,
      elapsedAmplitude, jointAmplitude, elapsedPoint_eq]
  cases adjoint with
  | false => exact hforward hmap
  | true =>
    have hswap := (hforward (W₀ := Prod.swap ⁻¹' W) (fun q hq => by
      simpa only [Bool.true_eq, ite_true, Prod.swap_swap] using hmap q.swap hq)).comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun q hq => by
        simpa using hq)
    exact (starL ℝ : M ≃L[ℝ] M).contDiff.comp_contDiffOn hswap

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement.AmplitudeJets.OriginalProfiles
