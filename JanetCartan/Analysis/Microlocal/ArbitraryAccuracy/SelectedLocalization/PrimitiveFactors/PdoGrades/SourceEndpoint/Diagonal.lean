module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.Basic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds.Diagonal

/-!
# Joint and physical endpoint diagonal jets

Transfer the retained two-time order seminorm through the literal diagonal.
The shell radius and source frequency are distinct. Both time slots and all
covariable derivatives are retained. These are amplitude-factor estimates;
the coefficient, multiplier and physical masks must still be multiplied in
before obtaining the endpoint PDO grade of `CompleteFactor`.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
and `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector.Characteristic RegularSector.Characteristic.EndpointPdoBounds
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral.PrimitiveProfiles
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => FiniteChain.Graph.JointVariables E
local notation "T" => SymbolBudgets.TwoTimePoint d

/-- Joint diagonal insertion for the endpoint in
`app:ch_regular_base:eq:energy-complete-residual`. Both time slots and the
normalized covector vary inside the same linear map. -/
def endpointJointDiagonal (a : ℝ) : V →L[ℝ] T :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ ((v.1.1 0, v.1.1 0, spatialPart v.1.1), a • spatialPart v.2.1)
      map_add' := by intro v w; ext <;> simp [spatialPart, mul_add]
      map_smul' := by intro t v; ext <;> simp [spatialPart, mul_left_comm] }

/-- The diagonal repeats time without a derivative loss. Changing the shell
scale costs only the frequency dilation (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_endpointJointDiagonal_le (a : ℝ) :
    ‖endpointJointDiagonal (d := d) a‖ ≤ max 1 |a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hx : ‖v.1.1‖ ≤ ‖v‖ := (norm_fst_le v.1).trans (norm_fst_le v)
  have hξ : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have hbase : ‖v‖ ≤ max 1 |a| * ‖v‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
  change max (max |v.1.1 0| (max |v.1.1 0| ‖spatialPart v.1.1‖))
    ‖a • spatialPart v.2.1‖ ≤ _
  apply max_le
  · have ht := (PiLp.norm_apply_le v.1.1 0).trans hx
    exact (max_le ht (max_le ht ((norm_spatialPart_le _).trans hx))).trans hbase
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (le_max_right _ _) ((norm_spatialPart_le _).trans hξ)
      (norm_nonneg _) (by positivity)

private theorem normalizedAmplitude_jet_le
    {J : Set T} (hJ : IsCompact J)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    {o m : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (hb : BoundedTwoTimeOrderSeminorm o J m W) {w : T} (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ m (normalizedField R (jointAmplitude W)) w‖ ≤
      (R ^ o)⁻¹ * twoTimeOrderSeminorm o J m W := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hs : ContDiff ℝ ∞ (normalizedField R (jointAmplitude W)) :=
    hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))
  have hc : cNorm J m (twoTimeOrderField o R W) =
      R ^ o * cNorm J m (normalizedField R (jointAmplitude W)) := by
    exact (cNorm_smul (R ^ o) (hs.of_le (by simp))).trans
      (by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hRp.le _)])
  have hn := cNorm_twoTimeOrderField_le hb hR
  rw [hc] at hn
  exact (norm_iteratedFDeriv_le_cNorm hJ (hs.of_le (by simp)) hw le_rfl).trans
    ((le_inv_mul_iff₀ (pow_pos hRp o)).mpr hn)

/-- Transfer the retained JOINT amplitude seminorm to the endpoint's packed
variables. The shell radius `R` is independent of the source frequency `ρ`;
the geometric cover supplies the displayed normalized point. No covariable
derivative or diagonal time derivative is omitted. Consumer: the endpoint
symbol grade of `CompleteFactor` (`app:ch_regular:eq:high-amplitude`). -/
theorem norm_iteratedFDeriv_endpointJointDiagonal_le
    {J : Set T} (hJ : IsCompact J)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    {o m : ℕ} {R ρ : ℝ} (hR : 1 ≤ R)
    (hb : BoundedTwoTimeOrderSeminorm o J m W)
    {v : V} (hv : endpointJointDiagonal (ρ / R) v ∈ J) :
    ‖iteratedFDeriv ℝ m (fun w : V ↦
      W (w.1.1 0) (w.1.1 0) (spatialPart w.1.1) (spatialPart (ρ • w.2.1))) v‖ ≤
      (R ^ o)⁻¹ * twoTimeOrderSeminorm o J m W * (max 1 |ρ / R|) ^ m := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hs : ContDiff ℝ ∞ (normalizedField R (jointAmplitude W)) :=
    hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))
  have he : (fun w : V ↦
      W (w.1.1 0) (w.1.1 0) (spatialPart w.1.1) (spatialPart (ρ • w.2.1))) =
      normalizedField R (jointAmplitude W) ∘ endpointJointDiagonal (ρ / R) := by
    funext w
    simp [normalizedField, jointAmplitude, endpointJointDiagonal, spatialPart_smul,
      smul_smul, mul_div_cancel₀, hRp.ne']
  rw [he, (endpointJointDiagonal (ρ / R)).iteratedFDeriv_comp_right hs v (by simp)]
  apply ((iteratedFDeriv ℝ m (normalizedField R (jointAmplitude W))
    (endpointJointDiagonal (ρ / R) v)).norm_compContinuousLinearMap_le
      (fun _ ↦ endpointJointDiagonal (ρ / R))).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (normalizedAmplitude_jet_le hJ W hW hR hb hv)
    (pow_le_pow_left₀ (norm_nonneg _) (norm_endpointJointDiagonal_le _) m)
    (by positivity) (mul_nonneg (by positivity) (twoTimeOrderSeminorm_nonneg _ _ _ _))

/-- Physical endpoint jets retain the same order on any represented shell.
The affine pullback differentiates both diagonal time slots. Consumer: the
noncomparable endpoint symbol grade of `CompleteFactor`
(`app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_endpointPhysicalDiagonal_le
    {J : Set T} (hJ : IsCompact J)
    (W : TwoTimeAmplitude d q) (hW : ContDiff ℝ ∞ (jointAmplitude W))
    {o m : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (hb : BoundedTwoTimeOrderSeminorm o J m W)
    (η : Euclidean d) {z : E × E} (hz : diagonalPoint η z.1 ∈ J) :
    ‖iteratedFDeriv ℝ m (fun w : E × E ↦
      W (w.1 0) (w.1 0) (spatialPart w.1) (R • η)) z‖ ≤
      (R ^ o)⁻¹ * twoTimeOrderSeminorm o J m W := by
  let F := normalizedField R (jointAmplitude W)
  let P : E × E →L[ℝ] SymbolBudgets.TwoTimePoint d :=
    diagonalLinear.comp (ContinuousLinearMap.fst ℝ E E)
  have hT : ‖P‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact (mul_le_mul norm_diagonalLinear_le (ContinuousLinearMap.norm_fst_le ℝ E E)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hs : ContDiff ℝ ∞ F :=
    hW.comp (contDiff_fst.prodMk (contDiff_snd.const_smul R))
  have he : (fun w : E × E ↦
      W (w.1 0) (w.1 0) (spatialPart w.1) (R • η)) =
      fun w ↦ F (P w + ((0, 0, 0), η)) := by
    funext w
    simp [F, P, normalizedField, jointAmplitude, diagonalLinear]
  rw [he]
  apply (norm_iteratedFDeriv_preAffine_le P ((0, 0, 0), η) isOpen_univ
    hs.contDiffOn (mem_univ _) m).trans
  have hn := normalizedAmplitude_jet_le hJ W hW hR hb hz
  change ‖iteratedFDeriv ℝ m F (diagonalPoint η z.1)‖ * ‖P‖ ^ m ≤ _
  exact (mul_le_mul hn (pow_le_one₀ (norm_nonneg _) hT) (by positivity)
    (mul_nonneg (by positivity) (twoTimeOrderSeminorm_nonneg _ _ _ _))).trans_eq (mul_one _)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
