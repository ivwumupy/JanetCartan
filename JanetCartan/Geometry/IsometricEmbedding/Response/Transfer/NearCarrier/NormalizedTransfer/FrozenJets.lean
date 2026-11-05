module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.NormalizedTransfer.Parameter

/-!
# Frozen joint jets and the physical low symbol budget

Freezing the parameter is an affine map whose linear part has norm at most
one. It therefore spends no derivative order and introduces no frequency
factor. The scalar expression bound is converted to the published physical
full-source-symbol budget, retaining the Frobenius matrix norm.
Consumer: `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ResponseTransfer.NormalizedTransfer
open FourierIntegral FullAmplitudePrimitiveBudget.Local FullLowBounds SourceExpansion
open IsometricEmbedding.Response.NearCarrier NearCarrierParameter NearCarrierSymbol
variable {n p r : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "P" => Euclidean p
local notation "Z" => JointAmplitudePoint n p

/-- The linear part of parameter freezing in normalized coordinates.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
def frozenDirectionMap : Point n →L[ℝ] Z :=
  ((0 : Point n →L[ℝ] P).prod (ContinuousLinearMap.fst ℝ (E × E) E)).prod
    (ContinuousLinearMap.snd ℝ (E × E) E)

/-- Freezing costs no norm factor in the product norms used for joint jets.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_frozenDirectionMap_le : ‖frozenDirectionMap (n := n) (p := p)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp [frozenDirectionMap, Prod.norm_def]

/-- Exact frozen-slice chain rule for every joint derivative order. The
original parameter is a spectator, with no change of physical positions.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem iteratedFDeriv_frozenField (c : P) {b : Z → ℂ} (hb : ContDiff ℝ ∞ b)
    (j : ℕ) (z : Point n) :
    iteratedFDeriv ℝ j (frozenField c b) z =
      (iteratedFDeriv ℝ j b ((c, z.1), z.2)).compContinuousLinearMap
        (fun _ ↦ frozenDirectionMap) := by
  let s : Z := ((c, 0), 0)
  let g : Z → ℂ := fun w ↦ b (w + s)
  have hg : ContDiff ℝ ∞ g := hb.comp (contDiff_id.add contDiff_const)
  have he : frozenField c b = g ∘ frozenDirectionMap := by
    funext w
    simp [frozenField, g, s, frozenDirectionMap]
  rw [he, frozenDirectionMap.iteratedFDeriv_comp_right hg z (by simp)]
  simp [g, s, iteratedFDeriv_comp_add_right, frozenDirectionMap]

/-- Joint primitive jets control the frozen spatial jets without any loss of
order. This is the normalized input to the low symbol budget in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_iteratedFDeriv_frozenField_le (c : P) {b : Z → ℂ}
    (hb : ContDiff ℝ ∞ b) (j : ℕ) (z : Point n) :
    ‖iteratedFDeriv ℝ j (frozenField c b) z‖ ≤
      ‖iteratedFDeriv ℝ j b ((c, z.1), z.2)‖ := by
  rw [iteratedFDeriv_frozenField c hb]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
    (fun _ _ ↦ norm_frozenDirectionMap_le)

/-- Entrywise scalar recovery has the full physical symbol budget, derived
from its normalized jets and original selector support. The matrix insertion
norm is a fixed dimension constant. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasFullSourceSymbolBound_scalarPhysical
    {b : Point n → ℂ} (hb : ContDiff ℝ ∞ b)
    {ρ radius B : ℝ} (hρ : 1 ≤ ρ) (hradius : 0 ≤ radius) (hB : 0 ≤ B) (N : ℕ)
    (hs : ∀ z ∈ tsupport b, ‖z.2‖ ≤ radius)
    (hj : ∀ j ≤ N, ∀ z, ‖iteratedFDeriv ℝ j b z‖ ≤ B) :
    HasFullSourceSymbolBound (scalarPhysicalAmplitude (r := r) ρ b) N
      ((1 + radius) ^ N * (‖scalarMatrixMap (r := r)‖ * B)) := by
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  apply hasFullSourceSymbolBound_of_normalized_jets (contDiff_scalarPhysicalAmplitude ρ hb)
    hρ hradius (mul_nonneg (norm_nonneg _) hB) N
  · apply support_physicalAmplitudeOfNormalized hρpos
    intro z hz
    exact hs z (tsupport_comp_subset (map_zero scalarMatrixMap) b hz)
  · intro j hjN z
    rw [scalarPhysicalAmplitude, normalizedField_physicalAmplitudeOfNormalized hρpos.ne']
    exact (ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (G := Matrix (Fin r) (Fin r) ℂ) scalarMatrixMap hb.contDiffAt (by simp)).trans
        (mul_le_mul_of_nonneg_left (hj j hjN z) (norm_nonneg _))

/-- The low physical budget of a frozen joint expression follows from the
primitive total-order reserve and original compact supports. No transfer
identity or modified-amplitude estimate is assumed. Consumer:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem hasFullSourceSymbolBound_frozen_expression
    (a : ι → Z → ℂ) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (e : AmplitudeExpression Z ℂ ι)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (c₀ R k : ℕ) (hR : c₀ + 2 < R) (hcost : e.derivativeCost ≤ k)
    {L ρ radius : ℝ} (hL : 1 ≤ L) (hρ : 1 ≤ ρ) (hradius : 0 ≤ radius)
    (hj : ∀ i j, j ≤ c₀ + k → ∀ z,
      ‖iteratedFDeriv ℝ j (a i) z‖ ≤ M i j * L ^ (j + 2 - R))
    {U : Set P} {X Y F : Set E}
    (hX : IsCompact X) (hY : IsCompact Y) (hF : IsCompact F)
    (hb : ParameterAmplitudeAdmissible U X Y F (e.evaluate a))
    (hFradius : ∀ ε ∈ F, ‖ε‖ ≤ radius) {c : P} (hc : c ∈ U) :
    HasFullSourceSymbolBound
      (scalarPhysicalAmplitude (r := r) ρ (frozenField c (e.evaluate a))) c₀
      (((1 + radius) ^ c₀ * (‖scalarMatrixMap (r := r)‖ * e.lowJetConstant M c₀)) * L ^ k) := by
  rw [mul_assoc, mul_assoc]
  apply hasFullSourceSymbolBound_scalarPhysical (contDiff_frozenField hb.1 hc)
    hρ hradius (mul_nonneg (e.lowJetConstant_nonneg M hM c₀)
      (pow_nonneg (zero_le_one.trans hL) _)) c₀
  · intro z hz
    exact hFradius z.2 ((supportedAmplitude_frozenField hX hY hF hb hc).2 hz).2
  · intro j hjc z
    exact (norm_iteratedFDeriv_frozenField_le c (e.contDiff_evaluate a ha) j z).trans
      (e.norm_lowJet_evaluate_le M hM c₀ R k hR hcost L hL a ha hj j hjc _)

end JanetCartan.ResponseTransfer.NormalizedTransfer
