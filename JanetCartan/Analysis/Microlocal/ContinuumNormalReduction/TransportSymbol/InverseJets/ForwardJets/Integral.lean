module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.ForwardJets.Differential
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.AveragedGradient.Integral
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InverseJetInduction.Bounds
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-! # Joint transport jets through the actual interval integral

The derivative loss in `app:ch_background:eq:bg-Psi` is one mixed derivative
of `Y`. These estimates supply the primitive forward input to
`exists_inverseCoordinates_fixedShift_bound`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- A fixed coefficient for the joint integrand jets. Only the coordinate
projection, never the varying geometry, enters this constant
(`app:ch_background:eq:bg-mixed-input`). -/
def transportIntegrandJetConstant (K : Set (InputVariables n)) (m k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * 3 ^ m * cNorm K m (fun p : InputVariables n ↦ p.2.2)

/-- Nonnegativity of the fixed jet coefficient (`app:ch_background:eq:bg-Psi`). -/
theorem transportIntegrandJetConstant_nonneg (K : Set (InputVariables n)) (m k : ℕ) :
    0 ≤ transportIntegrandJetConstant K m k := by
  exact mul_nonneg (by positivity) (cNorm_nonneg _ _ _)

/-- All mixed integrand jets are linear in one primitive high norm of `Y`.
The compact set `K` bounds the covector coordinate, and `L` covers all segment
evaluations (`app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-mixed-input`). -/
theorem norm_iteratedFDeriv_transportSegmentGradient_le
    {U K : Set (InputVariables n)} (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    (hY : ContDiffOn ℝ ∞ Y V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hseg : MapsTo (transportSegmentInput n t) U L)
    {m k : ℕ} (hk : k ≤ m) {p : InputVariables n} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ k (transportSegmentGradient Y t) p‖ ≤
      transportIntegrandJetConstant K m k * cNorm L (m + 1) Y := by
  let A := transportSegmentInput n t
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ Y) V := hY.fderiv_of_isOpen hV (by simp)
  have hf : ContDiffOn ℝ ∞ (fderiv ℝ Y ∘ A) U :=
    hd.comp A.contDiff.contDiffOn (fun q hq ↦ hLV (hseg hq))
  have hbound (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (fderiv ℝ Y ∘ A) p‖ ≤ 3 ^ m * cNorm L (m + 1) Y := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ i (fderiv ℝ Y) (A p)‖ * ‖A‖ ^ i :=
        NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le A hV hd
          (hLV (hseg hp)) i
      _ = ‖iteratedFDeriv ℝ (i + 1) Y (A p)‖ * ‖A‖ ^ i := by
        rw [norm_iteratedFDeriv_fderiv]
      _ ≤ cNorm L (m + 1) Y * (3 : ℝ) ^ m := by
        apply mul_le_mul
        · exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
            (fun z hz ↦ (hY.contDiffAt (hV.mem_nhds (hLV hz))).of_le (by simp))
            (hseg hp) (by omega)
        · exact (pow_le_pow_left₀ (norm_nonneg A) (norm_transportSegmentInput_le n ht) i).trans
            (pow_le_pow_right₀ (by norm_num) (hi.trans hk))
        · positivity
        · exact cNorm_nonneg _ _ _
      _ = _ := mul_comm _ _
  have hb := NormalComparison.InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
    (transportSpatialAdjoint n) (norm_transportSpatialAdjoint_le n) hU hf
    (contDiff_snd.snd.contDiffOn) (mul_nonneg (by positivity) (cNorm_nonneg _ _ _)) hp k
    hbound (fun i hi ↦ norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK
      (fun _ _ ↦ contDiffAt_snd.snd) (hUK hp) (hi.trans hk))
  exact hb.trans_eq (by dsimp [transportIntegrandJetConstant]; ring)

/-- Equality with the actual gradient integral; this is an identity proved
from differentiability of `Y`, not a forward-map hypothesis
(`app:ch_background:eq:bg-Psi`). -/
theorem transportAveragedGradient_eq_integral_segment
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    (p : InputVariables n)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ Y (transportSegmentInput n t p)) :
    transportAveragedGradient Y p = ∫ t in (0 : ℝ)..1, transportSegmentGradient Y t p := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact (transportSpatialAdjoint_fderiv (hY t (by simpa using ht)) p.2.2).symm

/-- Joint smoothness of the literal averaged gradient. The open interval `T`
is a buffer of the integration interval; its only input is containment in the
primitive smooth domain (`app:ch_background:eq:bg-Psi`). -/
theorem transportAveragedGradient_contDiffOn
    {U : Set (InputVariables n)} (hU : IsOpen U)
    {V : Set (Euclidean n × (ℝ × Euclidean 2))} (hV : IsOpen V)
    {T : Set ℝ} (hT : IsOpen T) (hIT : Icc (0 : ℝ) 1 ⊆ T)
    (hseg : ∀ t ∈ T, MapsTo (transportSegmentInput n t) U V)
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    (hY : ContDiffOn ℝ ∞ Y V) : ContDiffOn ℝ ∞ (transportAveragedGradient Y) U := by
  have hH : ContDiffOn ℝ ∞ (fun z : InputVariables n × ℝ ↦
      transportSegmentGradient Y z.2 z.1) (U ×ˢ T) := by
    intro z hz
    exact ((transportSegmentGradient_contDiffAt (z := (z.2, z.1))
      (hY.contDiffAt (hV.mem_nhds (hseg z.2 hz.2 hz.1)))).comp z
        (contDiffAt_snd.prodMk contDiffAt_fst)).contDiffWithinAt
  apply (contDiffOn_unitIntervalParameterIntegral hU hT hIT hH).congr
  intro p hp
  exact transportAveragedGradient_eq_integral_segment p (fun t ht ↦
    (hY.contDiffAt (hV.mem_nhds (hseg t (hIT ht) hp))).differentiableAt (by simp))

/-- Quantitative mixed derivatives pass through the literal unit interval
integral (`app:ch_background:eq:bg-Psi`). No integral-jet bounds are assumed. -/
theorem norm_iteratedFDeriv_transportAveragedGradient_le
    {U K : Set (InputVariables n)} (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) U L)
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    (hY : ContDiffOn ℝ ∞ Y V) {m k : ℕ} (hk : k ≤ m)
    {p : InputVariables n} (hp : p ∈ U) :
    ‖iteratedFDeriv ℝ k (transportAveragedGradient Y) p‖ ≤
      transportIntegrandJetConstant K m k * cNorm L (m + 1) Y := by
  have heq : transportAveragedGradient Y =ᶠ[𝓝 p]
      (fun q ↦ ∫ t in (0 : ℝ)..1, transportSegmentGradient Y t q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact transportAveragedGradient_eq_integral_segment q (fun t ht ↦
      (hY.contDiffAt (hV.mem_nhds (hLV (hseg t ht hq)))).differentiableAt (by simp))
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  apply NormalComparison.norm_iteratedFDeriv_unitIntervalIntegral_le hU
    (fun z hz ↦ transportSegmentGradient_contDiffAt
      (hY.contDiffAt (hV.mem_nhds (hLV (hseg z.1 hz.1 hz.2))))) _ hp
  intro j hj t ht q hq
  exact norm_iteratedFDeriv_transportSegmentGradient_le hU hK hUK hV hL hLV hY ht
    (hseg t ht) (hj.trans hk) hq

/-- The compact-domain mixed seminorm of the literal forward gradient has
exactly one derivative of loss (`app:ch_background:eq:bg-mixed-input`). -/
theorem cNorm_transportAveragedGradient_le
    {S U K : Set (InputVariables n)} (hSU : S ⊆ U)
    (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) U L)
    {Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    (hY : ContDiffOn ℝ ∞ Y V) (m : ℕ) :
    cNorm S m (transportAveragedGradient Y) ≤
      (∑ j ∈ Finset.range (m + 1), transportIntegrandJetConstant K m j) *
        cNorm L (m + 1) Y := by
  rw [Finset.sum_mul]
  exact cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (transportIntegrandJetConstant_nonneg K m j) (cNorm_nonneg _ _ _))
    (fun j hj p hp ↦ norm_iteratedFDeriv_transportAveragedGradient_le
      hU hK hUK hV hL hLV hseg hY hj (hSU hp))

end JanetCartan.ContinuumNormalReduction.TransportSymbol
