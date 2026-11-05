module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.PhaseExtension

/-!
# Sobolev estimates on a buffered supported phase chart

The graph amplitudes used by the finite calculus are supported in a closed
physical/frequency carrier.  All phase differentiations, homogeneity trades,
and mixed inverse coefficients are therefore needed only on an open buffered
neighborhood of that carrier.  This file records the support-local closure
lemmas used by the supported Sobolev assembly.  The phase is kept
in the original `(x,y,η)` coordinates throughout; no globally homogeneous or
nondegenerate extension is introduced.
-/

@[expose] public noncomputable section
open MeasureTheory Filter JanetCartan.Pseudodifferential
open LineDeriv
open scoped ContDiff Topology Matrix.Norms.Frobenius SchwartzMap
namespace JanetCartan.FourierIntegral

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)
open FullAmplitudePrimitiveBudget FullAmplitudePrimitiveBudget.Local
open FirstOutputJets PrimitiveProfiles

/-- A buffered chart contains the closed support of a full amplitude. -/
def SupportedCarrier (U : Set (Point n)) (K : Set (E × E)) (F : Set E) : Prop :=
  IsOpen U ∧ K ×ˢ F ⊆ U

/-- Local phase regularity on a buffered supported chart. -/
def SupportedPhaseRegularity (S : E → E → ℝ) (U : Set (Point n)) : Prop :=
  ∀ p ∈ U, p.2 ≠ 0 → ContDiffAt ℝ ∞ (Function.uncurry S) (p.1.1, p.2)

/-- Local degree-one homogeneity on the buffered supported chart. -/
def SupportedPhaseHomogeneity (S : E → E → ℝ) (U : Set (Point n)) : Prop :=
  ∀ p ∈ U, p.2 ≠ 0 → ∀ᶠ t : ℝ in 𝓝 1,
    (fun z ↦ S z (t • p.2)) =ᶠ[𝓝 p.1.1] (fun z ↦ t * S z p.2)

/-- Local mixed invertibility on the buffered supported chart. -/
def SupportedMixedInvertibility (S : E → E → ℝ) (U : Set (Point n)) : Prop :=
  ∀ p ∈ U, IsUnit (mixedPhaseMatrix S p.1.1 p.2).det

/-- Local smoothness of a forward transfer datum.  Outside the closed support
of the input amplitude the branch is eventually zero, so no phase regularity
outside the buffered chart is used. -/
theorem ForwardAmplitudeAdmissible.graphTransferDatum_of_supported
    {X Y F : Set E} {U : Set (Point n)} {A : FullAmplitude n r}
    (S : E → E → ℝ)
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F)
    (hF0 : (0 : E) ∉ F) (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U)
    (hphase : SupportedPhaseRegularity (S := S) U)
    (i j : Fin n) :
    ForwardAmplitudeAdmissible X Y F (FourierIntegral.graphTransferDatum S i j A) := by
  refine ⟨contDiff_iff_contDiffAt.mpr (fun p ↦ ?_), ?_⟩
  · by_cases hx : p.1 ∈ X
    · by_cases hy : p.2.1 ∈ Y
      · by_cases hη : p.2.2 ∈ F
        · have hη0 : p.2.2 ≠ 0 := fun hz ↦ hF0 (hz ▸ hη)
          have hsp := hphase ((p.1, p.2.1), p.2.2)
            (hcarrier ⟨⟨hx, hy⟩, hη⟩) hη0
          exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
            ((ForwardRegularized.smoothAt_mixedPhaseEntry hsp i j).comp p
              (contDiffAt_fst.prodMk contDiffAt_snd.snd))).smul hA.smooth.contDiffAt
        · apply (contDiffAt_const (c := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
          filter_upwards [(continuous_snd.snd.isOpen_preimage _ hF.isOpen_compl).mem_nhds hη] with q hq
          simp [FourierIntegral.graphTransferDatum, hA.support q.1 q.2.1 q.2.2
            (Or.inr (Or.inr hq))]
      · apply (contDiffAt_const (c := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
        filter_upwards [(continuous_snd.fst.isOpen_preimage _ hY.isOpen_compl).mem_nhds hy] with q hq
        simp [FourierIntegral.graphTransferDatum, hA.support q.1 q.2.1 q.2.2
          (Or.inr (Or.inl hq))]
    · apply (contDiffAt_const (c := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
      filter_upwards [(continuous_fst.isOpen_preimage _ hX.isOpen_compl).mem_nhds hx] with q hq
      simp [FourierIntegral.graphTransferDatum, hA.support q.1 q.2.1 q.2.2
        (Or.inl hq)]
  · intro x y η h
    simp [FourierIntegral.graphTransferDatum, hA.support x y η h]

/-- Local smoothness of a forward transfer remainder. -/
theorem ForwardAmplitudeAdmissible.graphTransferRemainder_of_supported
    {X Y F : Set E} {U : Set (Point n)} {A : FullAmplitude n r}
    (S : E → E → ℝ)
    (hA : ForwardAmplitudeAdmissible X Y F A)
    (hX : IsClosed X) (hY : IsClosed Y) (hF : IsClosed F)
    (hF0 : (0 : E) ∉ F) (hcarrier : (X ×ˢ Y) ×ˢ F ⊆ U)
    (hphase : SupportedPhaseRegularity (S := S) U)
    (i : Fin n) :
    ForwardAmplitudeAdmissible X Y F (FourierIntegral.graphTransferRemainder S i A) := by
  have hx := hA.outputPartial hX i
  have hy (j) := ForwardAmplitudeAdmissible.graphTransferDatum_of_supported S
    (hA.sourcePartial hY j) hX hY hF hF0 hcarrier hphase i j
  refine ⟨hx.smooth.add (ContDiff.sum (fun j _ ↦ (hy j).smooth)), ?_⟩
  intro x y η h
  change _ + ∑ j, FourierIntegral.graphTransferDatum S i j
    (fun x y η ↦ partialDeriv (fun z ↦ A x z η) y j) x y η = 0
  rw [hx.support x y η h]
  simp only [(hy _).support x y η h, Finset.sum_const_zero, add_zero]

/-- Local smoothness and support closure for a reverse datum branch. -/
theorem ReverseAmplitudeAdmissible.adjointTransferDatum_of_supported
    {K : Set (E × E)} {F : Set E} {U : Set (Point n)} {C : FullAmplitude n r}
    (S : E → E → ℝ)
    (hC : ReverseAmplitudeAdmissible K C)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (hF : IsClosed F) (_hF0 : (0 : E) ∉ F)
    (hcarrier : K ×ˢ F ⊆ U)
    (hphase : SupportedPhaseRegularity (S := S) U)
    (hinv : SupportedMixedInvertibility (S := S) U)
    (i j : Fin n) :
    ReverseAmplitudeAdmissible K (FourierIntegral.adjointTransferDatum S i j C) := by
  refine ⟨?_, (tsupport_adjointTransferDatum_subset S C i j).trans hC.support⟩
  intro p hη
  by_cases hp : p ∈ tsupport (fun q : Point n ↦ C q.1.1 q.1.2 q.2)
  · have hpF : p.2 ∈ F := by
      by_contra hz
      have heq : (fun q : Point n ↦ C q.1.1 q.1.2 q.2) =ᶠ[𝓝 p] (fun _ ↦ 0) := by
        filter_upwards [(continuous_snd.isOpen_preimage _ hF.isOpen_compl).mem_nhds hz] with q hq
        exact hfreq q.1.1 q.1.2 q.2 hq
      exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hp
    have hU : p ∈ U := hcarrier ⟨hC.support hp, hpF⟩
    have hi := contDiffAt_mixedPhaseMatrix_inverse_of_phase S (p.1.1, p.2)
      (hphase p hU hη) (hinv p hU)
    let ev : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
          (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i))
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (ev.contDiff.contDiffAt.comp p (hi.comp p
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)))).smul (hC.smooth p hη)
  · apply (contDiffAt_const (c := (0 : Matrix (Fin r) (Fin r) ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    simp [hq, FourierIntegral.adjointTransferDatum]

/-- Local smoothness and support closure for the complete reverse remainder. -/
theorem ReverseAmplitudeAdmissible.adjointTransferRemainder_of_supported
    {K : Set (E × E)} {F : Set E} {U : Set (Point n)} {C : FullAmplitude n r}
    (S : E → E → ℝ)
    (hC : ReverseAmplitudeAdmissible K C)
    (hfreq : ∀ x y η, η ∉ F → C x y η = 0)
    (hF : IsClosed F) (_hF0 : (0 : E) ∉ F)
    (hcarrier : K ×ˢ F ⊆ U)
    (hphase : SupportedPhaseRegularity (S := S) U)
    (hinv : SupportedMixedInvertibility (S := S) U)
    (i : Fin n) :
    ReverseAmplitudeAdmissible K (FourierIntegral.adjointTransferRemainder S i C) := by
  refine ⟨?_, (tsupport_adjointTransferRemainder_subset S C i).trans hC.support⟩
  intro p hη
  have hsource (B : FullAmplitude n r) (p : Point n) (hp : ContDiffAt ℝ ∞
      (fun q : Point n ↦ B q.1.1 q.1.2 q.2) p) (j : Fin n) :
      ContDiffAt ℝ ∞ (fun q : Point n ↦
        partialDeriv (fun x ↦ B x q.1.2 q.2) q.1.1 j) p := by
    have hh := hp.comp (p, p.1.1)
      ((contDiffAt_snd.prodMk contDiffAt_fst.fst.snd).prodMk contDiffAt_fst.snd)
    exact (hh.fderiv contDiffAt_fst.fst (by simp)).clm_apply contDiffAt_const
  have houtput (p : Point n) (hp : ContDiffAt ℝ ∞
      (fun q : Point n ↦ C q.1.1 q.1.2 q.2) p) (j : Fin n) :
      ContDiffAt ℝ ∞ (fun q : Point n ↦
        partialDeriv (fun y ↦ C q.1.1 y q.2) q.1.2 j) p := by
    have hh := hp.comp (p, p.1.2)
      ((contDiffAt_fst.fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
    exact (hh.fderiv contDiffAt_fst.snd (by simp)).clm_apply contDiffAt_const
  exact houtput p (hC.smooth p hη) i |>.add
    (ContDiffAt.sum fun j _ ↦ hsource (FourierIntegral.adjointTransferDatum S i j C) p
      ((ReverseAmplitudeAdmissible.adjointTransferDatum_of_supported S hC hfreq hF _hF0 hcarrier hphase hinv i j).smooth p hη) j)

end JanetCartan.FourierIntegral

namespace JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
open JanetCartan.FourierIntegral
open JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget
open Weighted
variable {n r : ℕ} {S : Euclidean n → Euclidean n → ℝ} {A : FullAmplitude n r}

/-- Forward branch bounds with primitive regularity supplied only on an open
buffer containing the closed amplitude carrier. -/
theorem graph_branch_jet_norm_le_of_supported
    {K : Set (Euclidean n × Euclidean n)} {F : Set (Euclidean n)}
    {U : Set (Point n)} (hU : IsOpen U)
    (hcarrier : K ×ˢ F ⊆ U)
    (hreg : SmoothPrimitivesOn S A U)
    (hsupp : tsupport (uncurry A) ⊆ K ×ˢ F)
    (ρ : Euclidean n → ℝ) (hρ : ∀ η, 0 ≤ ρ η)
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s : ℕ)
    (L Kc H : ℝ) (hL : 1 ≤ L) (hKc : 1 ≤ Kc) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ Kc * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (is : List (Fin n)) (his : is.length ≤ s)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (graphTransferRemainder S)
      (graphTransferDatum S) A is)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) (x y η : Euclidean n)
    (hAmp : ∀ p ∈ K ×ˢ F, ∀ v,
      (ρ p.2) ^ FirstOutputJets.frequencyOrder v * ‖uncurry (jet v A) p‖ ≤ q none v.length)
    (hScalar : ∀ p ∈ K ×ˢ F, ∀ a v,
      (ρ p.2) ^ FirstOutputJets.frequencyOrder v * ‖uncurry (jet v (scalarPrimitive S a)) p‖ ≤
        q (some a) v.length) :
    (ρ η) ^ FirstOutputJets.frequencyOrder w * ‖jet w p.1 x y η‖ ≤
      branchJetConstant n s μ L Kc * H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  by_cases hz : jet w p.1 x y η = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (branchJetConstant_nonneg n s μ (zero_le_one.trans hL)
      (zero_le_one.trans hKc)) (Real.rpow_nonneg (zero_le_one.trans hH) _)
  have hj := graph_branch_jet_support (S := S) (A := A) is p hp w
  have hc : ((x, y), η) ∈ K ×ˢ F := hsupp (hj (subset_tsupport (uncurry (jet w p.1)) hz))
  have hAmp' := hAmp ((x, y), η) hc
  have hScalar' := hScalar ((x, y), η) hc
  exact Weighted.graph_branch_jet_norm_le hU hreg q hq hmono μ s is his p hp
    L Kc H hL hKc hH hlow hhigh hinterp (ρ η) (hρ η) x y η (hcarrier hc) hAmp' hScalar' w hw

/-- Literal-adjoint branch bounds with the same support-local primitive data. -/
theorem adjoint_branch_jet_norm_le_of_supported
    {K : Set (Euclidean n × Euclidean n)} {F : Set (Euclidean n)}
    {U : Set (Point n)} (hU : IsOpen U)
    (hcarrier : K ×ˢ F ⊆ U)
    (hreg : SmoothPrimitivesOn S A U)
    (hsupp : tsupport (uncurry A) ⊆ K ×ˢ F)
    (ρ : Euclidean n → ℝ) (hρ : ∀ η, 0 ≤ ρ η)
    (q : Option (ScalarIndex n) → ℕ → ℝ) (hq : ∀ a j, 0 ≤ q a j)
    (hmono : ∀ a, Monotone (q a)) (μ s : ℕ)
    (L Kc H : ℝ) (hL : 1 ≤ L) (hKc : 1 ≤ Kc) (hH : 1 ≤ H)
    (hlow : ∀ a, q a μ ≤ L) (hhigh : ∀ a, q a (μ + s) ≤ H)
    (hinterp : ∀ a j, μ < j → j < μ + s →
      q a j ≤ Kc * q a μ ^ (1 - ((j - μ : ℕ) : ℝ) / s) *
        q a (μ + s) ^ (((j - μ : ℕ) : ℝ) / s))
    (is : List (Fin n)) (his : is.length ≤ s)
    (p : FullAmplitude n r × List (Fin n))
    (hp : p ∈ fullAmplitudeDerivativeTerms (adjointTransferRemainder S)
      (adjointTransferDatum S) A is)
    (w : List (Coordinate n)) (hw : w.length ≤ μ) (x y η : Euclidean n)
    (hAmp : ∀ p ∈ K ×ˢ F, ∀ v,
      (ρ p.2) ^ FirstOutputJets.frequencyOrder v * ‖uncurry (jet v A) p‖ ≤ q none v.length)
    (hScalar : ∀ p ∈ K ×ˢ F, ∀ a v,
      (ρ p.2) ^ FirstOutputJets.frequencyOrder v * ‖uncurry (jet v (scalarPrimitive S a)) p‖ ≤
        q (some a) v.length) :
    (ρ η) ^ FirstOutputJets.frequencyOrder w * ‖jet w p.1 x y η‖ ≤
      branchJetConstant n s μ L Kc * H ^ (((s - p.2.length : ℕ) : ℝ) / s) := by
  by_cases hz : jet w p.1 x y η = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (branchJetConstant_nonneg n s μ (zero_le_one.trans hL)
      (zero_le_one.trans hKc)) (Real.rpow_nonneg (zero_le_one.trans hH) _)
  have hj := adjoint_branch_jet_support (S := S) (A := A) is p hp w
  have hc : ((x, y), η) ∈ K ×ˢ F := hsupp (hj (subset_tsupport (uncurry (jet w p.1)) hz))
  exact Weighted.adjoint_branch_jet_norm_le hU hreg q hq hmono μ s is his p hp
    L Kc H hL hKc hH hlow hhigh hinterp (ρ η) (hρ η) x y η
    (hcarrier hc) (hAmp ((x, y), η) hc) (hScalar ((x, y), η) hc) w hw

end JanetCartan.FourierIntegral.FullAmplitudePrimitiveBudget.Local
