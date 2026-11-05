module

public import JanetCartan.Analysis.Operator.SmallSupport.Cutoff
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.Hilbert.CompactFamily

/-!
# Actual parameter derivatives of the uncut reduced solution

The joint smooth solution and its actual L² family have the same parameter
derivatives. Localize by an exhausting countable family of spatial bumps,
apply the existing compact-family differentiation theorem, and remove the
bumps almost everywhere. Thus no compact-output assumption is needed for
the original full solver in `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace JanetCartan.FixedDomainInverse

open SmallSupport Pseudodifferential
open ResponseTransfer.Complement.ParameterDerivatives.Hilbert

variable {n q : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "CF" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp CF 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem bump_iteratedFDeriv_L2_ae_of_joint_smooth
    {V : Set P} (hV : IsOpen V) {g : P → E → CF}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    {u : P → H} (hu : ContDiffOn ℝ ∞ u V)
    (hidentify : ∀ c ∈ V, u c =ᵐ[volume] g c)
    {center : E} (χ : ContDiffBump center)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    (fun x ↦ χ x • (iteratedFDeriv ℝ k u c v : H) x) =ᵐ[volume]
      fun x ↦ χ x • iteratedFDeriv ℝ k (fun b ↦ g b x) c v := by
  let X := tsupport (χ : E → ℝ)
  have hX : IsCompact X := χ.hasCompactSupport
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  let gχ : P → E → CF := fun b x ↦ χ x • g b x
  have hgχ : ContDiffOn ℝ ∞ (Function.uncurry gχ) (V ×ˢ univ) :=
    (χ.contDiff.comp contDiff_snd).contDiffOn.smul hg
  have hsχ : ∀ b ∈ V, ∀ x ∉ X, gχ b x = 0 := by
    intro b _ x hx
    change χ x • g b x = 0
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  let B : H →L[ℝ] H := bumpL2 (p := 2) le_rfl χ
  have he : compactVectorL2Family hX gχ =ᶠ[𝓝 c] B ∘ u := by
    filter_upwards [hV.mem_nhds hc] with b hb
    apply Lp.ext
    filter_upwards [compactVectorL2Family_ae hX hgχ hsχ hb,
      bumpL2_coeFn (p := 2) le_rfl χ (u b), hidentify b hb] with x hx hy hz
    exact hx.trans ((congrArg (fun z : CF ↦ χ x • z) hz.symm).trans hy.symm)
  have hder : iteratedFDeriv ℝ k (compactVectorL2Family hX gχ) c v =
      B (iteratedFDeriv ℝ k u c v) := by
    calc
      _ = iteratedFDeriv ℝ k (B ∘ u) c v :=
        congrArg (fun m ↦ m v) (he.iteratedFDeriv ℝ k).eq_of_nhds
      _ = _ := congrArg (fun m ↦ m v)
        (B.iteratedFDeriv_comp_left (hu.contDiffAt (hV.mem_nhds hc)) (by simp))
  have hj := iteratedFDeriv_compactVectorL2Family_ae hX hV hgχ hsχ k v hc
  rw [hder] at hj
  filter_upwards [hj, bumpL2_coeFn (p := 2) le_rfl χ
    (iteratedFDeriv ℝ k u c v)] with x hx hy
  apply (hy.symm.trans hx).trans
  have hgx : ContDiffOn ℝ ∞ (fun b ↦ g b x) V :=
    hg.comp (contDiffOn_id.prodMk contDiffOn_const) (fun b hb ↦ ⟨hb, mem_univ x⟩)
  exact congrArg (fun m ↦ m v)
    (iteratedFDeriv_const_smul_apply' (a := χ x)
      ((hgx.contDiffAt (hV.mem_nhds hc)).of_le (by simp)))

/-- The actual L² parameter derivative represents the actual classical
parameter derivative of the SAME jointly smooth solution, without an
output-support hypothesis. This closes the uncut `ug` identification needed
by `CanonicalAtomRealization`'s original response Fourier-to-classical
conversion (`app:ch_response:eq:response-graded-reduced`,
`app:ch_response:thm:response-literal-transfer`). -/
theorem iteratedFDeriv_L2_ae_of_joint_smooth
    {V : Set P} (hV : IsOpen V) {g : P → E → CF}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    {u : P → H} (hu : ContDiffOn ℝ ∞ u V)
    (hidentify : ∀ c ∈ V, u c =ᵐ[volume] g c)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    (iteratedFDeriv ℝ k u c v : H) =ᵐ[volume]
      fun x ↦ iteratedFDeriv ℝ k (fun b ↦ g b x) c v := by
  let χ (N : ℕ) : ContDiffBump (0 : E) :=
    ⟨(N : ℝ) + 1, (N : ℝ) + 2, by positivity, by linarith⟩
  have hlocal (N : ℕ) :=
    bump_iteratedFDeriv_L2_ae_of_joint_smooth hV hg hu hidentify (χ N) k v hc
  filter_upwards [ae_all_iff.mpr hlocal] with x hx
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  have hχ : χ N x = 1 := by
    apply (χ N).one_of_mem_closedBall
    change dist x 0 ≤ (N : ℝ) + 1
    rw [dist_zero_right]
    exact hN.le.trans (le_add_of_nonneg_right zero_le_one)
  simpa only [hχ, one_smul] using hx N

/-- Scalar Fourier coordinates of every actual classical parameter jet
of the retained reduced solution. Membership and norms agree definitionally
with the already bounded L² derivative, with no additional reserve or
coefficient loss (`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_matrixFourier_parameter_jet_class_of_joint_smooth
    {V : Set P} (hV : IsOpen V) {g : P → E → CF}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    {u : P → H} (hu : ContDiffOn ℝ ∞ u V)
    (hidentify : ∀ c ∈ V, u c =ᵐ[volume] g c)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ V) :
    ∃ ug : PiLp 2 (fun _ : Fin q ↦ Lp ℂ 2 (volume : Measure E)),
      (∀ j, ug j =ᵐ[volume] fun x ↦
        (iteratedFDeriv ℝ k (fun b ↦ g b x) c v) j) ∧
      ug = finiteL2CoordinateIsometry volume (iteratedFDeriv ℝ k u c v) ∧
      (∀ s : ℝ, MemMatrixFourierSobolev s ug ↔
        MemVectorFourierSobolev s (iteratedFDeriv ℝ k u c v)) ∧
      (∀ s : ℝ, matrixFourierSobolevNorm s ug =
        vectorFourierSobolevNorm s (iteratedFDeriv ℝ k u c v)) := by
  refine ⟨finiteL2CoordinateIsometry volume (iteratedFDeriv ℝ k u c v),
    ?_, rfl, fun _ ↦ Iff.rfl, fun _ ↦ rfl⟩
  exact (finiteL2CoordinateIsometry_ae_iff volume _ _).mp
    (iteratedFDeriv_L2_ae_of_joint_smooth hV hg hu hidentify k v hc)

end JanetCartan.FixedDomainInverse
