module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.WeakTransfer.ParameterClass

/-!
# Smoothness of the supported annular L² representative

The consumer is the fixed-time regularity input of
`Parameter.orderedTransferAction_elapsedIntegral`. The existing compact-family
lift gives norm smoothness from the proved joint kernel smoothness, for
`app:ch_response:eq:direct-envelope-profile` and `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
open Pseudodifferential CompactTransfer AnnularSobolev.WeakTransfer
open JanetCartan.ResponseTransfer.ParameterRealization.L2Family
open JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- The existing supported joint-word class is smooth in the original L²
norm. This supplies fixed-time smoothness, independently of quantitative
domination, in `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_supportedJointWordClass
    (g : E × P → Fin r → ℂ) {C : Set P} (hC : IsOpen C)
    (hg : ContDiffOn ℝ ∞ g (univ ×ˢ C)) {X : Set E} (hX : IsCompact X)
    (es : List (E × P)) :
    ContDiffOn ℝ ∞ (supportedJointWordClass g hX es) C := by
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  have hG : ContDiffOn ℝ ∞ (fun q : P × E => (WithLp.toLp 2
      (originalDatumDerivative es g (q.2, q.1)) : V)) (C ×ˢ univ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r => ℂ)).symm.contDiff.comp_contDiffOn
      ((contDiffOn_originalDatumDerivative (isOpen_univ.prod hC) hg es).comp
        (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hq => ⟨mem_univ _, hq.1⟩))
  apply contDiffOn_infty.mpr
  intro k c hc
  exact ((compactToL2Vector hX).contDiff.contDiffAt.comp c
    (compactFamily_contDiffAt k hC hG hc)).contDiffWithinAt

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
