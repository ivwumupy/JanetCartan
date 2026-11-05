module

public import JanetCartan.Geometry.IsometricEmbedding.Calculus

import Mathlib.Tactic.Abel

/-!
# The exact finite-stage metric ledger

The algebraic identity `main:eq:metric-ledger` in `paper.tex`, and the exact
contribution of the last Fourier cutoff in `main:thm:step`.

The mean equation and the self/off definitions are explicit inputs. Here `H`
denotes the common unscaled Hermitian tensor ∑ μν Re((dZν)* dZν) in
`main:eq:mean-equation` and `main:eq:self-off`. No estimates or construction of
the mean and product responses are asserted. In particular, the pair residual
`linearizedMetric F S + Qoff` is retained without assuming that it vanishes.

The interaction `linearizedMetric P W₂` is exactly 2 sym((dP)ᵀ dW₂), and
`inducedMetric W₂` is (dW₂)ᵀ dW₂, by the definitions in `Basic`.
All derivatives are ordinary derivatives at points; the domain versions thus
apply also to the closed measurement domain, when the fields are smooth nearby.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace JanetCartan

variable {n N : ℕ} {F P V S W₂ U Ecut : Euclidean n → Euclidean N}
  {g e eR H Hself Qoff Emean : MetricField n} {x : Euclidean n}
  {s : Set (Euclidean n)} {b : ℝ}

/-- `main:eq:metric-expansion`, applied twice: the exact metric error of a
primary and a secondary increment, before using the mean and pair identities. -/
theorem inducedMetric_add_add_sub (hF : DifferentiableAt ℝ F x)
    (hP : DifferentiableAt ℝ P x) (hW₂ : DifferentiableAt ℝ W₂ x) :
    inducedMetric (F + P + W₂) x - g x =
      inducedMetric F x - g x + linearizedMetric F P x +
        linearizedMetric F W₂ x + inducedMetric P x +
        linearizedMetric P W₂ x + inducedMetric W₂ x := by
  rw [add_assoc F P W₂, inducedMetric_add hF (hP.add hW₂),
    linearizedMetric_add_apply hP hW₂, inducedMetric_add hP hW₂]
  abel

/-- `main:eq:mean-equation` and `main:eq:self-off`: multiplying the genuine
normalized mean equation by b² cancels the complete Hermitian self tensor.
The assumption `b ≠ 0` is essential for the normalization e_R / b². -/
theorem meanMetric_cancellation (hb : b ≠ 0)
    (hmean : Emean x = linearizedMetric F V x + H x - (b ^ 2)⁻¹ • eR x)
    (hself : Hself x = b ^ 2 • H x) :
    b ^ 2 • linearizedMetric F V x + Hself x = eR x + b ^ 2 • Emean x := by
  rw [hmean, hself, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hb),
    one_smul]
  abel

/-- `main:eq:metric-ledger`: the exact finite-stage ledger, conditional only on
the displayed mean equation and the definitions of e, W₂, H_self and Q_off.
The primary strain, mean residual, pair residual and nonlinear terms all remain. -/
theorem inducedMetric_metricLedger (hF : DifferentiableAt ℝ F x)
    (hP : DifferentiableAt ℝ P x) (hV : DifferentiableAt ℝ V x)
    (hS : DifferentiableAt ℝ S x) (hb : b ≠ 0)
    (he : e x = g x - inducedMetric F x) (hW₂ : W₂ = b ^ 2 • V + S)
    (hself : Hself x = b ^ 2 • H x)
    (hoff : Qoff x = inducedMetric P x - Hself x)
    (hmean : Emean x = linearizedMetric F V x + H x - (b ^ 2)⁻¹ • eR x) :
    inducedMetric (F + P + W₂) x - g x =
      (eR x - e x) + linearizedMetric F P x + b ^ 2 • Emean x +
        (linearizedMetric F S x + Qoff x) +
        linearizedMetric P W₂ x + inducedMetric W₂ x := by
  have hW₂' : DifferentiableAt ℝ W₂ x := hW₂ ▸ (hV.const_smul _).add hS
  have hlin : linearizedMetric F W₂ x =
      b ^ 2 • linearizedMetric F V x + linearizedMetric F S x := by
    rw [hW₂, linearizedMetric_add_apply (hV.const_smul _) hS,
      linearizedMetric_smul_apply hV]
  have hquad : inducedMetric P x = Hself x + Qoff x := by rw [hoff]; abel
  calc
    inducedMetric (F + P + W₂) x - g x =
        (inducedMetric F x - g x) + linearizedMetric F P x +
          (b ^ 2 • linearizedMetric F V x + Hself x) +
          linearizedMetric F S x + Qoff x +
          linearizedMetric P W₂ x + inducedMetric W₂ x := by
      rw [inducedMetric_add_add_sub hF hP hW₂', hlin, hquad]
      abel
    _ = _ := by rw [meanMetric_cancellation hb hmean hself, he]; abel

/-- `main:eq:metric-ledger` with all named auxiliary fields substituted by their
definitions. The free tensor `H` is the common Hermitian wave tensor; `eR` is the
chosen smoothed defect. This identity alone makes no size claim about either. -/
theorem inducedMetric_metricLedger_substitute (hF : DifferentiableAt ℝ F x)
    (hP : DifferentiableAt ℝ P x) (hV : DifferentiableAt ℝ V x)
    (hS : DifferentiableAt ℝ S x) (hb : b ≠ 0) :
    let e := g - inducedMetric F
    let Hself := b ^ 2 • H
    let Qoff := inducedMetric P - Hself
    let Emean := linearizedMetric F V + H - (b ^ 2)⁻¹ • eR
    let W₂ := b ^ 2 • V + S
    inducedMetric (F + P + W₂) x - g x =
      (eR x - e x) + linearizedMetric F P x + b ^ 2 • Emean x +
        (linearizedMetric F S x + Qoff x) +
        linearizedMetric P W₂ x + inducedMetric W₂ x :=
  inducedMetric_metricLedger hF hP hV hS hb rfl rfl rfl rfl rfl

/-- `main:eq:metric-ledger` on the measurement domain, using the same mean and
self/off identities at every point of that domain. -/
theorem inducedMetric_metricLedger_on
    (hF : ∀ x ∈ s, DifferentiableAt ℝ F x) (hP : ∀ x ∈ s, DifferentiableAt ℝ P x)
    (hV : ∀ x ∈ s, DifferentiableAt ℝ V x) (hS : ∀ x ∈ s, DifferentiableAt ℝ S x)
    (hb : b ≠ 0) (he : EqOn e (g - inducedMetric F) s) (hW₂ : W₂ = b ^ 2 • V + S)
    (hself : EqOn Hself (b ^ 2 • H) s)
    (hoff : EqOn Qoff (inducedMetric P - Hself) s)
    (hmean : EqOn Emean (linearizedMetric F V + H - (b ^ 2)⁻¹ • eR) s) :
    EqOn (inducedMetric (F + P + W₂) - g)
      ((eR - e) + linearizedMetric F P + b ^ 2 • Emean +
        (linearizedMetric F S + Qoff) + linearizedMetric P W₂ + inducedMetric W₂) s := by
  intro x hx
  exact inducedMetric_metricLedger (hF x hx) (hP x hx) (hV x hx) (hS x hx)
    hb (he hx) hW₂ (hself hx) (hoff hx) (hmean hx)

/-- `main:thm:step`: if E_cut = U - (P + W₂), the exact extra metric error is
Dγ_(F+P+W₂) E_cut + (dE_cut)ᵀ dE_cut, including its quadratic term. -/
theorem inducedMetric_cutoffError (hF : DifferentiableAt ℝ F x)
    (hP : DifferentiableAt ℝ P x) (hW₂ : DifferentiableAt ℝ W₂ x)
    (hEcut : DifferentiableAt ℝ Ecut x) (hcut : Ecut = U - (P + W₂)) :
    inducedMetric (F + U) x - g x =
      (inducedMetric (F + P + W₂) x - g x) +
        linearizedMetric (F + P + W₂) Ecut x + inducedMetric Ecut x := by
  have hsum : F + U = (F + P + W₂) + Ecut := by rw [hcut]; abel
  rw [hsum, inducedMetric_add ((hF.add hP).add hW₂) hEcut]
  abel

/-- `main:eq:metric-ledger` and the final cutoff paragraph of `main:thm:step`:
the full exact ledger for the final increment U, including both cutoff terms. -/
theorem inducedMetric_metricLedger_cutoff (hF : DifferentiableAt ℝ F x)
    (hP : DifferentiableAt ℝ P x) (hV : DifferentiableAt ℝ V x)
    (hS : DifferentiableAt ℝ S x) (hEcut : DifferentiableAt ℝ Ecut x) (hb : b ≠ 0)
    (he : e x = g x - inducedMetric F x) (hW₂ : W₂ = b ^ 2 • V + S)
    (hself : Hself x = b ^ 2 • H x)
    (hoff : Qoff x = inducedMetric P x - Hself x)
    (hmean : Emean x = linearizedMetric F V x + H x - (b ^ 2)⁻¹ • eR x)
    (hcut : Ecut = U - (P + W₂)) :
    inducedMetric (F + U) x - g x =
      (eR x - e x) + linearizedMetric F P x + b ^ 2 • Emean x +
        (linearizedMetric F S x + Qoff x) +
        linearizedMetric P W₂ x + inducedMetric W₂ x +
        linearizedMetric (F + P + W₂) Ecut x + inducedMetric Ecut x := by
  have hW₂' : DifferentiableAt ℝ W₂ x := hW₂ ▸ (hV.const_smul _).add hS
  rw [inducedMetric_cutoffError hF hP hW₂' hEcut hcut,
    inducedMetric_metricLedger hF hP hV hS hb he hW₂ hself hoff hmean]

/-- `main:thm:step`: the complete ledger on the measurement domain after the
final cutoff. The analytic smallness of the displayed residuals is separate. -/
theorem inducedMetric_metricLedger_cutoff_on
    (hF : ∀ x ∈ s, DifferentiableAt ℝ F x) (hP : ∀ x ∈ s, DifferentiableAt ℝ P x)
    (hV : ∀ x ∈ s, DifferentiableAt ℝ V x) (hS : ∀ x ∈ s, DifferentiableAt ℝ S x)
    (hEcut : ∀ x ∈ s, DifferentiableAt ℝ Ecut x) (hb : b ≠ 0)
    (he : EqOn e (g - inducedMetric F) s) (hW₂ : W₂ = b ^ 2 • V + S)
    (hself : EqOn Hself (b ^ 2 • H) s)
    (hoff : EqOn Qoff (inducedMetric P - Hself) s)
    (hmean : EqOn Emean (linearizedMetric F V + H - (b ^ 2)⁻¹ • eR) s)
    (hcut : Ecut = U - (P + W₂)) :
    EqOn (inducedMetric (F + U) - g)
      ((eR - e) + linearizedMetric F P + b ^ 2 • Emean +
        (linearizedMetric F S + Qoff) + linearizedMetric P W₂ + inducedMetric W₂ +
        linearizedMetric (F + P + W₂) Ecut + inducedMetric Ecut) s := by
  intro x hx
  exact inducedMetric_metricLedger_cutoff (hF x hx) (hP x hx) (hV x hx) (hS x hx)
    (hEcut x hx) hb (he hx) hW₂ (hself hx) (hoff hx) (hmean hx) hcut

end JanetCartan
