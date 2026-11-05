module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.PrimitivePhases

/-!
# Fixed frequency loss for complementary parameter jets

For `app:ch_response:thm:response-literal-transfer`:

* `complementaryCarrierJet_eq_polynomial` expands the actual full jet after
  exact carrier cancellation. Its coefficients have no frequency argument and
  its degrees are bounded by the parameter order.
* `contDiffOn_complementaryCarrierJet` and
  `contDiffOn_normalizedComplementaryCarrierJet` prove joint smoothness from
  the original phase, carrier, selector and full-amplitude smoothness.
* `norm_iteratedFDeriv_complementarySelector_joint_le` derives the actual moving
  selector grades from primitive profiles. Compactness supplies uniform carrier
  and selector profiles; no bound on a modified amplitude is assumed.
* `norm_iteratedFDeriv_normalizedComplementaryCarrierJet_joint_le` combines the
  scalar polynomial with the original matrix amplitude. Extraction of `ρ^(2*k)`
  when `1 ≤ L ≤ ρ` restores the original spatial grade, independently of all
  subsequent target/source derivative orders.
* `exists_complementaryCarrierJet_graph_mixed_profile` supplies GraphDecay's
  exact ordered `normalMatrixDerivList` / source `iteratedFDeriv` bound from
  primitive joint phase and original full-amplitude grades. Constants precede
  frequency, amplitude realization and compact parameter.
* `exists_forward_reverse_complementary_mixed_profile` instantiates both actual
  carrier signs using compactness of the parameter and physical supports and
  smoothness of the original phase. Only the original full-amplitude grades
  remain as quantitative inputs from the finite FIO calculus.

The normalized amplitudes preserve the original joint support, the closed
complementary gap, and the exact auxiliary-selector identity. No original mask
is divided out; all physical/frequency shoulders and the literal reverse weight
remain in the generic full amplitude. Fixed Sobolev realization costs and final
decay assembly remain obligations of the parent construction.
-/
