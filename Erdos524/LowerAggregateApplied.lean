import Erdos524.LowerPotentialEstimates
import Erdos524.LowerPotentialAggregate

/-! The own-node potential lower bound and the fully discharged aggregate estimate. -/

namespace Erdos524.QuantileCounting

open Set Filter
open scoped BigOperators
open Erdos524.CauchyKernel Erdos524.RegressionWeightBounds

 theorem lower_core_node_potential_80 {L : ℝ} (hL : 16 ≤ L)
    (hM0 : 1 ≤ lowerMaxDensity L) (hM : lowerMaxDensity L ≤ L)
    (mesh : LowerMesh L) (i : Fin ⌊lowerTotal L⌋₊)
    (hi0 : 0 ≤ mesh.node i) (hi : mesh.node i ≤ 2 * L + 4 * Real.log L) :
    L - mesh.node i / 2 + 80 * Real.log L ≤ omittedPotential mesh.node i (mesh.node i) := by
  dsimp only [LowerMesh, lowerTotal] at mesh i ⊢
  obtain ⟨hab, hB, hr⟩ := lower_parameters_valid (by linarith : 2 ≤ L)
  have hinj := (mesh.strictMono (affineCDF_strictMono hB hr)).injective
  have he := affine_omitted_potential_lower hab hB hr hM0 mesh i (mesh.node i)
    (fun j hj h ↦ hj (hinj h))
  have hb := abs_le.mp (lowerPotential_interior hL hi0 hi)
  have hl := lower_log_max_bound hL hM0 hM
  have hh := lower_log_half hL
  have he' : lowerPotential L (mesh.node i) -
      6 * Real.log (4 * lowerMaxDensity L) - 2 ≤ omittedPotential mesh.node i (mesh.node i) := by
    rw [← omittedPotential_even_sum mesh.node i (mesh.node i)] at he
    exact he
  linarith [hb.1]

theorem lower_aggregate_actual {L : ℝ} (hL : 16 ≤ L)
    (hM0 : 1 ≤ lowerMaxDensity L) (hM : lowerMaxDensity L ≤ L) (mesh : LowerMesh L) :
    (∑ i, (L - mesh.node i / 2)) - 15 * L ^ 2 * (Real.log L + 1) ≤
      ∑ i, omittedPotential mesh.node i (mesh.node i) := by
  apply lower_aggregate_remainder (by linarith) mesh hM
  intro i hi0 hi
  have h := lower_core_node_potential_80 hL hM0 hM mesh i hi0 hi
  have hlog := Real.log_nonneg (by linarith : 1 ≤ L)
  linarith

theorem eventually_lower_aggregate_actual {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ mesh : LowerMesh L,
      (∑ i, (L - mesh.node i / 2)) - ε * L ^ 3 ≤
        ∑ i, omittedPotential mesh.node i (mesh.node i) := by
  filter_upwards [Erdos524.CauchyKernel.eventually_log_remainder_le
    (by norm_num : (0 : ℝ) < 15) heps, eventually_lower_size_controls,
    eventually_ge_atTop (16 : ℝ)] with L herr hsize hL
  intro mesh
  have h := lower_aggregate_actual hL hsize.1 hsize.2.1 mesh
  linarith

end Erdos524.QuantileCounting
