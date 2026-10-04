import Erdos524.LowerAggregateApplied
import Erdos524.LowerProbabilityBudgets
import Erdos524.SampleBoxAsymptotic
import Erdos524.PotentialSmallBallLower
import Erdos524.PotentialReindex

/-! Assembly of the actual finite-only lower small-ball bound. -/

namespace Erdos524.LowerSmallBallAssembly

open Set MeasureTheory ProbabilityTheory Matrix WithLp Filter
open scoped ENNReal BigOperators
open Erdos524.CauchyKernel Erdos524.QuantileCounting
open Erdos524.RegressionWeightBounds Erdos524.SampleBoxLowerExponent
open Erdos524.SampleBoxAsymptotic Erdos524.PotentialSmallBallLower
open Erdos524.FiniteSmallBallEnvelope Erdos524.GaussianBoxDensity

 theorem finite_lower_smallBall (L : ℝ) (hL : 16 ≤ L)
    (hM0 : 1 ≤ lowerMaxDensity L) (hM : lowerMaxDensity L ≤ L)
    (hNmax : (⌊lowerTotal L⌋₊ : ℝ) ≤ L ^ 2) (hNpos : 0 < ⌊lowerTotal L⌋₊)
    (mesh : LowerMesh L) :
    ENNReal.ofReal (Real.exp (sampleContribution L (⌊lowerTotal L⌋₊ : ℝ)
      (∑ i, (L - mesh.node i / 2)))) ≤ finiteSmallBall (Real.exp (1 - L)) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
  let e : Fin (n + 1) ≃o Fin ⌊lowerTotal L⌋₊ := Fin.castOrderIso hn.symm
  let s : Fin (n + 1) → ℝ := fun i ↦ mesh.node (e i)
  obtain ⟨hab, hB, hr⟩ := lower_parameters_valid (by linarith : 2 ≤ L)
  have hs : StrictMono s := (mesh.strictMono (affineCDF_strictMono hB hr)).comp e.strictMono
  have hN : (n + 1 : ℝ) = (⌊lowerTotal L⌋₊ : ℝ) := by exact_mod_cast hn.symm
  have hsum : (∑ i, (L - s i / 2)) = ∑ i, (L - mesh.node i / 2) :=
    e.toEquiv.sum_comp (fun i ↦ L - mesh.node i / 2)
  have hsumU : (∑ i, omittedPotential s i (s i)) =
      ∑ i, omittedPotential mesh.node i (mesh.node i) :=
    sum_own_potential_equiv mesh.node e.toEquiv
  have ho (i : Fin (n + 1)) (t : ℝ) : omittedPotential s i t = omittedPotential mesh.node (e i) t :=
    omittedPotential_equiv mesh.node e.toEquiv i t
  have hrow (i : Fin (n + 1)) : omittedPotential s i (s i) ≤ L - s i / 2 + 120 * Real.log L := by
    rw [ho]
    exact lower_node_potential_120 hL hM0 hM mesh (e i)
  have hagg : (∑ i, (L - s i / 2)) - 15 * L ^ 2 * (Real.log L + 1) ≤
      ∑ i, omittedPotential s i (s i) := by
    rw [hsum, hsumU]
    exact lower_aggregate_actual hL hM0 hM mesh
  have hp := raw_constant_sample_box_lower s hs L (120 * Real.log L) (200 * Real.log L)
    (15 * L ^ 2 * (Real.log L + 1)) hrow hagg
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hnode (i : Fin (n + 1)) : s i ≤ 2 * L + 2 * (4 * Real.log L) := by
    have h := (mesh.node_mem (e i)).2
    change s i ≤ lowerRight L at h
    unfold lowerRight at h
    linarith
  have hpoint (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 2 * L + 4 * Real.log L)
      (hne : ∀ j, t ≠ s j) (i : Fin (n + 1)) :
      L - t / 2 + 80 * Real.log L ≤ omittedPotential s i t := by
    have hne' (j) : t ≠ mesh.node j := by
      intro hj
      apply hne (e.symm j)
      simpa only [s, e.apply_symm_apply] using hj
    rw [ho]
    exact lower_omitted_potential_80 hL hM0 hM mesh ht0 ht hne' (e i)
  have hcontract := finiteSmallBall_lower_of_potentials s hs.injective L (4 * Real.log L)
    (120 * Real.log L) (80 * Real.log L) (Real.exp (-L - 200 * Real.log L))
    (Real.exp (-L)) (Real.exp (-L) / 2)
    (Real.exp_pos _).le (by positivity) (by positivity) (by positivity) (by positivity)
    hrow hnode hpoint
    (lower_mean_budget hL (by positivity) (by rw [hN]; exact hNmax))
    (lower_residual_budget hL)
  have hE : sampleContribution L (n + 1 : ℝ) (∑ i, (L - s i / 2)) + Real.log 2 =
      -(∑ i, (L - s i / 2)) / 2 - (n + 1 : ℝ) * (200 * Real.log L) -
        (15 * L ^ 2 * (Real.log L + 1)) / 2 +
        (n + 1 : ℝ) * ((3 / 2 : ℝ) * Real.log 2 - Real.log (Real.sqrt (2 * Real.pi))) -
        (n + 1 : ℝ) ^ 2 * Real.exp (2 * (120 * Real.log L - 200 * Real.log L)) := by
    unfold sampleContribution sampleNormalization
    rw [show 2 * (120 * Real.log L - 200 * Real.log L) = -160 * Real.log L by ring]
    ring
  rw [← hE] at hp
  have hscale (z : ℝ) : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (z + Real.log 2)) =
      ENNReal.ofReal (Real.exp z) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [mul_comm (1 / 2 : ℝ≥0∞), mul_assoc]
    norm_num
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have hp' := mul_le_mul_of_nonneg_left hp (show (0 : ℝ≥0∞) ≤ 1 / 2 by positivity)
  rw [hscale] at hp'
  have hfinal := hp'.trans hcontract
  rw [hN, hsum, ← Real.exp_add] at hfinal
  convert hfinal using 1 <;> congr 2 <;> ring

theorem sharp_smallBall_lower_shifted {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      ENNReal.ofReal (Real.exp (-(2 / (3 * Real.pi ^ 2) + ε) * L ^ 3)) ≤
        finiteSmallBall (Real.exp (1 - L)) := by
  filter_upwards [eventually_lower_size_controls, eventually_lower_deficit_sum heps,
    eventually_sampleContribution_lower heps, eventually_ge_atTop (16 : ℝ)] with L hsize hsum hexp hL
  obtain ⟨hab, hB, hr⟩ := lower_parameters_valid (by linarith : 2 ≤ L)
  obtain ⟨mesh⟩ := exists_affine_quantile_mesh hab hB hr
  have hp := finite_lower_smallBall L hL hsize.1 hsize.2.1 hsize.2.2.1 hsize.2.2.2 mesh
  have he := hexp (⌊lowerTotal L⌋₊ : ℝ) (∑ i, (L - mesh.node i / 2))
    (by positivity) hsize.2.2.1 (hsum mesh)
  exact (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he)).trans hp

theorem eventually_cubic_shift {C ε : ℝ} (hC : 0 < C) (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, C * (L + 1) ^ 3 ≤ (C + ε) * L ^ 3 := by
  filter_upwards [eventually_ge_atTop (max 1 (7 * C / ε))] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hb : 7 * C / ε ≤ L := (le_max_right _ _).trans hL
  have hCeps : 7 * C ≤ ε * L := by
    have h := (div_le_iff₀ heps).mp hb
    linarith
  have hcube : (L + 1) ^ 3 ≤ L ^ 3 + 7 * L ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hcube hC.le
  have h2 := mul_le_mul_of_nonneg_right hCeps (sq_nonneg L)
  nlinarith

theorem sharp_smallBall_lower {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      ENNReal.ofReal (Real.exp (-(2 / (3 * Real.pi ^ 2) + ε) * L ^ 3)) ≤
        finiteSmallBall (Real.exp (-L)) := by
  have heps2 : 0 < ε / 2 := by linarith
  have hC : 0 < 2 / (3 * Real.pi ^ 2) + ε / 2 := by positivity
  obtain ⟨R, hR⟩ := eventually_atTop.mp (sharp_smallBall_lower_shifted heps2)
  filter_upwards [eventually_ge_atTop R, eventually_cubic_shift hC heps2] with L hLR hcube
  have hp := hR (L + 1) (by linarith)
  have he : 1 - (L + 1) = -L := by ring
  rw [he] at hp
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) hp
  nlinarith

theorem sharp_smallBall_two_sided {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      ENNReal.ofReal (Real.exp (-(2 / (3 * Real.pi ^ 2) + ε) * L ^ 3)) ≤
          finiteSmallBall (Real.exp (-L)) ∧
      finiteSmallBall (Real.exp (-L)) ≤
          ENNReal.ofReal (Real.exp (-(2 / (3 * Real.pi ^ 2) - ε) * L ^ 3)) :=
  (sharp_smallBall_lower heps).and (sharp_smallBall_upper heps)

end Erdos524.LowerSmallBallAssembly
