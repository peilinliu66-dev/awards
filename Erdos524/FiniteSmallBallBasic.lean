import Erdos524.LowerSmallBallAssembly

/-! Positivity and sharp logarithmic asymptotics for the finite-only envelope. -/

namespace Erdos524.FiniteSmallBallBasic

open Filter MeasureTheory ProbabilityTheory Matrix WithLp Set
open scoped ENNReal
open Erdos524.FiniteSmallBallEnvelope Erdos524.LowerSmallBallAssembly
open Erdos524.LaplaceKernelComparison Erdos524.GaussianBoxDensity Erdos524.GaussianCovarianceBox

noncomputable def smallBallReal (δ : ℝ) : ℝ := (finiteSmallBall δ).toReal

theorem finiteSmallBall_ne_top (δ : ℝ) : finiteSmallBall δ ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (finiteSmallBall_le_one δ) (by simp))

theorem finiteSmallBall_pos {δ : ℝ} (hδ : 0 < δ) : 0 < finiteSmallBall δ := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (sharp_smallBall_lower (by norm_num : (0 : ℝ) < 1))
  let L := max R (-Real.log δ)
  have hRL : R ≤ L := le_max_left _ _
  have hδL : -Real.log δ ≤ L := le_max_right _ _
  have he : Real.exp (-L) ≤ δ := by
    rw [← Real.exp_log hδ]
    exact Real.exp_le_exp.mpr (by linarith)
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le
    ((hR L hRL).trans (finiteSmallBall_mono he))

theorem smallBallReal_pos {δ : ℝ} (hδ : 0 < δ) : 0 < smallBallReal δ :=
  ENNReal.toReal_pos_iff.mpr ⟨finiteSmallBall_pos hδ, lt_top_iff_ne_top.mpr (finiteSmallBall_ne_top δ)⟩

theorem smallBallReal_le_one (δ : ℝ) : smallBallReal δ ≤ 1 := by
  have h := (ENNReal.toReal_le_toReal (finiteSmallBall_ne_top δ) (by simp : (1 : ℝ≥0∞) ≠ ⊤)).mpr
    (finiteSmallBall_le_one δ)
  simpa only [smallBallReal, ENNReal.toReal_one] using h

theorem smallBallReal_mono : Monotone smallBallReal := by
  intro a b hab
  exact (ENNReal.toReal_le_toReal (finiteSmallBall_ne_top a) (finiteSmallBall_ne_top b)).mpr
    (finiteSmallBall_mono hab)

theorem finiteSmallBall_zero : finiteSmallBall 0 = 0 := by
  have he : finiteKernel (fun _ : Fin 1 ↦ (0 : ℝ)) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [finiteKernel_apply, Matrix.one_apply]
  have hS : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := Matrix.PosDef.one
  have hbox := gaussian_box_upper hS (fun _ ↦ 0)
  simp only [mul_zero, ENNReal.ofReal_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.zero_add, pow_one, mul_zero] at hbox
  have h := finiteSmallBall_le_evaluation 0 0 (fun _ ↦ 0)
  change finiteSmallBall 0 ≤ (multivariateGaussian 0 (finiteKernel (fun _ : Fin 1 ↦ (0 : ℝ))))
    (ofLp ⁻¹' box (fun _ ↦ 0)) at h
  rw [he] at h
  exact le_antisymm (h.trans hbox) bot_le

theorem finiteSmallBall_nonpos {δ : ℝ} (hδ : δ ≤ 0) : finiteSmallBall δ = 0 :=
  le_antisymm ((finiteSmallBall_mono hδ).trans_eq finiteSmallBall_zero) bot_le

theorem sharp_log_bounds {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      -(2 / (3 * Real.pi ^ 2) + ε) ≤ Real.log (smallBallReal (Real.exp (-L))) / L ^ 3 ∧
      Real.log (smallBallReal (Real.exp (-L))) / L ^ 3 ≤ -(2 / (3 * Real.pi ^ 2) - ε) := by
  filter_upwards [sharp_smallBall_two_sided heps, eventually_gt_atTop (0 : ℝ)] with L h hL
  have hpos := smallBallReal_pos (Real.exp_pos (-L))
  have hlo := (ENNReal.toReal_le_toReal (by finiteness) (finiteSmallBall_ne_top _)).mpr h.1
  have hhi := (ENNReal.toReal_le_toReal (finiteSmallBall_ne_top _) (by finiteness)).mpr h.2
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hlo hhi
  change Real.exp (-(2 / (3 * Real.pi ^ 2) + ε) * L ^ 3) ≤ smallBallReal (Real.exp (-L)) at hlo
  change smallBallReal (Real.exp (-L)) ≤ Real.exp (-(2 / (3 * Real.pi ^ 2) - ε) * L ^ 3) at hhi
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  have hu := Real.log_le_log hpos hhi
  rw [Real.log_exp] at hl hu
  constructor
  · exact (le_div_iff₀ (pow_pos hL 3)).mpr hl
  · exact (div_le_iff₀ (pow_pos hL 3)).mpr hu

theorem sharp_log_asymptotic :
    Tendsto (fun L : ℝ ↦ Real.log (smallBallReal (Real.exp (-L))) / L ^ 3)
      atTop (nhds (-(2 / (3 * Real.pi ^ 2)))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε heps
  filter_upwards [sharp_log_bounds (by linarith : 0 < ε / 2)] with L h
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h.1, h.2]

end Erdos524.FiniteSmallBallBasic
