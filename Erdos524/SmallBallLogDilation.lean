import Erdos524.FiniteSmallBallDilation
import Erdos524.DilationMesh
import Erdos524.FiniteSmallBallBasic

/-! Uniform quantitative logarithmic growth, at the precision needed for inverse-F scaling. -/

namespace Erdos524.SmallBallLogDilation

open Set Filter MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.FiniteSmallBallDilation Erdos524.FiniteSmallBallEnvelope
open Erdos524.FiniteSmallBallBasic Erdos524.DilationMesh
open Erdos524.GaussianBoxDensity Erdos524.FiniteKernelPerturbation

theorem sq_sub_one_le_six_log {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) : r ^ 2 - 1 ≤ 6 * Real.log r := by
  have hrp : 0 < r := by linarith
  have hlog := Real.log_nonneg hr
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hrp) hrp.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hrp.ne'] at h
  have h1 := mul_nonneg (sub_nonneg.mpr hr2) hlog
  have h2 := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr2)
  nlinarith

theorem finiteSmallBall_log_dilation {L : ℝ} (hL : 100 ≤ L) (hmesh : 4 * Real.log L ≤ L / 4)
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    L ^ 2 / (8 * Real.pi ^ 2) * Real.log r ≤
      Real.log (smallBallReal (r * Real.exp (-L))) - Real.log (smallBallReal (Real.exp (-L))) := by
  have hb := count_bounds (by linarith : 16 ≤ L) hmesh
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hb.2.2)
  have hN : (count L : ℝ) = n + 1 := by exact_mod_cast hn
  have hsize : (n + 1 : ℝ) ≤ L ^ 2 := by simpa only [hN] using hb.2.1
  have hQ : ∀ x ∈ box (fun i : Fin (n + 1) ↦ Real.sqrt (Real.exp (node L i)) * Real.exp (-L)),
      x ⬝ᵥ (normalizedFiniteKernel (fun i : Fin (n + 1) ↦ Real.exp (node L i)))⁻¹ *ᵥ x ≤ (n + 1 : ℝ) / 6 := by
    intro x hx
    exact (sample_box_energy (by linarith) hmesh hn hx).trans
      (energy_budget_small hL (by positivity) hsize)
  have hd := finiteSmallBall_dilation (fun i : Fin (n + 1) ↦ Real.exp (node L i))
    (fun _ ↦ Real.exp_pos _) (sample_posDef (by linarith) hmesh hn) hr hQ
  let c := r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * ((n + 1 : ℝ) / 6)) / 2)
  have hrp : 0 < r := by linarith
  have hc : 0 < c := by unfold c; positivity
  have hF := smallBallReal_pos (Real.exp_pos (-L))
  have hFr := smallBallReal_pos (mul_pos hrp (Real.exp_pos (-L)))
  have hreal : c * smallBallReal (Real.exp (-L)) ≤ smallBallReal (r * Real.exp (-L)) := by
    have h := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finiteSmallBall_ne_top _)) (finiteSmallBall_ne_top _)).mpr hd
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, smallBallReal, c] using h
  have hlog := Real.log_le_log (mul_pos hc hF) hreal
  rw [Real.log_mul hc.ne' hF.ne'] at hlog
  have hcLog : Real.log c = (n + 1 : ℝ) * Real.log r - (r ^ 2 - 1) * (n + 1 : ℝ) / 12 := by
    unfold c
    rw [Real.log_mul (pow_pos hrp _).ne' (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    push_cast
    ring
  rw [hcLog] at hlog
  have hsix := sq_sub_one_le_six_log hr hr2
  have hcost := mul_le_mul_of_nonneg_right hsix (show 0 ≤ (n + 1 : ℝ) / 12 by positivity)
  have hNl : L ^ 2 / (4 * Real.pi ^ 2) ≤ (n + 1 : ℝ) := by simpa only [hN] using hb.1
  have hcount := mul_le_mul_of_nonneg_right hNl (show 0 ≤ Real.log r / 2 by exact div_nonneg (Real.log_nonneg hr) (by norm_num))
  have he : L ^ 2 / (8 * Real.pi ^ 2) * Real.log r = L ^ 2 / (4 * Real.pi ^ 2) * (Real.log r / 2) := by ring
  rw [he]
  nlinarith only [hcount, hcost, hlog]

theorem eventually_log_dilation :
    ∀ᶠ L : ℝ in atTop, ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
      L ^ 2 / (8 * Real.pi ^ 2) * Real.log r ≤
        Real.log (smallBallReal (r * Real.exp (-L))) - Real.log (smallBallReal (Real.exp (-L))) := by
  filter_upwards [eventually_dilation_mesh] with L hL
  intro r hr hr2
  exact finiteSmallBall_log_dilation hL.1 hL.2.1 hr hr2

theorem eventually_log_contraction :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℝ, 1 / 2 ≤ q → q ≤ 1 →
      L ^ 2 / (8 * Real.pi ^ 2) * (-Real.log q) ≤
        Real.log (smallBallReal (Real.exp (-L))) - Real.log (smallBallReal (q * Real.exp (-L))) := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp eventually_log_dilation
  filter_upwards [eventually_ge_atTop (max R 0)] with L hL
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 ≤ L := (le_max_right _ _).trans hL
  intro q hq hq1
  have hqp : 0 < q := by linarith
  have hlog : Real.log q ≤ 0 := Real.log_nonpos hqp.le hq1
  have hshift : R ≤ L - Real.log q := by linarith
  have hr : 1 ≤ q⁻¹ := (one_le_inv₀ hqp).mpr hq1
  have hr2 : q⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hqp).mpr (by linarith)
  have h := hR (L - Real.log q) hshift q⁻¹ hr hr2
  have he : Real.exp (-(L - Real.log q)) = q * Real.exp (-L) := by
    rw [show -(L - Real.log q) = Real.log q + -L by ring, Real.exp_add, Real.exp_log hqp]
  rw [he, show q⁻¹ * (q * Real.exp (-L)) = Real.exp (-L) by rw [← mul_assoc, inv_mul_cancel₀ hqp.ne', one_mul],
    Real.log_inv] at h
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

theorem eventually_probability_dilation {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℝ in atTop,
      smallBallReal (Real.exp (-L)) * Real.exp (c * L ^ 2) ≤
        smallBallReal ((1 + ε) * Real.exp (-L)) ∧
      smallBallReal ((1 - ε) * Real.exp (-L)) ≤
        smallBallReal (Real.exp (-L)) * Real.exp (-c * L ^ 2) := by
  let c := min (Real.log (1 + ε)) (-Real.log (1 - ε)) / (8 * Real.pi ^ 2)
  have hplus : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hminus : 0 < -Real.log (1 - ε) := neg_pos.mpr (Real.log_neg (by linarith) (by linarith))
  have hc : 0 < c := div_pos (lt_min hplus hminus) (by positivity)
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_log_dilation, eventually_log_contraction] with L hp hm
  have hp := hp (1 + ε) (by linarith) (by linarith)
  have hm := hm (1 - ε) (by linarith) (by linarith)
  have hcp : c * L ^ 2 ≤ L ^ 2 / (8 * Real.pi ^ 2) * Real.log (1 + ε) := by
    have h := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (min_le_left (Real.log (1 + ε)) (-Real.log (1 - ε))) (by positivity : 0 ≤ 8 * Real.pi ^ 2))
      (sq_nonneg L)
    dsimp only [c]
    convert h using 1 <;> ring
  have hcm : c * L ^ 2 ≤ L ^ 2 / (8 * Real.pi ^ 2) * (-Real.log (1 - ε)) := by
    have h := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (min_le_right (Real.log (1 + ε)) (-Real.log (1 - ε))) (by positivity : 0 ≤ 8 * Real.pi ^ 2))
      (sq_nonneg L)
    dsimp only [c]
    convert h using 1 <;> ring
  have hF := smallBallReal_pos (Real.exp_pos (-L))
  have hFp := smallBallReal_pos (mul_pos (by linarith : 0 < 1 + ε) (Real.exp_pos (-L)))
  have hFm := smallBallReal_pos (mul_pos (by linarith : 0 < 1 - ε) (Real.exp_pos (-L)))
  constructor
  · have h := Real.exp_le_exp.mpr (show Real.log (smallBallReal (Real.exp (-L))) + c * L ^ 2 ≤
        Real.log (smallBallReal ((1 + ε) * Real.exp (-L))) by linarith)
    simpa only [Real.exp_add, Real.exp_log hF, Real.exp_log hFp] using h
  · have h := Real.exp_le_exp.mpr (show Real.log (smallBallReal ((1 - ε) * Real.exp (-L))) ≤
        Real.log (smallBallReal (Real.exp (-L))) + -c * L ^ 2 by linarith)
    simpa only [Real.exp_add, Real.exp_log hF, Real.exp_log hFm] using h

end Erdos524.SmallBallLogDilation
