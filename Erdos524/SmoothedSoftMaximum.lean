import Erdos524.SoftMaximumBounds
import Erdos524.SmoothCompositionBounds

namespace Erdos524.SmoothedSoftMaximum
open Erdos524.SoftMaximum Erdos524.SmoothCutoff Erdos524.SmoothCompositionJets

noncomputable def smoothedPath {n : ℕ} (b η r : ℝ) (x v : Fin n → ℝ) (t : ℝ) : ℝ :=
  cutoff ((softPath (b/η) x v t-r)/η)

theorem softPath_contDiff {n : ℕ} (hn : 0<n) (β : ℝ) (x v : Fin n → ℝ) (k : ℕ) :
    ContDiff ℝ k (softPath β x v) := by
  have hz : ContDiff ℝ k (fun t : ℝ => partition β (fun i => x i+t*v i)) := by
    unfold partition
    fun_prop
  unfold softPath softMax
  exact (hz.log (fun t => ne_of_gt (partition_pos hn β _))).div_const β

theorem smoothedPath_contDiff {n : ℕ} (hn : 0<n) (b η r : ℝ) (x v : Fin n → ℝ) (k : ℕ) :
    ContDiff ℝ k (smoothedPath b η r x v) :=
  (cutoff_contDiff k).comp (((softPath_contDiff hn (b/η) x v k).sub contDiff_const).div_const η)

theorem smoothedPath_mem_Icc {n : ℕ} (b η r : ℝ) (x v : Fin n → ℝ) (t : ℝ) :
    smoothedPath b η r x v t ∈ Set.Icc (0:ℝ) 1 := cutoff_mem_Icc _

theorem fourth_derivative_bound {n : ℕ} (hn : 0<n) {b η a C : ℝ}
    (hb : 1≤b) (hη : 0<η) (ha : 0≤a) (hC : 0≤C)
    (hcut : ∀ j : Fin 4, ∀ z : ℝ, ‖iteratedDeriv (j.val+1) cutoff z‖≤C)
    (r : ℝ) (x v : Fin n → ℝ) (hv : ∀ i, |v i|≤a) (t : ℝ) :
    |iteratedDeriv 4 (smoothedPath b η r x v) t|≤75*C*b^3*a^4/η^4 := by
  let β : ℝ := b/η
  have hβ : 0<β := by dsimp [β]; positivity
  let q : ℝ → ℝ := fun s => (softPath β x v s-r)/η
  let q1 : ℝ → ℝ := fun s => directionalMoment β x v 1 s/η
  let q2 : ℝ → ℝ := fun s => softSecond β x v s/η
  let q3 : ℝ → ℝ := fun s => softThird β x v s/η
  let q4 : ℝ → ℝ := fun s => softFourth β x v s/η
  have hq (s : ℝ) : HasDerivAt q (q1 s) s := ((softPath_hasDerivAt hn (ne_of_gt hβ) x v s).sub_const r).div_const η
  have hq1 (s : ℝ) : HasDerivAt q1 (q2 s) s := (softFirst_hasDerivAt hn β x v s).div_const η
  have hq2 (s : ℝ) : HasDerivAt q2 (q3 s) s := (softSecond_hasDerivAt hn β x v s).div_const η
  have hq3 (s : ℝ) : HasDerivAt q3 (q4 s) s := (softThird_hasDerivAt hn β x v s).div_const η
  have hfour := composition_iteratedDeriv_four q q1 q2 q3 q4 hq hq1 hq2 hq3
  change |iteratedDeriv 4 (fun s => cutoff (q s)) t|≤_
  rw [hfour]
  have hc1 : |cutoffJet 1 q t|≤C := by simpa only [cutoffJet,Real.norm_eq_abs] using hcut ⟨0,by decide⟩ (q t)
  have hc2 : |cutoffJet 2 q t|≤C := by simpa only [cutoffJet,Real.norm_eq_abs] using hcut ⟨1,by decide⟩ (q t)
  have hc3 : |cutoffJet 3 q t|≤C := by simpa only [cutoffJet,Real.norm_eq_abs] using hcut ⟨2,by decide⟩ (q t)
  have hc4 : |cutoffJet 4 q t|≤C := by simpa only [cutoffJet,Real.norm_eq_abs] using hcut ⟨3,by decide⟩ (q t)
  have h1 : |q1 t|≤a/η := by
    dsimp [q1]
    rw [abs_div,abs_of_pos hη]
    have hm := directionalMoment_abs_le hn β x v ha hv 1 t
    simp only [pow_one] at hm
    exact div_le_div_of_nonneg_right hm hη.le
  have h2 : |q2 t|≤2*β*a^2/η := by
    dsimp [q2]
    rw [abs_div,abs_of_pos hη]
    exact div_le_div_of_nonneg_right (softSecond_abs_le hn hβ.le ha x v hv t) hη.le
  have h3 : |q3 t|≤6*β^2*a^3/η := by
    dsimp [q3]
    rw [abs_div,abs_of_pos hη]
    exact div_le_div_of_nonneg_right (softThird_abs_le hn hβ.le ha x v hv t) hη.le
  have h4 : |q4 t|≤26*β^3*a^4/η := by
    dsimp [q4]
    rw [abs_div,abs_of_pos hη]
    exact div_le_div_of_nonneg_right (softFourth_abs_le hn hβ.le ha x v hv t) hη.le
  have hcomp := compositionFourth_abs_le q q1 q2 q3 q4 t hC (by positivity) (by positivity)
    (by positivity) (by positivity) hc1 hc2 hc3 hc4 h1 h2 h3 h4
  have he : C*((a/η)^4+6*(a/η)^2*(2*β*a^2/η)+3*(2*β*a^2/η)^2+
      4*(a/η)*(6*β^2*a^3/η)+(26*β^3*a^4/η)) =
      (C*a^4/η^4)*(1+12*b+36*b^2+26*b^3) := by
    dsimp [β]
    field_simp
    <;> ring
  rw [he] at hcomp
  have hpoly : 1+12*b+36*b^2+26*b^3≤75*b^3 := by
    have h2 : b≤b^2 := by nlinarith
    have h3 := mul_nonneg (sq_nonneg b) (by linarith : 0≤b-1)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hpoly (show 0≤C*a^4/η^4 by positivity)
  calc
    _ ≤ _ := hcomp.trans hm
    _ = _ := by ring

end Erdos524.SmoothedSoftMaximum
