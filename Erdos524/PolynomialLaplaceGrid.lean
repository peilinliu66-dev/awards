import Erdos524.ExponentialKernelLipschitz
import Mathlib.Tactic

namespace Erdos524.PolynomialLaplaceGrid
open Erdos524.ExponentialKernelLipschitz

noncomputable def normalizedLaplace (N : ℕ) (a : Fin N → ℝ) (u : ℝ) : ℝ :=
  (∑ i : Fin N, a i*Real.exp (-((i.val+1:ℕ):ℝ)/(N:ℝ)*u))/Real.sqrt N

theorem normalizedLaplace_lipschitz {N : ℕ} (hN : 0<N) (a : Fin N → ℝ)
    (ha : ∀ i, |a i|≤1) {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    |normalizedLaplace N a v-normalizedLaplace N a u|≤Real.sqrt N*|v-u| := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hsp : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNp
  have hs := Real.sq_sqrt hNp.le
  have hi (i : Fin N) : 0≤((i.val+1:ℕ):ℝ)/(N:ℝ) ∧ ((i.val+1:ℕ):ℝ)/(N:ℝ)≤1 := by
    constructor
    · positivity
    · apply (div_le_one hNp).mpr
      exact_mod_cast (show i.val+1≤N by omega)
  have he (i : Fin N) :
      |a i*(Real.exp (-((i.val+1:ℕ):ℝ)/(N:ℝ)*v)-Real.exp (-((i.val+1:ℕ):ℝ)/(N:ℝ)*u))|≤|v-u| := by
    rw [abs_mul]
    have hh := exp_negative_lipschitz (hi i).1 hu hv
    simp only [neg_div] at hh ⊢
    have hh' := hh.trans (mul_le_mul_of_nonneg_right (hi i).2 (abs_nonneg (v-u)))
    have hmul := mul_le_mul (ha i) hh' (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    simpa only [one_mul] using hmul
  unfold normalizedLaplace
  rw [← sub_div,← Finset.sum_sub_distrib,abs_div,abs_of_pos hsp]
  apply (div_le_iff₀ hsp).mpr
  calc
    _ ≤ ∑ i : Fin N, |a i*Real.exp (-((i.val+1:ℕ):ℝ)/(N:ℝ)*v)-a i*Real.exp (-((i.val+1:ℕ):ℝ)/(N:ℝ)*u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, |v-u| := Finset.sum_le_sum (fun i _ => by rw [← mul_sub]; exact he i)
    _ = (N:ℝ)*|v-u| := by simp
    _ = Real.sqrt (N:ℝ)^2*|v-u| := by rw [hs]
    _ = _ := by ring

theorem normalizedLaplace_grid_error {N : ℕ} (hN : 0<N) (a : Fin N → ℝ)
    (ha : ∀ i, |a i|≤1) {u v : ℝ} (hu : 0≤u) (hv : 0≤v)
    (hmesh : |v-u|≤1/(N:ℝ)) :
    |normalizedLaplace N a v-normalizedLaplace N a u|≤1/Real.sqrt N := by
  have hb := (normalizedLaplace_lipschitz hN a ha hu hv).trans
    (mul_le_mul_of_nonneg_left hmesh (Real.sqrt_nonneg _))
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hs := Real.sq_sqrt hNp.le
  have he : Real.sqrt (N:ℝ)*(1/(N:ℝ))=1/Real.sqrt N := by
    field_simp
    nlinarith
  rwa [he] at hb

theorem exists_grid_point {N : ℕ} (hN : 0<N) {T u : ℝ} (hu : 0≤u) (huT : u≤T) :
    ∃ j : ℕ, j≤⌈T*(N:ℝ)⌉₊ ∧ 0≤(j:ℝ)/(N:ℝ) ∧ |u-(j:ℝ)/(N:ℝ)|≤1/(N:ℝ) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  let j : ℕ := ⌊u*(N:ℝ)⌋₊
  have hj : (j:ℝ)≤u*(N:ℝ) := Nat.floor_le (mul_nonneg hu hNp.le)
  have hj' : u*(N:ℝ)<(j:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨j,?_,by positivity,?_⟩
  · have ht : T*(N:ℝ)≤(⌈T*(N:ℝ)⌉₊:ℝ) := Nat.le_ceil _
    have hle : (j:ℝ)≤(⌈T*(N:ℝ)⌉₊:ℝ) := hj.trans ((mul_le_mul_of_nonneg_right huT hNp.le).trans ht)
    exact_mod_cast hle
  · have hju : (j:ℝ)/(N:ℝ)≤u := (div_le_iff₀ hNp).mpr hj
    rw [abs_of_nonneg (sub_nonneg.mpr hju)]
    apply (le_div_iff₀ hNp).mpr
    have he : (u-(j:ℝ)/(N:ℝ))*(N:ℝ)=u*(N:ℝ)-(j:ℝ) := by field_simp
    rw [he]
    linarith

end Erdos524.PolynomialLaplaceGrid
