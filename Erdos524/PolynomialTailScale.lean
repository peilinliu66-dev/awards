import Erdos524.PolynomialBlockTail

namespace Erdos524.PolynomialTailScale
open MeasureTheory
open Erdos524.PolynomialBlockTail

noncomputable def blockLength (N : ℕ) (T : ℝ) : ℕ := ⌈(N:ℝ)/T⌉₊
noncomputable def tailRadius (N : ℕ) (T : ℝ) : ℝ := Real.exp (-T/(N:ℝ))

theorem blockLength_pos {N : ℕ} (hN : 0<N) {T : ℝ} (hT : 0<T) : 0<blockLength N T := by
  unfold blockLength
  apply Nat.ceil_pos.mpr
  positivity

theorem tailRadius_nonneg (N : ℕ) (T : ℝ) : 0≤tailRadius N T := (Real.exp_pos _).le

theorem tailRadius_lt_one {N : ℕ} (hN : 0<N) {T : ℝ} (hT : 0<T) : tailRadius N T<1 := by
  unfold tailRadius
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hT) (by exact_mod_cast hN)

theorem tailRadius_block_power {N : ℕ} (hN : 0<N) {T : ℝ} (hT : 0<T) :
    (tailRadius N T)^(blockLength N T)≤Real.exp (-1) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  unfold tailRadius
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hm : (N:ℝ)/T≤(blockLength N T:ℝ) := Nat.le_ceil _
  have hn := (div_le_iff₀ hT).mp hm
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hNp).mpr
  nlinarith

theorem tailRadius_denominator {N : ℕ} (hN : 0<N) {T : ℝ} (hT : 0<T) :
    (1/2:ℝ)≤1-(tailRadius N T)^(blockLength N T) := by
  have he : Real.exp (-1)≤(1/2:ℝ) := by
    rw [Real.exp_neg]
    have h := Real.add_one_le_exp 1
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    linarith
  linarith [tailRadius_block_power hN hT]

theorem blockLength_upper {N : ℕ} (hN : 0<N) {T : ℝ} (hT : 0<T) (hTN : T≤N) :
    (blockLength N T:ℝ)≤2*(N:ℝ)/T := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hceil := Nat.ceil_lt_add_one (div_nonneg hNp.le hT.le)
  have hlarge : (1:ℝ)≤(N:ℝ)/T := (le_div_iff₀ hT).mpr (by simpa using hTN)
  unfold blockLength
  rw [mul_div_assoc]
  linarith

theorem normalized_tail_budget {N : ℕ} (hN : 0<N) {T : ℝ} (hT : 0<T) (hTN : T≤N) :
    (3*Real.sqrt (blockLength N T:ℝ)/(1-(tailRadius N T)^(blockLength N T)))/Real.sqrt (N:ℝ)≤9/Real.sqrt T := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hSN : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNp
  have hST : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
  have hd := tailRadius_denominator hN hT
  have hm := blockLength_upper hN hT hTN
  have hsM := Real.sq_sqrt (show (0:ℝ)≤(blockLength N T:ℝ) by positivity)
  have hsN := Real.sq_sqrt hNp.le
  have hsT := Real.sq_sqrt hT.le
  have hden : 0<1-(tailRadius N T)^(blockLength N T) := by linarith
  have hb : 3*Real.sqrt (blockLength N T:ℝ)/(1-(tailRadius N T)^(blockLength N T))≤6*Real.sqrt (blockLength N T:ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.sqrt_nonneg (blockLength N T:ℝ)]
  apply (div_le_div_of_nonneg_right hb hSN.le).trans
  apply (div_le_div_iff₀ hSN hST).mpr
  have hmT : (blockLength N T:ℝ)*T≤2*(N:ℝ) := (le_div_iff₀ hT).mp hm
  have hsprod : (Real.sqrt (blockLength N T:ℝ)*Real.sqrt T)^2≤2*(N:ℝ) := by rw [mul_pow,hsM,hsT]; exact hmT
  nlinarith [Real.sqrt_nonneg (blockLength N T:ℝ)]

end Erdos524.PolynomialTailScale
