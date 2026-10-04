import Erdos524.EnvelopeBlocking
import Erdos524.InverseSmallBallMargins
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Even factorial-square blocks: exact ratios, parity, growth and logarithmic size. -/

namespace Erdos524.FactorialSparseMesh

open Filter

/-- The shift avoids the repeated initial values 0! = 1!. -/
def endpoint (j : ℕ) : ℕ := 2 * ((j + 1).factorial) ^ 2

def blockLength (j : ℕ) : ℕ := endpoint (j + 1) - endpoint j

theorem endpoint_pos (j : ℕ) : 0 < endpoint j := by unfold endpoint; positivity

theorem endpoint_succ (j : ℕ) : endpoint (j + 1) = (j + 2) ^ 2 * endpoint j := by
  simp only [endpoint, Nat.factorial_succ (j + 1)]
  ring

theorem endpoint_strictMono : StrictMono endpoint := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [endpoint_succ]
  have he := endpoint_pos j
  have hp : 1 < (j + 2) ^ 2 := by
    have h : 2 ≤ j + 2 := by omega
    have hpow := Nat.pow_le_pow_left h 2
    omega
  nlinarith

theorem blockLength_identity (j : ℕ) : blockLength j = ((j + 2) ^ 2 - 1) * endpoint j := by
  unfold blockLength
  rw [endpoint_succ, Nat.sub_mul, one_mul]

theorem blockLength_pos (j : ℕ) : 0 < blockLength j := by
  unfold blockLength
  exact Nat.sub_pos_of_lt (endpoint_strictMono (Nat.lt_succ_self j))

theorem endpoint_even (j : ℕ) : Even (endpoint j) := by
  exact ⟨((j + 1).factorial) ^ 2, by unfold endpoint; omega⟩

theorem blockLength_even (j : ℕ) : Even (blockLength j) := by
  rw [blockLength_identity]
  exact (endpoint_even j).mul_left _

theorem endpoint_ratio (j : ℕ) : (endpoint j : ℝ) / endpoint (j + 1) = 1 / (j + 2 : ℝ) ^ 2 := by
  rw [endpoint_succ]
  push_cast
  have he : (endpoint j : ℝ) ≠ 0 := by exact_mod_cast (endpoint_pos j).ne'
  field_simp

theorem blockLength_ratio (j : ℕ) : (blockLength j : ℝ) / endpoint (j + 1) = 1 - 1 / (j + 2 : ℝ) ^ 2 := by
  unfold blockLength
  rw [Nat.cast_sub (endpoint_strictMono.monotone (Nat.le_succ j)), sub_div,
    div_self (by exact_mod_cast (endpoint_pos (j + 1)).ne'), endpoint_ratio]

theorem endpoint_lower (j : ℕ) : 2 * (j + 1) ^ 2 ≤ endpoint j := by
  have h := Nat.self_le_factorial (j + 1)
  unfold endpoint
  nlinarith

theorem endpoint_log_upper (j : ℕ) :
    Real.log (endpoint j : ℝ) ≤ Real.log 2 + 2 * (j + 1 : ℝ) * Real.log (j + 1 : ℝ) := by
  have hj : 0 < (j + 1 : ℝ) := by positivity
  have hf : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos (j + 1)
  have hbound : ((j + 1).factorial : ℝ) ≤ (j + 1 : ℝ) ^ (j + 1) := by
    exact_mod_cast Nat.factorial_le_pow (j + 1)
  have hlog := Real.log_le_log hf hbound
  rw [Real.log_pow] at hlog
  simp only [endpoint, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hf 2).ne', Real.log_pow]
  push_cast at hlog
  nlinarith

theorem endpoint_tendsto_atTop : Tendsto endpoint atTop atTop := endpoint_strictMono.tendsto_atTop

theorem endpoint_real_tendsto_atTop : Tendsto (fun j ↦ (endpoint j : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp endpoint_tendsto_atTop

theorem blockLength_lower (j : ℕ) : endpoint j ≤ blockLength j := by
  rw [blockLength_identity]
  have he := endpoint_pos j
  have hp : 2 ≤ (j + 2) ^ 2 := by
    have h : 2 ≤ j + 2 := by omega
    have hpow := Nat.pow_le_pow_left h 2
    omega
  have hsub : 1 ≤ (j + 2) ^ 2 - 1 := by omega
  nlinarith

theorem blockLength_tendsto_atTop : Tendsto blockLength atTop atTop :=
  tendsto_atTop_mono blockLength_lower endpoint_tendsto_atTop

theorem blockLength_real_tendsto_atTop : Tendsto (fun j ↦ (blockLength j : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp blockLength_tendsto_atTop

end Erdos524.FactorialSparseMesh
