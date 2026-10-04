import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Erdos524.DyadicMesh

noncomputable def point (k Q j : ℕ) : ℕ := 2*(2^k+(j*2^k)/Q)

theorem point_zero (k Q : ℕ) : point k Q 0=2*2^k := by simp [point]
theorem point_end (k Q : ℕ) (hQ : 0<Q) : point k Q Q=4*2^k := by simp [point,Nat.mul_div_right _ hQ]; omega

theorem point_even (k Q j : ℕ) : Even (point k Q j) := ⟨2^k+(j*2^k)/Q,by unfold point; omega⟩
theorem point_lower (k Q j : ℕ) : 2*2^k≤point k Q j := by
  unfold point
  exact Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)

theorem point_monotone (k Q : ℕ) : Monotone (point k Q) := by
  intro i j hij
  have hd := Nat.div_le_div_right (Nat.mul_le_mul_right (2^k) hij) (c := Q)
  unfold point
  omega

theorem point_step_bound (k Q j : ℕ) : point k Q (j+1)≤point k Q j+2*(2^k/Q+1) := by
  have h := Nat.add_div_le_div_add_div_add_one (j*2^k) (2^k) Q
  have he : (j+1)*2^k=j*2^k+2^k := by ring
  unfold point
  rw [he]
  omega

theorem point_step_ratio_nat (k Q j : ℕ) (hQ : Q≤2^k) :
    point k Q (j+1)*Q≤point k Q j*(Q+2) := by
  have hs := Nat.mul_le_mul_right Q (point_step_bound k Q j)
  have hd := Nat.div_mul_le_self (2^k) Q
  have hlo := point_lower k Q j
  nlinarith

theorem point_step_ratio (k Q j : ℕ) (hQ0 : 0<Q) (hQ : Q≤2^k) :
    (point k Q (j+1):ℝ)≤(1+2/(Q:ℝ))*(point k Q j:ℝ) := by
  have hp : (0:ℝ)<Q := by exact_mod_cast hQ0
  have h : (point k Q (j+1):ℝ)*(Q:ℝ)≤(point k Q j:ℝ)*((Q:ℝ)+2) := by exact_mod_cast point_step_ratio_nat k Q j hQ
  apply (le_of_mul_le_mul_right ?_ hp)
  have he : ((1+2/(Q:ℝ))*(point k Q j:ℝ))*(Q:ℝ)=(point k Q j:ℝ)*((Q:ℝ)+2) := by field_simp <;> ring
  rwa [he]

theorem point_cover (k Q n : ℕ) (hlo : 2*2^k≤n) (hhi : n<4*2^k) (hQ : 0<Q) :
    ∃ j, j<Q ∧ point k Q j≤n ∧ n<point k Q (j+1) := by
  have hex : ∃ i, n<point k Q i := ⟨Q,by rwa [point_end k Q hQ]⟩
  let i := Nat.find hex
  have hi : n<point k Q i := Nat.find_spec hex
  have hiQ : i≤Q := Nat.find_min' hex (by rwa [point_end k Q hQ])
  have hi0 : 0 < i := by
    by_contra h
    have he : i=0 := by omega
    rw [he,point_zero] at hi
    omega
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hi0)
  refine ⟨j,by omega,?_,by simpa only [hj,Nat.succ_eq_add_one] using hi⟩
  exact le_of_not_gt (Nat.find_min hex (show j<Nat.find hex by change j < i; omega))

theorem point_gap_bound (k Q j : ℕ) : point k Q (j+1)-point k Q j≤2*(2^k/Q+1) := by
  have h := point_step_bound k Q j
  omega

theorem band_cover (n : ℕ) (hn : 2≤n) : ∃ k, 2*2^k≤n ∧ n<4*2^k := by
  have hlog : 0<Nat.log 2 n := Nat.log_pos (by norm_num) hn
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hlog)
  have hlo := Nat.pow_log_le_self 2 (by omega : n≠0)
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1<2) n
  rw [hk] at hlo hhi
  refine ⟨k,?_,?_⟩
  · simpa only [pow_succ,mul_comm] using hlo
  · have he : 2^(k+1+1)=4*2^k := by ring
    simpa only [Nat.succ_eq_add_one,he] using hhi

theorem cover_after (Q : ℕ → ℕ) (hQ : ∀ k, 0<Q k) (K n : ℕ) (hn : 4*2^K≤n) :
    ∃ k, K≤k ∧ ∃ j, j<Q k ∧ point k (Q k) j≤n ∧ n<point k (Q k) (j+1) := by
  have hp : 1≤2^K := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨k,hlo,hhi⟩ := band_cover n (by omega)
  have hk : K≤k := by
    by_contra h
    have hkk : k≤K := by omega
    have hpow : 2^k≤2^K := by gcongr
    omega
  obtain ⟨j,hj,hjl,hjr⟩ := point_cover k (Q k) n hlo hhi (hQ k)
  exact ⟨k,hk,j,hj,hjl,hjr⟩

theorem index_le_two_pow (k : ℕ) : k≤2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hp : 1≤2^k := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

end Erdos524.DyadicMesh
