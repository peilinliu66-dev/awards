import Erdos524.TwoSidedStepGram

namespace Erdos524.ParityPowerSum
open Erdos524.TwoSidedStepGram

theorem power_even {σ : ℝ} (hσ : σ^2=1) (k : ℕ) : σ^(2*k)=1 := by rw [pow_mul,hσ,one_pow]
theorem power_odd {σ : ℝ} (hσ : σ^2=1) (k : ℕ) : σ^(2*k+1)=σ := by rw [pow_succ,power_even hσ,one_mul]

theorem parity_exponential_sum {M : ℕ} (hM : 0<M) {σ τ : ℝ} (hσ : σ^2=1) (hτ : τ^2=1) (u v : ℝ) :
    (∑ i : Fin (2*M), σ^(i.val+1)*τ^(i.val+1)*
      Real.exp (-u*((i.val+1:ℕ):ℝ)/(2*(M:ℝ)))*Real.exp (-v*((i.val+1:ℕ):ℝ)/(2*(M:ℝ))))=
    σ*τ*(∑ k : Fin M, Real.exp (-u*((k:ℝ)+1/2)/(M:ℝ))*Real.exp (-v*((k:ℝ)+1/2)/(M:ℝ)))+
      (∑ k : Fin M, Real.exp (-u*((k:ℝ)+1)/(M:ℝ))*Real.exp (-v*((k:ℝ)+1)/(M:ℝ))) := by
  let f : ℕ → ℝ := fun i => σ^(i+1)*τ^(i+1)*Real.exp (-u*((i+1:ℕ):ℝ)/(2*(M:ℝ)))*Real.exp (-v*((i+1:ℕ):ℝ)/(2*(M:ℝ)))
  let g : ℕ → ℝ := fun k => Real.exp (-u*((k:ℝ)+1/2)/(M:ℝ))*Real.exp (-v*((k:ℝ)+1/2)/(M:ℝ))
  let h : ℕ → ℝ := fun k => Real.exp (-u*((k:ℝ)+1)/(M:ℝ))*Real.exp (-v*((k:ℝ)+1)/(M:ℝ))
  change (∑ i : Fin (2*M), f i.val)=σ*τ*(∑ k : Fin M, g k.val)+(∑ k : Fin M, h k.val)
  rw [Fin.sum_univ_eq_sum_range f,Fin.sum_univ_eq_sum_range g,Fin.sum_univ_eq_sum_range h,sum_range_even_odd]
  dsimp only [f,g,h]
  rw [Finset.mul_sum]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro k hk
    rw [power_odd hσ,power_odd hτ]
    have he (a : ℝ) : -a*((2*k+1:ℕ):ℝ)/(2*(M:ℝ))=-a*((k:ℝ)+1/2)/(M:ℝ) := by push_cast; field_simp <;> ring
    rw [he u,he v]
    ring
  · apply Finset.sum_congr rfl
    intro k hk
    rw [show 2*k+1+1=2*(k+1) by omega,power_even hσ,power_even hτ]
    have he (a : ℝ) : -a*((2*(k+1):ℕ):ℝ)/(2*(M:ℝ))=-a*((k:ℝ)+1)/(M:ℝ) := by push_cast; field_simp <;> ring
    rw [he u,he v]
    ring

end Erdos524.ParityPowerSum
