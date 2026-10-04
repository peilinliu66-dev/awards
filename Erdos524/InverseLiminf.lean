import Erdos524.InverseLiminfLower

/-! The exact almost-sure inverse-small-ball liminf for the full sign polynomial on [-1,1]. -/

namespace Erdos524.InverseLiminf

open Filter MeasureTheory
open Erdos524.RandomPolynomialModel Erdos524.InversePolynomialScale
open Erdos524.FiniteSmallBallInverse

theorem ae_inverse_normalized_liminf_eq_one :
    ∀ᵐ ω ∂P, liminf (fun N ↦ fullNorm ω N / normalizer (N : ℝ)) atTop = 1 := by
  filter_upwards [Erdos524.InverseLiminfUpper.ae_inverse_normalized_liminf_le_one,
    Erdos524.InverseLiminfLower.ae_inverse_normalized_liminf_ge_one] with ω hu hl
  exact le_antisymm hu hl

theorem ae_explicit_inverse_liminf_eq_one :
    ∀ᵐ ω ∂P, liminf (fun N : ℕ ↦ fullNorm ω N /
      (Real.sqrt (N : ℝ) * smallBallInverse ((Real.sqrt (Real.log (N : ℝ)))⁻¹))) atTop = 1 := by
  filter_upwards [ae_inverse_normalized_liminf_eq_one] with ω hω
  have he : (fun N : ℕ ↦ fullNorm ω N / normalizer (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ ↦ fullNorm ω N / (Real.sqrt (N : ℝ) * smallBallInverse ((Real.sqrt (Real.log (N : ℝ)))⁻¹))) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    unfold normalizer
    rw [delta_exact _ (by exact_mod_cast (show 1 < N by omega))]
  rwa [liminf_congr he] at hω

end Erdos524.InverseLiminf
