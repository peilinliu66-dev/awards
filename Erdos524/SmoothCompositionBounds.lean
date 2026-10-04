import Erdos524.SmoothCompositionJets

namespace Erdos524.SmoothCompositionJets

 theorem abs_sum_five_le (a b c d e : ℝ) :
    |a+b+c+d+e|≤|a|+|b|+|c|+|d|+|e| := by
  calc
    _ ≤ |a+b+c+d|+|e| := abs_add_le _ _
    _ ≤ (|a+b+c|+|d|)+|e| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|a+b|+|c|)+|d|)+|e| := by gcongr; exact abs_add_le _ _
    _ ≤ (((|a|+|b|)+|c|)+|d|)+|e| := by gcongr; exact abs_add_le _ _
    _ = _ := by ring

theorem compositionFourth_abs_le (q q1 q2 q3 q4 : ℝ → ℝ) (t : ℝ)
    {C U1 U2 U3 U4 : ℝ} (hC : 0≤C) (hU1 : 0≤U1) (hU2 : 0≤U2) (hU3 : 0≤U3) (hU4 : 0≤U4)
    (hc1 : |cutoffJet 1 q t|≤C) (hc2 : |cutoffJet 2 q t|≤C)
    (hc3 : |cutoffJet 3 q t|≤C) (hc4 : |cutoffJet 4 q t|≤C)
    (h1 : |q1 t|≤U1) (h2 : |q2 t|≤U2) (h3 : |q3 t|≤U3) (h4 : |q4 t|≤U4) :
    |compositionFourth q q1 q2 q3 q4 t|≤C*(U1^4+6*U1^2*U2+3*U2^2+4*U1*U3+U4) := by
  unfold compositionFourth
  have h := abs_sum_five_le (cutoffJet 4 q t*(q1 t)^4) (6*cutoffJet 3 q t*(q1 t)^2*q2 t)
    (3*cutoffJet 2 q t*(q2 t)^2) (4*cutoffJet 2 q t*q1 t*q3 t) (cutoffJet 1 q t*q4 t)
  simp only [abs_mul,abs_pow] at h
  norm_num only at h
  calc
    _ ≤ |cutoffJet 4 q t| * |q1 t|^4+6*|cutoffJet 3 q t| * |q1 t|^2*|q2 t|+
        3*|cutoffJet 2 q t| * |q2 t|^2+4*|cutoffJet 2 q t| * |q1 t| * |q3 t|+|cutoffJet 1 q t| * |q4 t| := by
      simpa only [sq_abs] using h
    _ ≤ C*U1^4+6*C*U1^2*U2+3*C*U2^2+4*C*U1*U3+C*U4 := by gcongr
    _ = _ := by ring

end Erdos524.SmoothCompositionJets
