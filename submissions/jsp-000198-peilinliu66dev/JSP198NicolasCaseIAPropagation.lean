/- Exact finite determinant certificate for the Case I.A endpoint bridge.
Generated case splits only; every identity is proved by ring and every sign
step by ordered-field lemmas. No SAT result is imported into Lean. -/
import JSP198NicolasCaseIASupport
noncomputable section
open Classical Horton
namespace JSP198.Nicolas
theorem ia_arc_support_propagation_certificate (A a b x y c z : Point)
    (h18 : (orient a b y) < 0)
    (h16 : (orient a b c) < 0)
    (h19 : (orient a b z) < 0)
    (h23 : (orient a x y) < 0)
    (h20 : 0 < (orient a c x))
    (h24 : (orient a x z) < 0)
    (h25 : (orient a y z) < 0)
    (h22 : (orient a c z) < 0)
    (h35 : (orient x y z) < 0)
    (h33 : 0 < (orient c x z))
    (h1 : (orient A a b) < 0)
    (h12 : (orient A c z) < 0)
    (h5 : (orient A a z) < 0)
    (h13 : 0 < (orient A x y))
    (n2 : (orient A a c) ≠ 0)
    (n3 : (orient A a x) ≠ 0)
    (n4 : (orient A a y) ≠ 0)
    (n10 : (orient A c x) ≠ 0)
    (n14 : (orient A x z) ≠ 0)
    : False := by
  have eq0 : ((orient A a x)) + -((orient A a y)) + -((orient a x y)) + ((orient A x y)) = 0 := by
    unfold orient
    ring
  have eq1 : ((orient A a x) * (orient A c z)) + -((orient A a c) * (orient A x z)) + -((orient A a z) * (orient A c x)) = 0 := by
    unfold orient
    ring
  have eq2 : -((orient A a b) * (orient a y z)) + ((orient A a y) * (orient a b z)) + -((orient A a z) * (orient a b y)) = 0 := by
    unfold orient
    ring
  have eq3 : -((orient A a b) * (orient a c z)) + ((orient A a c) * (orient a b z)) + -((orient A a z) * (orient a b c)) = 0 := by
    unfold orient
    ring
  have eq4 : ((orient A a x) * (orient x y z)) + -((orient A x y) * (orient a x z)) + ((orient A x z) * (orient a x y)) = 0 := by
    unfold orient
    ring
  have eq5 : ((orient A a c) * (orient c x z)) + -((orient A c x) * (orient a c z)) + ((orient A c z) * (orient a c x)) = 0 := by
    unfold orient
    ring
  have s0 : (orient A a y) < 0 := by
    by_contra hn
    have s0n : 0 < (orient A a y) := lt_of_le_of_ne (le_of_not_gt hn) n4.symm
    have p1 : 0 < (orient A a b) * (orient a y z) := mul_pos_of_neg_of_neg h1 h25
    have p2 : (orient A a y) * (orient a b z) < 0 := mul_neg_of_pos_of_neg s0n h19
    have p3 : 0 < (orient A a z) * (orient a b y) := mul_pos_of_neg_of_neg h5 h18
    linarith only [eq2, p1, p2, p3]
  have s4 : (orient A a c) < 0 := by
    by_contra hn
    have s4n : 0 < (orient A a c) := lt_of_le_of_ne (le_of_not_gt hn) n2.symm
    have p5 : 0 < (orient A a b) * (orient a c z) := mul_pos_of_neg_of_neg h1 h22
    have p6 : (orient A a c) * (orient a b z) < 0 := mul_neg_of_pos_of_neg s4n h19
    have p7 : 0 < (orient A a z) * (orient a b c) := mul_pos_of_neg_of_neg h5 h16
    linarith only [eq3, p5, p6, p7]
  have s8 : 0 < (orient A c x) := by
    by_contra hn
    have s8n : (orient A c x) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n10
    have p9 : (orient A a c) * (orient c x z) < 0 := mul_neg_of_neg_of_pos s4 h33
    have p10 : 0 < (orient A c x) * (orient a c z) := mul_pos_of_neg_of_neg s8n h22
    have p11 : (orient A c z) * (orient a c x) < 0 := mul_neg_of_neg_of_pos h12 h20
    linarith only [eq5, p9, p10, p11]
  have s12 : (orient A a x) < 0 := by
    by_contra hn
    have s12n : 0 < (orient A a x) := lt_of_le_of_ne (le_of_not_gt hn) n3.symm
    linarith only [eq0, s12n, s0, h23, h13]
  have s13 : (orient A x z) < 0 := by
    by_contra hn
    have s13n : 0 < (orient A x z) := lt_of_le_of_ne (le_of_not_gt hn) n14.symm
    have p14 : 0 < (orient A a x) * (orient A c z) := mul_pos_of_neg_of_neg s12 h12
    have p15 : (orient A a c) * (orient A x z) < 0 := mul_neg_of_neg_of_pos s4 s13n
    have p16 : (orient A a z) * (orient A c x) < 0 := mul_neg_of_neg_of_pos h5 s8
    linarith only [eq1, p14, p15, p16]
  have p17 : 0 < (orient A a x) * (orient x y z) := mul_pos_of_neg_of_neg s12 h35
  have p18 : (orient A x y) * (orient a x z) < 0 := mul_neg_of_pos_of_neg h13 h24
  have p19 : 0 < (orient A x z) * (orient a x y) := mul_pos_of_neg_of_neg s13 h23
  linarith only [eq4, p17, p18, p19]
end JSP198.Nicolas
#print axioms JSP198.Nicolas.ia_arc_support_propagation_certificate
