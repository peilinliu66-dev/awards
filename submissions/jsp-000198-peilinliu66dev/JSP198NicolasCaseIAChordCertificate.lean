/- Exact finite determinant certificate for the Case I.A endpoint bridge.
Generated case splits only; every identity is proved by ring and every sign
step by ordered-field lemmas. No SAT result is imported into Lean. -/
import JSP198NicolasCaseIASupport
noncomputable section
open Classical Horton
namespace JSP198.Nicolas
theorem ia_nine_point_chord_support_certificate (A R K B a b c z o : Point)
    (h8 : 0 < (orient A K R))
    (h1 : 0 < (orient A B K))
    (h29 : 0 < (orient B K R))
    (h77 : (orient a b z) < 0)
    (h79 : (orient a c z) < 0)
    (h14 : (orient A R a) < 0)
    (h16 : (orient A R c) < 0)
    (h18 : (orient A R z) < 0)
    (h30 : 0 < (orient B K a))
    (h34 : 0 < (orient B K z))
    (h33 : 0 < (orient B K o))
    (h67 : 0 < (orient R a o))
    (h76 : (orient a b o) < 0)
    (h64 : 0 < (orient K o z))
    (h63 : 0 < (orient K c z))
    (h21 : (orient A a o) < 0)
    (h19 : (orient A a b) < 0)
    (h22 : 0 < (orient A a z))
    (h27 : (orient A c z) < 0)
    (n9 : (orient A K a) ≠ 0)
    (n11 : (orient A K c) ≠ 0)
    (n12 : (orient A K o) ≠ 0)
    (n13 : (orient A K z) ≠ 0)
    (n20 : (orient A a c) ≠ 0)
    (n50 : (orient K R a) ≠ 0)
    (n55 : (orient K a b) ≠ 0)
    (n56 : (orient K a c) ≠ 0)
    (n57 : (orient K a o) ≠ 0)
    (n58 : (orient K a z) ≠ 0)
    : False := by
  have eq0 : ((orient A K a)) + -((orient A K z)) + -((orient K a z)) + ((orient A a z)) = 0 := by
    unfold orient
    ring
  have eq1 : ((orient A K a)) + -((orient A K o)) + -((orient K a o)) + ((orient A a o)) = 0 := by
    unfold orient
    ring
  have eq2 : -((orient A K R) * (orient A a c)) + -((orient A R a) * (orient A K c)) + ((orient A R c) * (orient A K a)) = 0 := by
    unfold orient
    ring
  have eq3 : ((orient A R a) * (orient A c z)) + -((orient A R c) * (orient A a z)) + ((orient A R z) * (orient A a c)) = 0 := by
    unfold orient
    ring
  have eq4 : ((orient A K R) * (orient B K a)) + -((orient A B K) * (orient K R a)) + -((orient A K a) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq5 : -((orient A B K) * (orient K o z)) + -((orient A K z) * (orient B K o)) + ((orient A K o) * (orient B K z)) = 0 := by
    unfold orient
    ring
  have eq6 : ((orient A K a) * (orient K o z)) + ((orient A K z) * (orient K a o)) + -((orient A K o) * (orient K a z)) = 0 := by
    unfold orient
    ring
  have eq7 : -((orient A R a) * (orient K a o)) + ((orient A K a) * (orient R a o)) + ((orient A a o) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq8 : ((orient A K a) * (orient a b z)) + -((orient A a b) * (orient K a z)) + ((orient A a z) * (orient K a b)) = 0 := by
    unfold orient
    ring
  have eq9 : ((orient A K a) * (orient a b o)) + -((orient A a b) * (orient K a o)) + ((orient A a o) * (orient K a b)) = 0 := by
    unfold orient
    ring
  have eq10 : ((orient A K a) * (orient a c z)) + -((orient A a c) * (orient K a z)) + ((orient A a z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have eq11 : -((orient A K c) * (orient a c z)) + ((orient A a c) * (orient K c z)) + -((orient A c z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have s0 : 0 < (orient A a c) := by
    by_contra hn
    have s0n : (orient A a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n20
    have p1 : 0 < (orient A R a) * (orient A c z) := mul_pos_of_neg_of_neg h14 h27
    have p2 : (orient A R c) * (orient A a z) < 0 := mul_neg_of_neg_of_pos h16 h22
    have p3 : 0 < (orient A R z) * (orient A a c) := mul_pos_of_neg_of_neg h18 s0n
    linarith only [eq3, p1, p2, p3]
  by_cases s4 : 0 < (orient A K a)
  ·
    have s5 : 0 < (orient A K c) := by
      by_contra hn
      have s5n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n11
      have p6 : 0 < (orient A K R) * (orient A a c) := mul_pos h8 s0
      have p7 : 0 < (orient A R a) * (orient A K c) := mul_pos_of_neg_of_neg h14 s5n
      have p8 : (orient A R c) * (orient A K a) < 0 := mul_neg_of_neg_of_pos h16 s4
      linarith only [eq2, p6, p7, p8]
    have s9 : (orient K a c) < 0 := by
      by_contra hn
      have s9n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
      have p10 : (orient A K c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s5 h79
      have p11 : 0 < (orient A a c) * (orient K c z) := mul_pos s0 h63
      have p12 : (orient A c z) * (orient K a c) < 0 := mul_neg_of_neg_of_pos h27 s9n
      linarith only [eq11, p10, p11, p12]
    have s13 : (orient K a z) < 0 := by
      by_contra hn
      have s13n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
      have p14 : (orient A K a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s4 h79
      have p15 : 0 < (orient A a c) * (orient K a z) := mul_pos s0 s13n
      have p16 : (orient A a z) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h22 s9
      linarith only [eq10, p14, p15, p16]
    have s17 : 0 < (orient A K z) := by
      by_contra hn
      have s17n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
      linarith only [eq0, s4, s17n, s13, h22]
    have s18 : 0 < (orient A K o) := by
      by_contra hn
      have s18n : (orient A K o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n12
      have p19 : 0 < (orient A B K) * (orient K o z) := mul_pos h1 h64
      have p20 : 0 < (orient A K z) * (orient B K o) := mul_pos s17 h33
      have p21 : (orient A K o) * (orient B K z) < 0 := mul_neg_of_neg_of_pos s18n h34
      linarith only [eq5, p19, p20, p21]
    have s22 : (orient K a o) < 0 := by
      by_contra hn
      have s22n : 0 < (orient K a o) := lt_of_le_of_ne (le_of_not_gt hn) n57.symm
      have p23 : 0 < (orient A K a) * (orient K o z) := mul_pos s4 h64
      have p24 : 0 < (orient A K z) * (orient K a o) := mul_pos s17 s22n
      have p25 : (orient A K o) * (orient K a z) < 0 := mul_neg_of_pos_of_neg s18 s13
      linarith only [eq6, p23, p24, p25]
    have s26 : 0 < (orient K a b) := by
      by_contra hn
      have s26n : (orient K a b) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n55
      have p27 : (orient A K a) * (orient a b z) < 0 := mul_neg_of_pos_of_neg s4 h77
      have p28 : 0 < (orient A a b) * (orient K a z) := mul_pos_of_neg_of_neg h19 s13
      have p29 : (orient A a z) * (orient K a b) < 0 := mul_neg_of_pos_of_neg h22 s26n
      linarith only [eq8, p27, p28, p29]
    have p30 : (orient A K a) * (orient a b o) < 0 := mul_neg_of_pos_of_neg s4 h76
    have p31 : 0 < (orient A a b) * (orient K a o) := mul_pos_of_neg_of_neg h19 s22
    have p32 : (orient A a o) * (orient K a b) < 0 := mul_neg_of_neg_of_pos h21 s26
    linarith only [eq9, p30, p31, p32]
  · have s4n : (orient A K a) < 0 := lt_of_le_of_ne (le_of_not_gt s4) n9
    have s33 : 0 < (orient K R a) := by
      by_contra hn
      have s33n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
      have p34 : 0 < (orient A K R) * (orient B K a) := mul_pos h8 h30
      have p35 : (orient A B K) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h1 s33n
      have p36 : (orient A K a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s4n h29
      linarith only [eq4, p34, p35, p36]
    have s37 : 0 < (orient K a o) := by
      by_contra hn
      have s37n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
      have p38 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s37n
      have p39 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s4n h67
      have p40 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s33
      linarith only [eq7, p38, p39, p40]
    have s41 : 0 < (orient K a b) := by
      by_contra hn
      have s41n : (orient K a b) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n55
      have p42 : 0 < (orient A K a) * (orient a b o) := mul_pos_of_neg_of_neg s4n h76
      have p43 : (orient A a b) * (orient K a o) < 0 := mul_neg_of_neg_of_pos h19 s37
      have p44 : 0 < (orient A a o) * (orient K a b) := mul_pos_of_neg_of_neg h21 s41n
      linarith only [eq9, p42, p43, p44]
    have s45 : (orient A K o) < 0 := by
      by_contra hn
      have s45n : 0 < (orient A K o) := lt_of_le_of_ne (le_of_not_gt hn) n12.symm
      linarith only [eq1, s4n, s45n, s37, h21]
    have s46 : (orient A K z) < 0 := by
      by_contra hn
      have s46n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
      have p47 : 0 < (orient A B K) * (orient K o z) := mul_pos h1 h64
      have p48 : 0 < (orient A K z) * (orient B K o) := mul_pos s46n h33
      have p49 : (orient A K o) * (orient B K z) < 0 := mul_neg_of_neg_of_pos s45 h34
      linarith only [eq5, p47, p48, p49]
    have s50 : 0 < (orient K a z) := by
      by_contra hn
      have s50n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
      have p51 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s4n h64
      have p52 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s46 s37
      have p53 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s45 s50n
      linarith only [eq6, p51, p52, p53]
    have p54 : 0 < (orient A K a) * (orient a b z) := mul_pos_of_neg_of_neg s4n h77
    have p55 : (orient A a b) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h19 s50
    have p56 : 0 < (orient A a z) * (orient K a b) := mul_pos h22 s41
    linarith only [eq8, p54, p55, p56]
end JSP198.Nicolas
#print axioms JSP198.Nicolas.ia_nine_point_chord_support_certificate
