/- Exact finite determinant certificate for the Case I.A endpoint bridge.
Generated case splits only; every identity is proved by ring and every sign
step by ordered-field lemmas. No SAT result is imported into Lean. -/
import JSP198NicolasCaseIASupport
noncomputable section
open Classical Horton
namespace JSP198.Nicolas
theorem ia_nine_point_end_support_certificate (A R K B a b c z o : Point)
    (h8 : 0 < (orient A K R))
    (h2 : 0 < (orient A B R))
    (h1 : 0 < (orient A B K))
    (h29 : 0 < (orient B K R))
    (h77 : (orient a b z) < 0)
    (h79 : (orient a c z) < 0)
    (h14 : (orient A R a) < 0)
    (h16 : (orient A R c) < 0)
    (h18 : (orient A R z) < 0)
    (h30 : 0 < (orient B K a))
    (h32 : 0 < (orient B K c))
    (h67 : 0 < (orient R a o))
    (h65 : 0 < (orient R a b))
    (h64 : 0 < (orient K o z))
    (h63 : 0 < (orient K c z))
    (h21 : (orient A a o) < 0)
    (h19 : (orient A a b) < 0)
    (h48 : (orient B c z) < 0)
    (h27 : 0 < (orient A c z))
    (n5 : (orient A B c) ≠ 0)
    (n9 : (orient A K a) ≠ 0)
    (n11 : (orient A K c) ≠ 0)
    (n12 : (orient A K o) ≠ 0)
    (n13 : (orient A K z) ≠ 0)
    (n20 : (orient A a c) ≠ 0)
    (n22 : (orient A a z) ≠ 0)
    (n50 : (orient K R a) ≠ 0)
    (n52 : (orient K R c) ≠ 0)
    (n54 : (orient K R z) ≠ 0)
    (n56 : (orient K a c) ≠ 0)
    (n57 : (orient K a o) ≠ 0)
    (n58 : (orient K a z) ≠ 0)
    (n68 : (orient R a z) ≠ 0)
    : False := by
  have eq0 : ((orient A K a)) + -((orient A K o)) + -((orient K a o)) + ((orient A a o)) = 0 := by
    unfold orient
    ring
  have eq1 : ((orient A a c)) + -((orient A a z)) + -((orient a c z)) + ((orient A c z)) = 0 := by
    unfold orient
    ring
  have eq2 : -((orient A K R) * (orient A B c)) + ((orient A B R) * (orient A K c)) + -((orient A R c) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq3 : -((orient A K R) * (orient A a c)) + -((orient A R a) * (orient A K c)) + ((orient A R c) * (orient A K a)) = 0 := by
    unfold orient
    ring
  have eq4 : ((orient A K R) * (orient R a z)) + -((orient A R a) * (orient K R z)) + ((orient A R z) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq5 : ((orient A K R) * (orient B K a)) + -((orient A B K) * (orient K R a)) + -((orient A K a) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq6 : ((orient A K R) * (orient B K c)) + -((orient A B K) * (orient K R c)) + -((orient A K c) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq7 : -((orient A K R) * (orient K c z)) + ((orient A K c) * (orient K R z)) + -((orient A K z) * (orient K R c)) = 0 := by
    unfold orient
    ring
  have eq8 : ((orient A B K) * (orient K a c)) + -((orient A K a) * (orient B K c)) + ((orient A K c) * (orient B K a)) = 0 := by
    unfold orient
    ring
  have eq9 : ((orient A K a) * (orient K o z)) + ((orient A K z) * (orient K a o)) + -((orient A K o) * (orient K a z)) = 0 := by
    unfold orient
    ring
  have eq10 : -((orient A R a) * (orient K a z)) + ((orient A K a) * (orient R a z)) + ((orient A a z) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq11 : -((orient A R a) * (orient K a o)) + ((orient A K a) * (orient R a o)) + ((orient A a o) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq12 : ((orient A R a) * (orient a b z)) + -((orient A a b) * (orient R a z)) + ((orient A a z) * (orient R a b)) = 0 := by
    unfold orient
    ring
  have eq13 : ((orient A K a) * (orient a c z)) + -((orient A a c) * (orient K a z)) + ((orient A a z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have eq14 : -((orient A K c) * (orient B c z)) + ((orient A B c) * (orient K c z)) + ((orient A c z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq15 : -((orient A K c) * (orient a c z)) + ((orient A a c) * (orient K c z)) + -((orient A c z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  by_cases s0 : 0 < (orient A K a)
  ·
    by_cases s1 : 0 < (orient K a z)
    ·
      by_cases s2 : 0 < (orient A K c)
      ·
        have s3 : 0 < (orient A B c) := by
          by_contra hn
          have s3n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
          have p4 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s3n
          have p5 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s2
          have p6 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
          linarith only [eq2, p4, p5, p6]
        have p7 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s2 h48
        have p8 : 0 < (orient A B c) * (orient K c z) := mul_pos s3 h63
        have p9 : 0 < (orient A c z) * (orient B K c) := mul_pos h27 h32
        linarith only [eq14, p7, p8, p9]
      · have s2n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt s2) n11
        have s10 : (orient A a c) < 0 := by
          by_contra hn
          have s10n : 0 < (orient A a c) := lt_of_le_of_ne (le_of_not_gt hn) n20.symm
          have p11 : 0 < (orient A K R) * (orient A a c) := mul_pos h8 s10n
          have p12 : 0 < (orient A R a) * (orient A K c) := mul_pos_of_neg_of_neg h14 s2n
          have p13 : (orient A R c) * (orient A K a) < 0 := mul_neg_of_neg_of_pos h16 s0
          linarith only [eq3, p11, p12, p13]
        have s14 : 0 < (orient K R c) := by
          by_contra hn
          have s14n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
          have p15 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
          have p16 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s14n
          have p17 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s2n h29
          linarith only [eq6, p15, p16, p17]
        have s18 : 0 < (orient K a c) := by
          by_contra hn
          have s18n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
          have p19 : (orient A B K) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h1 s18n
          have p20 : 0 < (orient A K a) * (orient B K c) := mul_pos s0 h32
          have p21 : (orient A K c) * (orient B K a) < 0 := mul_neg_of_neg_of_pos s2n h30
          linarith only [eq8, p19, p20, p21]
        have p22 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s2n h79
        have p23 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s10 h63
        have p24 : 0 < (orient A c z) * (orient K a c) := mul_pos h27 s18
        linarith only [eq15, p22, p23, p24]
    · have s1n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt s1) n58
      by_cases s25 : 0 < (orient A K c)
      ·
        have s26 : 0 < (orient A B c) := by
          by_contra hn
          have s26n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
          have p27 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s26n
          have p28 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s25
          have p29 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
          linarith only [eq2, p27, p28, p29]
        have p30 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s25 h48
        have p31 : 0 < (orient A B c) * (orient K c z) := mul_pos s26 h63
        have p32 : 0 < (orient A c z) * (orient B K c) := mul_pos h27 h32
        linarith only [eq14, p30, p31, p32]
      · have s25n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt s25) n11
        have s33 : (orient A a c) < 0 := by
          by_contra hn
          have s33n : 0 < (orient A a c) := lt_of_le_of_ne (le_of_not_gt hn) n20.symm
          have p34 : 0 < (orient A K R) * (orient A a c) := mul_pos h8 s33n
          have p35 : 0 < (orient A R a) * (orient A K c) := mul_pos_of_neg_of_neg h14 s25n
          have p36 : (orient A R c) * (orient A K a) < 0 := mul_neg_of_neg_of_pos h16 s0
          linarith only [eq3, p34, p35, p36]
        have s37 : 0 < (orient K R c) := by
          by_contra hn
          have s37n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
          have p38 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
          have p39 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s37n
          have p40 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s25n h29
          linarith only [eq6, p38, p39, p40]
        have s41 : 0 < (orient K a c) := by
          by_contra hn
          have s41n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
          have p42 : (orient A B K) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h1 s41n
          have p43 : 0 < (orient A K a) * (orient B K c) := mul_pos s0 h32
          have p44 : (orient A K c) * (orient B K a) < 0 := mul_neg_of_neg_of_pos s25n h30
          linarith only [eq8, p42, p43, p44]
        have s45 : 0 < (orient A a z) := by
          by_contra hn
          have s45n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n22
          have p46 : (orient A K a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s0 h79
          have p47 : 0 < (orient A a c) * (orient K a z) := mul_pos_of_neg_of_neg s33 s1n
          have p48 : (orient A a z) * (orient K a c) < 0 := mul_neg_of_neg_of_pos s45n s41
          linarith only [eq13, p46, p47, p48]
        have p49 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s25n h79
        have p50 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s33 h63
        have p51 : 0 < (orient A c z) * (orient K a c) := mul_pos h27 s41
        linarith only [eq15, p49, p50, p51]
  · have s0n : (orient A K a) < 0 := lt_of_le_of_ne (le_of_not_gt s0) n9
    have s52 : 0 < (orient K R a) := by
      by_contra hn
      have s52n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
      have p53 : 0 < (orient A K R) * (orient B K a) := mul_pos h8 h30
      have p54 : (orient A B K) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h1 s52n
      have p55 : (orient A K a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s0n h29
      linarith only [eq5, p53, p54, p55]
    have s56 : 0 < (orient K a o) := by
      by_contra hn
      have s56n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
      have p57 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s56n
      have p58 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
      have p59 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s52
      linarith only [eq11, p57, p58, p59]
    have s60 : (orient A K o) < 0 := by
      by_contra hn
      have s60n : 0 < (orient A K o) := lt_of_le_of_ne (le_of_not_gt hn) n12.symm
      linarith only [eq0, s0n, s60n, s56, h21]
    by_cases s61 : 0 < (orient A K c)
    ·
      have s62 : 0 < (orient A B c) := by
        by_contra hn
        have s62n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
        have p63 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s62n
        have p64 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s61
        have p65 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
        linarith only [eq2, p63, p64, p65]
      have s66 : 0 < (orient A a c) := by
        by_contra hn
        have s66n : (orient A a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n20
        have p67 : (orient A K R) * (orient A a c) < 0 := mul_neg_of_pos_of_neg h8 s66n
        have p68 : (orient A R a) * (orient A K c) < 0 := mul_neg_of_neg_of_pos h14 s61
        have p69 : 0 < (orient A R c) * (orient A K a) := mul_pos_of_neg_of_neg h16 s0n
        linarith only [eq3, p67, p68, p69]
      have s70 : (orient K a c) < 0 := by
        by_contra hn
        have s70n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
        have p71 : 0 < (orient A B K) * (orient K a c) := mul_pos h1 s70n
        have p72 : (orient A K a) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s0n h32
        have p73 : 0 < (orient A K c) * (orient B K a) := mul_pos s61 h30
        linarith only [eq8, p71, p72, p73]
      have p74 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s61 h48
      have p75 : 0 < (orient A B c) * (orient K c z) := mul_pos s62 h63
      have p76 : 0 < (orient A c z) * (orient B K c) := mul_pos h27 h32
      linarith only [eq14, p74, p75, p76]
    · have s61n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt s61) n11
      have s77 : 0 < (orient K R c) := by
        by_contra hn
        have s77n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
        have p78 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
        have p79 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s77n
        have p80 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s61n h29
        linarith only [eq6, p78, p79, p80]
      by_cases s81 : 0 < (orient A a z)
      ·
        have s82 : (orient R a z) < 0 := by
          by_contra hn
          have s82n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
          have p83 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
          have p84 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s82n
          have p85 : 0 < (orient A a z) * (orient R a b) := mul_pos s81 h65
          linarith only [eq12, p83, p84, p85]
        have s86 : 0 < (orient K R z) := by
          by_contra hn
          have s86n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
          have p87 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s82
          have p88 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s86n
          have p89 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s52
          linarith only [eq4, p87, p88, p89]
        have s90 : (orient A K z) < 0 := by
          by_contra hn
          have s90n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
          have p91 : 0 < (orient A K R) * (orient K c z) := mul_pos h8 h63
          have p92 : (orient A K c) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s61n s86
          have p93 : 0 < (orient A K z) * (orient K R c) := mul_pos s90n s77
          linarith only [eq7, p91, p92, p93]
        have s94 : 0 < (orient K a z) := by
          by_contra hn
          have s94n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
          have p95 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
          have p96 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s90 s56
          have p97 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s60 s94n
          linarith only [eq9, p95, p96, p97]
        have p98 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s94
        have p99 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0n s82
        have p100 : 0 < (orient A a z) * (orient K R a) := mul_pos s81 s52
        linarith only [eq10, p98, p99, p100]
      · have s81n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s81) n22
        have s101 : (orient A a c) < 0 := by
          by_contra hn
          have s101n : 0 < (orient A a c) := lt_of_le_of_ne (le_of_not_gt hn) n20.symm
          linarith only [eq1, s101n, s81n, h79, h27]
        have s102 : (orient K a c) < 0 := by
          by_contra hn
          have s102n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
          have p103 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s61n h79
          have p104 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s101 h63
          have p105 : 0 < (orient A c z) * (orient K a c) := mul_pos h27 s102n
          linarith only [eq15, p103, p104, p105]
        have s106 : (orient K a z) < 0 := by
          by_contra hn
          have s106n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
          have p107 : 0 < (orient A K a) * (orient a c z) := mul_pos_of_neg_of_neg s0n h79
          have p108 : (orient A a c) * (orient K a z) < 0 := mul_neg_of_neg_of_pos s101 s106n
          have p109 : 0 < (orient A a z) * (orient K a c) := mul_pos_of_neg_of_neg s81n s102
          linarith only [eq13, p107, p108, p109]
        have s110 : 0 < (orient A K z) := by
          by_contra hn
          have s110n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
          have p111 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
          have p112 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s110n s56
          have p113 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s60 s106
          linarith only [eq9, p111, p112, p113]
        have s114 : (orient R a z) < 0 := by
          by_contra hn
          have s114n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
          have p115 : 0 < (orient A R a) * (orient K a z) := mul_pos_of_neg_of_neg h14 s106
          have p116 : (orient A K a) * (orient R a z) < 0 := mul_neg_of_neg_of_pos s0n s114n
          have p117 : (orient A a z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s81n s52
          linarith only [eq10, p115, p116, p117]
        have s118 : 0 < (orient K R z) := by
          by_contra hn
          have s118n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
          have p119 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s114
          have p120 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s118n
          have p121 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s52
          linarith only [eq4, p119, p120, p121]
        have p122 : 0 < (orient A K R) * (orient K c z) := mul_pos h8 h63
        have p123 : (orient A K c) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s61n s118
        have p124 : 0 < (orient A K z) * (orient K R c) := mul_pos s110 s77
        linarith only [eq7, p122, p123, p124]
end JSP198.Nicolas
#print axioms JSP198.Nicolas.ia_nine_point_end_support_certificate
