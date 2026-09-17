/- Released under the MIT license. Explicit ring and sign proofs; no SAT premise. -/
import JSP198NicolasCaseIASupport
noncomputable section
open Classical Horton
namespace JSP198.Nicolas
theorem ia_nine_point_bfirst_certificate (A R K B a b c z o : Point)
    (h8 : 0 < (orient A K R))
    (h2 : 0 < (orient A B R))
    (h1 : 0 < (orient A B K))
    (h29 : 0 < (orient B K R))
    (h77 : (orient a b z) < 0)
    (h79 : (orient a c z) < 0)
    (h14 : (orient A R a) < 0)
    (h16 : (orient A R c) < 0)
    (h18 : (orient A R z) < 0)
    (h17 : (orient A R o) < 0)
    (h30 : 0 < (orient B K a))
    (h32 : 0 < (orient B K c))
    (h34 : 0 < (orient B K z))
    (h33 : 0 < (orient B K o))
    (h67 : 0 < (orient R a o))
    (h65 : 0 < (orient R a b))
    (h76 : (orient a b o) < 0)
    (h64 : 0 < (orient K o z))
    (h63 : 0 < (orient K c z))
    (h21 : (orient A a o) < 0)
    (h19 : (orient A a b) < 0)
    (h48 : (orient B c z) < 0)
    (h40 : 0 < (orient B a b))
    (n3 : (orient A B a) ≠ 0)
    (n5 : (orient A B c) ≠ 0)
    (n7 : (orient A B z) ≠ 0)
    (n9 : (orient A K a) ≠ 0)
    (n11 : (orient A K c) ≠ 0)
    (n12 : (orient A K o) ≠ 0)
    (n13 : (orient A K z) ≠ 0)
    (n20 : (orient A a c) ≠ 0)
    (n22 : (orient A a z) ≠ 0)
    (n27 : (orient A c z) ≠ 0)
    (n41 : (orient B a c) ≠ 0)
    (n43 : (orient B a z) ≠ 0)
    (n50 : (orient K R a) ≠ 0)
    (n52 : (orient K R c) ≠ 0)
    (n53 : (orient K R o) ≠ 0)
    (n54 : (orient K R z) ≠ 0)
    (n55 : (orient K a b) ≠ 0)
    (n56 : (orient K a c) ≠ 0)
    (n57 : (orient K a o) ≠ 0)
    (n58 : (orient K a z) ≠ 0)
    (n68 : (orient R a z) ≠ 0)
    : False := by
  have eq0 : ((orient A K a)) + -((orient A K z)) + -((orient K a z)) + ((orient A a z)) = 0 := by
    unfold orient
    ring
  have eq1 : ((orient A B a)) + -((orient A B z)) + -((orient B a z)) + ((orient A a z)) = 0 := by
    unfold orient
    ring
  have eq2 : -((orient A K R) * (orient A B a)) + ((orient A B R) * (orient A K a)) + -((orient A R a) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq3 : -((orient A K R) * (orient A B c)) + ((orient A B R) * (orient A K c)) + -((orient A R c) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq4 : -((orient A K R) * (orient A a c)) + -((orient A R a) * (orient A K c)) + ((orient A R c) * (orient A K a)) = 0 := by
    unfold orient
    ring
  have eq5 : -((orient A K R) * (orient A a o)) + -((orient A R a) * (orient A K o)) + ((orient A R o) * (orient A K a)) = 0 := by
    unfold orient
    ring
  have eq6 : -((orient A B R) * (orient A a c)) + -((orient A R a) * (orient A B c)) + ((orient A R c) * (orient A B a)) = 0 := by
    unfold orient
    ring
  have eq7 : ((orient A K R) * (orient R a z)) + -((orient A R a) * (orient K R z)) + ((orient A R z) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq8 : ((orient A K R) * (orient R a o)) + -((orient A R a) * (orient K R o)) + ((orient A R o) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq9 : ((orient A K R) * (orient B K c)) + -((orient A B K) * (orient K R c)) + -((orient A K c) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq10 : ((orient A K R) * (orient B K o)) + -((orient A B K) * (orient K R o)) + -((orient A K o) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq11 : -((orient A K R) * (orient K a c)) + ((orient A K a) * (orient K R c)) + -((orient A K c) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq12 : ((orient A K R) * (orient K o z)) + ((orient A K z) * (orient K R o)) + -((orient A K o) * (orient K R z)) = 0 := by
    unfold orient
    ring
  have eq13 : ((orient A K a) * (orient K o z)) + ((orient A K z) * (orient K a o)) + -((orient A K o) * (orient K a z)) = 0 := by
    unfold orient
    ring
  have eq14 : -((orient A B K) * (orient B c z)) + ((orient A B c) * (orient B K z)) + -((orient A B z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq15 : -((orient A B a) * (orient B c z)) + ((orient A B c) * (orient B a z)) + -((orient A B z) * (orient B a c)) = 0 := by
    unfold orient
    ring
  have eq16 : -((orient A R a) * (orient K a z)) + ((orient A K a) * (orient R a z)) + ((orient A a z) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq17 : -((orient A R a) * (orient K a o)) + ((orient A K a) * (orient R a o)) + ((orient A a o) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq18 : ((orient A R a) * (orient a b z)) + -((orient A a b) * (orient R a z)) + ((orient A a z) * (orient R a b)) = 0 := by
    unfold orient
    ring
  have eq19 : -((orient A K a) * (orient B a b)) + ((orient A B a) * (orient K a b)) + ((orient A a b) * (orient B K a)) = 0 := by
    unfold orient
    ring
  have eq20 : ((orient A K a) * (orient a b o)) + -((orient A a b) * (orient K a o)) + ((orient A a o) * (orient K a b)) = 0 := by
    unfold orient
    ring
  have eq21 : ((orient A K a) * (orient a c z)) + -((orient A a c) * (orient K a z)) + ((orient A a z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have eq22 : ((orient A B a) * (orient a b z)) + -((orient A a b) * (orient B a z)) + ((orient A a z) * (orient B a b)) = 0 := by
    unfold orient
    ring
  have eq23 : ((orient A B a) * (orient a c z)) + -((orient A a c) * (orient B a z)) + ((orient A a z) * (orient B a c)) = 0 := by
    unfold orient
    ring
  have eq24 : -((orient A K c) * (orient B c z)) + ((orient A B c) * (orient K c z)) + ((orient A c z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq25 : -((orient A K c) * (orient a c z)) + ((orient A a c) * (orient K c z)) + -((orient A c z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have eq26 : -((orient A B c) * (orient a c z)) + ((orient A a c) * (orient B c z)) + -((orient A c z) * (orient B a c)) = 0 := by
    unfold orient
    ring
  by_cases s0 : 0 < (orient A K a)
  ·
    have s1 : 0 < (orient A B a) := by
      by_contra hn
      have s1n : (orient A B a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n3
      have p2 : (orient A K R) * (orient A B a) < 0 := mul_neg_of_pos_of_neg h8 s1n
      have p3 : 0 < (orient A B R) * (orient A K a) := mul_pos h2 s0
      have p4 : (orient A R a) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h14 h1
      linarith only [eq2, p2, p3, p4]
    have s5 : 0 < (orient K a b) := by
      by_contra hn
      have s5n : (orient K a b) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n55
      have p6 : 0 < (orient A K a) * (orient B a b) := mul_pos s0 h40
      have p7 : (orient A B a) * (orient K a b) < 0 := mul_neg_of_pos_of_neg s1 s5n
      have p8 : (orient A a b) * (orient B K a) < 0 := mul_neg_of_neg_of_pos h19 h30
      linarith only [eq19, p6, p7, p8]
    have s9 : 0 < (orient K a o) := by
      by_contra hn
      have s9n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
      have p10 : (orient A K a) * (orient a b o) < 0 := mul_neg_of_pos_of_neg s0 h76
      have p11 : 0 < (orient A a b) * (orient K a o) := mul_pos_of_neg_of_neg h19 s9n
      have p12 : (orient A a o) * (orient K a b) < 0 := mul_neg_of_neg_of_pos h21 s5
      linarith only [eq20, p10, p11, p12]
    have s13 : 0 < (orient K R a) := by
      by_contra hn
      have s13n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
      have p14 : (orient A R a) * (orient K a o) < 0 := mul_neg_of_neg_of_pos h14 s9
      have p15 : 0 < (orient A K a) * (orient R a o) := mul_pos s0 h67
      have p16 : 0 < (orient A a o) * (orient K R a) := mul_pos_of_neg_of_neg h21 s13n
      linarith only [eq17, p14, p15, p16]
    by_cases s17 : 0 < (orient A a c)
    ·
      have s18 : 0 < (orient A K c) := by
        by_contra hn
        have s18n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n11
        have p19 : 0 < (orient A K R) * (orient A a c) := mul_pos h8 s17
        have p20 : 0 < (orient A R a) * (orient A K c) := mul_pos_of_neg_of_neg h14 s18n
        have p21 : (orient A R c) * (orient A K a) < 0 := mul_neg_of_neg_of_pos h16 s0
        linarith only [eq4, p19, p20, p21]
      have s22 : 0 < (orient A B c) := by
        by_contra hn
        have s22n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
        have p23 : 0 < (orient A B R) * (orient A a c) := mul_pos h2 s17
        have p24 : 0 < (orient A R a) * (orient A B c) := mul_pos_of_neg_of_neg h14 s22n
        have p25 : (orient A R c) * (orient A B a) < 0 := mul_neg_of_neg_of_pos h16 s1
        linarith only [eq6, p23, p24, p25]
      have s26 : 0 < (orient A B z) := by
        by_contra hn
        have s26n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
        have p27 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
        have p28 : 0 < (orient A B c) * (orient B K z) := mul_pos s22 h34
        have p29 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s26n h32
        linarith only [eq14, p27, p28, p29]
      have s30 : (orient A c z) < 0 := by
        by_contra hn
        have s30n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
        have p31 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s18 h48
        have p32 : 0 < (orient A B c) * (orient K c z) := mul_pos s22 h63
        have p33 : 0 < (orient A c z) * (orient B K c) := mul_pos s30n h32
        linarith only [eq24, p31, p32, p33]
      have s34 : (orient K a c) < 0 := by
        by_contra hn
        have s34n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
        have p35 : (orient A K c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s18 h79
        have p36 : 0 < (orient A a c) * (orient K c z) := mul_pos s17 h63
        have p37 : (orient A c z) * (orient K a c) < 0 := mul_neg_of_neg_of_pos s30 s34n
        linarith only [eq25, p35, p36, p37]
      by_cases s38 : 0 < (orient A a z)
      ·
        have s39 : (orient R a z) < 0 := by
          by_contra hn
          have s39n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
          have p40 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
          have p41 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s39n
          have p42 : 0 < (orient A a z) * (orient R a b) := mul_pos s38 h65
          linarith only [eq18, p40, p41, p42]
        have s43 : (orient K a z) < 0 := by
          by_contra hn
          have s43n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
          have p44 : (orient A K a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s0 h79
          have p45 : 0 < (orient A a c) * (orient K a z) := mul_pos s17 s43n
          have p46 : (orient A a z) * (orient K a c) < 0 := mul_neg_of_pos_of_neg s38 s34
          linarith only [eq21, p44, p45, p46]
        have s47 : 0 < (orient A K z) := by
          by_contra hn
          have s47n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
          linarith only [eq0, s0, s47n, s43, s38]
        have s48 : 0 < (orient K R z) := by
          by_contra hn
          have s48n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
          have p49 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s39
          have p50 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s48n
          have p51 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s13
          linarith only [eq7, p49, p50, p51]
        have s52 : (orient A K o) < 0 := by
          by_contra hn
          have s52n : 0 < (orient A K o) := lt_of_le_of_ne (le_of_not_gt hn) n12.symm
          have p53 : 0 < (orient A K a) * (orient K o z) := mul_pos s0 h64
          have p54 : 0 < (orient A K z) * (orient K a o) := mul_pos s47 s9
          have p55 : (orient A K o) * (orient K a z) < 0 := mul_neg_of_pos_of_neg s52n s43
          linarith only [eq13, p53, p54, p55]
        have s56 : 0 < (orient K R o) := by
          by_contra hn
          have s56n : (orient K R o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n53
          have p57 : 0 < (orient A K R) * (orient B K o) := mul_pos h8 h33
          have p58 : (orient A B K) * (orient K R o) < 0 := mul_neg_of_pos_of_neg h1 s56n
          have p59 : (orient A K o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s52 h29
          linarith only [eq10, p57, p58, p59]
        have p60 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
        have p61 : 0 < (orient A K z) * (orient K R o) := mul_pos s47 s56
        have p62 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s52 s48
        linarith only [eq12, p60, p61, p62]
      · have s38n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s38) n22
        have s63 : 0 < (orient B a z) := by
          by_contra hn
          have s63n : (orient B a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n43
          have p64 : (orient A B a) * (orient a b z) < 0 := mul_neg_of_pos_of_neg s1 h77
          have p65 : 0 < (orient A a b) * (orient B a z) := mul_pos_of_neg_of_neg h19 s63n
          have p66 : (orient A a z) * (orient B a b) < 0 := mul_neg_of_neg_of_pos s38n h40
          linarith only [eq22, p64, p65, p66]
        have s67 : (orient B a c) < 0 := by
          by_contra hn
          have s67n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
          have p68 : (orient A B a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s1 h79
          have p69 : 0 < (orient A a c) * (orient B a z) := mul_pos s17 s63
          have p70 : (orient A a z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s38n s67n
          linarith only [eq23, p68, p69, p70]
        have p71 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s1 h48
        have p72 : 0 < (orient A B c) * (orient B a z) := mul_pos s22 s63
        have p73 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s26 s67
        linarith only [eq15, p71, p72, p73]
    · have s17n : (orient A a c) < 0 := lt_of_le_of_ne (le_of_not_gt s17) n20
      by_cases s74 : 0 < (orient A a z)
      ·
        have s75 : (orient R a z) < 0 := by
          by_contra hn
          have s75n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
          have p76 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
          have p77 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s75n
          have p78 : 0 < (orient A a z) * (orient R a b) := mul_pos s74 h65
          linarith only [eq18, p76, p77, p78]
        have s79 : 0 < (orient K R z) := by
          by_contra hn
          have s79n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
          have p80 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s75
          have p81 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s79n
          have p82 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s13
          linarith only [eq7, p80, p81, p82]
        by_cases s83 : 0 < (orient A B c)
        ·
          have s84 : 0 < (orient A B z) := by
            by_contra hn
            have s84n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
            have p85 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
            have p86 : 0 < (orient A B c) * (orient B K z) := mul_pos s83 h34
            have p87 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s84n h32
            linarith only [eq14, p85, p86, p87]
          by_cases s88 : 0 < (orient A K c)
          ·
            have s89 : (orient A c z) < 0 := by
              by_contra hn
              have s89n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
              have p90 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s88 h48
              have p91 : 0 < (orient A B c) * (orient K c z) := mul_pos s83 h63
              have p92 : 0 < (orient A c z) * (orient B K c) := mul_pos s89n h32
              linarith only [eq24, p90, p91, p92]
            have s93 : (orient B a c) < 0 := by
              by_contra hn
              have s93n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
              have p94 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s83 h79
              have p95 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s17n h48
              have p96 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s89 s93n
              linarith only [eq26, p94, p95, p96]
            have s97 : (orient B a z) < 0 := by
              by_contra hn
              have s97n : 0 < (orient B a z) := lt_of_le_of_ne (le_of_not_gt hn) n43.symm
              have p98 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s1 h48
              have p99 : 0 < (orient A B c) * (orient B a z) := mul_pos s83 s97n
              have p100 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s84 s93
              linarith only [eq15, p98, p99, p100]
            have p101 : (orient A B a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s1 h79
            have p102 : 0 < (orient A a c) * (orient B a z) := mul_pos_of_neg_of_neg s17n s97
            have p103 : (orient A a z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s74 s93
            linarith only [eq23, p101, p102, p103]
          · have s88n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt s88) n11
            have s104 : 0 < (orient K R c) := by
              by_contra hn
              have s104n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
              have p105 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
              have p106 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s104n
              have p107 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s88n h29
              linarith only [eq9, p105, p106, p107]
            have s108 : 0 < (orient K a c) := by
              by_contra hn
              have s108n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
              have p109 : (orient A K R) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h8 s108n
              have p110 : 0 < (orient A K a) * (orient K R c) := mul_pos s0 s104
              have p111 : (orient A K c) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s88n s13
              linarith only [eq11, p109, p110, p111]
            have s112 : (orient A c z) < 0 := by
              by_contra hn
              have s112n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
              have p113 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s88n h79
              have p114 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s17n h63
              have p115 : 0 < (orient A c z) * (orient K a c) := mul_pos s112n s108
              linarith only [eq25, p113, p114, p115]
            have s116 : (orient B a c) < 0 := by
              by_contra hn
              have s116n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
              have p117 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s83 h79
              have p118 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s17n h48
              have p119 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s112 s116n
              linarith only [eq26, p117, p118, p119]
            have s120 : (orient B a z) < 0 := by
              by_contra hn
              have s120n : 0 < (orient B a z) := lt_of_le_of_ne (le_of_not_gt hn) n43.symm
              have p121 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s1 h48
              have p122 : 0 < (orient A B c) * (orient B a z) := mul_pos s83 s120n
              have p123 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s84 s116
              linarith only [eq15, p121, p122, p123]
            have p124 : (orient A B a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s1 h79
            have p125 : 0 < (orient A a c) * (orient B a z) := mul_pos_of_neg_of_neg s17n s120
            have p126 : (orient A a z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s74 s116
            linarith only [eq23, p124, p125, p126]
        · have s83n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt s83) n5
          have s127 : (orient A K c) < 0 := by
            by_contra hn
            have s127n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
            have p128 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s83n
            have p129 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s127n
            have p130 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
            linarith only [eq3, p128, p129, p130]
          have s131 : 0 < (orient K R c) := by
            by_contra hn
            have s131n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
            have p132 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
            have p133 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s131n
            have p134 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s127 h29
            linarith only [eq9, p132, p133, p134]
          have s135 : 0 < (orient K a c) := by
            by_contra hn
            have s135n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
            have p136 : (orient A K R) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h8 s135n
            have p137 : 0 < (orient A K a) * (orient K R c) := mul_pos s0 s131
            have p138 : (orient A K c) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s127 s13
            linarith only [eq11, p136, p137, p138]
          have s139 : 0 < (orient A c z) := by
            by_contra hn
            have s139n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
            have p140 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s127 h48
            have p141 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s83n h63
            have p142 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s139n h32
            linarith only [eq24, p140, p141, p142]
          have p143 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s127 h79
          have p144 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s17n h63
          have p145 : 0 < (orient A c z) * (orient K a c) := mul_pos s139 s135
          linarith only [eq25, p143, p144, p145]
      · have s74n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s74) n22
        have s146 : 0 < (orient B a z) := by
          by_contra hn
          have s146n : (orient B a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n43
          have p147 : (orient A B a) * (orient a b z) < 0 := mul_neg_of_pos_of_neg s1 h77
          have p148 : 0 < (orient A a b) * (orient B a z) := mul_pos_of_neg_of_neg h19 s146n
          have p149 : (orient A a z) * (orient B a b) < 0 := mul_neg_of_neg_of_pos s74n h40
          linarith only [eq22, p147, p148, p149]
        by_cases s150 : 0 < (orient A B c)
        ·
          have s151 : 0 < (orient A B z) := by
            by_contra hn
            have s151n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
            have p152 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
            have p153 : 0 < (orient A B c) * (orient B K z) := mul_pos s150 h34
            have p154 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s151n h32
            linarith only [eq14, p152, p153, p154]
          have s155 : 0 < (orient B a c) := by
            by_contra hn
            have s155n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
            have p156 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s1 h48
            have p157 : 0 < (orient A B c) * (orient B a z) := mul_pos s150 s146
            have p158 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s151 s155n
            linarith only [eq15, p156, p157, p158]
          have s159 : 0 < (orient A c z) := by
            by_contra hn
            have s159n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
            have p160 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s150 h79
            have p161 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s17n h48
            have p162 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s159n s155
            linarith only [eq26, p160, p161, p162]
          have s163 : (orient A K c) < 0 := by
            by_contra hn
            have s163n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
            have p164 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s163n h48
            have p165 : 0 < (orient A B c) * (orient K c z) := mul_pos s150 h63
            have p166 : 0 < (orient A c z) * (orient B K c) := mul_pos s159 h32
            linarith only [eq24, p164, p165, p166]
          have s167 : (orient K a c) < 0 := by
            by_contra hn
            have s167n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
            have p168 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s163 h79
            have p169 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s17n h63
            have p170 : 0 < (orient A c z) * (orient K a c) := mul_pos s159 s167n
            linarith only [eq25, p168, p169, p170]
          have s171 : 0 < (orient K R c) := by
            by_contra hn
            have s171n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
            have p172 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
            have p173 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s171n
            have p174 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s163 h29
            linarith only [eq9, p172, p173, p174]
          have p175 : (orient A K R) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h8 s167
          have p176 : 0 < (orient A K a) * (orient K R c) := mul_pos s0 s171
          have p177 : (orient A K c) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s163 s13
          linarith only [eq11, p175, p176, p177]
        · have s150n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt s150) n5
          have s178 : (orient A K c) < 0 := by
            by_contra hn
            have s178n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
            have p179 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s150n
            have p180 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s178n
            have p181 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
            linarith only [eq3, p179, p180, p181]
          have s182 : 0 < (orient K R c) := by
            by_contra hn
            have s182n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
            have p183 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
            have p184 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s182n
            have p185 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s178 h29
            linarith only [eq9, p183, p184, p185]
          have s186 : 0 < (orient K a c) := by
            by_contra hn
            have s186n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
            have p187 : (orient A K R) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h8 s186n
            have p188 : 0 < (orient A K a) * (orient K R c) := mul_pos s0 s182
            have p189 : (orient A K c) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s178 s13
            linarith only [eq11, p187, p188, p189]
          have s190 : 0 < (orient K a z) := by
            by_contra hn
            have s190n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
            have p191 : (orient A K a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s0 h79
            have p192 : 0 < (orient A a c) * (orient K a z) := mul_pos_of_neg_of_neg s17n s190n
            have p193 : (orient A a z) * (orient K a c) < 0 := mul_neg_of_neg_of_pos s74n s186
            linarith only [eq21, p191, p192, p193]
          have s194 : 0 < (orient A c z) := by
            by_contra hn
            have s194n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
            have p195 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s178 h48
            have p196 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s150n h63
            have p197 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s194n h32
            linarith only [eq24, p195, p196, p197]
          have p198 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s178 h79
          have p199 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s17n h63
          have p200 : 0 < (orient A c z) * (orient K a c) := mul_pos s194 s186
          linarith only [eq25, p198, p199, p200]
  · have s0n : (orient A K a) < 0 := lt_of_le_of_ne (le_of_not_gt s0) n9
    have s201 : (orient A K o) < 0 := by
      by_contra hn
      have s201n : 0 < (orient A K o) := lt_of_le_of_ne (le_of_not_gt hn) n12.symm
      have p202 : (orient A K R) * (orient A a o) < 0 := mul_neg_of_pos_of_neg h8 h21
      have p203 : (orient A R a) * (orient A K o) < 0 := mul_neg_of_neg_of_pos h14 s201n
      have p204 : 0 < (orient A R o) * (orient A K a) := mul_pos_of_neg_of_neg h17 s0n
      linarith only [eq5, p202, p203, p204]
    have s205 : 0 < (orient K R o) := by
      by_contra hn
      have s205n : (orient K R o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n53
      have p206 : 0 < (orient A K R) * (orient B K o) := mul_pos h8 h33
      have p207 : (orient A B K) * (orient K R o) < 0 := mul_neg_of_pos_of_neg h1 s205n
      have p208 : (orient A K o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s201 h29
      linarith only [eq10, p206, p207, p208]
    have s209 : 0 < (orient K R a) := by
      by_contra hn
      have s209n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
      have p210 : 0 < (orient A K R) * (orient R a o) := mul_pos h8 h67
      have p211 : (orient A R a) * (orient K R o) < 0 := mul_neg_of_neg_of_pos h14 s205
      have p212 : 0 < (orient A R o) * (orient K R a) := mul_pos_of_neg_of_neg h17 s209n
      linarith only [eq8, p210, p211, p212]
    have s213 : 0 < (orient K a o) := by
      by_contra hn
      have s213n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
      have p214 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s213n
      have p215 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
      have p216 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s209
      linarith only [eq17, p214, p215, p216]
    have s217 : 0 < (orient K a b) := by
      by_contra hn
      have s217n : (orient K a b) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n55
      have p218 : 0 < (orient A K a) * (orient a b o) := mul_pos_of_neg_of_neg s0n h76
      have p219 : (orient A a b) * (orient K a o) < 0 := mul_neg_of_neg_of_pos h19 s213
      have p220 : 0 < (orient A a o) * (orient K a b) := mul_pos_of_neg_of_neg h21 s217n
      linarith only [eq20, p218, p219, p220]
    by_cases s221 : 0 < (orient A a c)
    ·
      by_cases s222 : 0 < (orient A B a)
      ·
        have s223 : 0 < (orient A B c) := by
          by_contra hn
          have s223n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
          have p224 : 0 < (orient A B R) * (orient A a c) := mul_pos h2 s221
          have p225 : 0 < (orient A R a) * (orient A B c) := mul_pos_of_neg_of_neg h14 s223n
          have p226 : (orient A R c) * (orient A B a) < 0 := mul_neg_of_neg_of_pos h16 s222
          linarith only [eq6, p224, p225, p226]
        have s227 : 0 < (orient A B z) := by
          by_contra hn
          have s227n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
          have p228 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
          have p229 : 0 < (orient A B c) * (orient B K z) := mul_pos s223 h34
          have p230 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s227n h32
          linarith only [eq14, p228, p229, p230]
        by_cases s231 : 0 < (orient A a z)
        ·
          have s232 : (orient R a z) < 0 := by
            by_contra hn
            have s232n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
            have p233 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
            have p234 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s232n
            have p235 : 0 < (orient A a z) * (orient R a b) := mul_pos s231 h65
            linarith only [eq18, p233, p234, p235]
          have s236 : 0 < (orient K R z) := by
            by_contra hn
            have s236n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
            have p237 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s232
            have p238 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s236n
            have p239 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s209
            linarith only [eq7, p237, p238, p239]
          have s240 : (orient A K z) < 0 := by
            by_contra hn
            have s240n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
            have p241 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
            have p242 : 0 < (orient A K z) * (orient K R o) := mul_pos s240n s205
            have p243 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s201 s236
            linarith only [eq12, p241, p242, p243]
          have s244 : 0 < (orient K a z) := by
            by_contra hn
            have s244n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
            have p245 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
            have p246 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s240 s213
            have p247 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s201 s244n
            linarith only [eq13, p245, p246, p247]
          have p248 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s244
          have p249 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0n s232
          have p250 : 0 < (orient A a z) * (orient K R a) := mul_pos s231 s209
          linarith only [eq16, p248, p249, p250]
        · have s231n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s231) n22
          have s251 : 0 < (orient B a z) := by
            by_contra hn
            have s251n : (orient B a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n43
            have p252 : (orient A B a) * (orient a b z) < 0 := mul_neg_of_pos_of_neg s222 h77
            have p253 : 0 < (orient A a b) * (orient B a z) := mul_pos_of_neg_of_neg h19 s251n
            have p254 : (orient A a z) * (orient B a b) < 0 := mul_neg_of_neg_of_pos s231n h40
            linarith only [eq22, p252, p253, p254]
          have s255 : (orient B a c) < 0 := by
            by_contra hn
            have s255n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
            have p256 : (orient A B a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s222 h79
            have p257 : 0 < (orient A a c) * (orient B a z) := mul_pos s221 s251
            have p258 : (orient A a z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s231n s255n
            linarith only [eq23, p256, p257, p258]
          have p259 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s222 h48
          have p260 : 0 < (orient A B c) * (orient B a z) := mul_pos s223 s251
          have p261 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s227 s255
          linarith only [eq15, p259, p260, p261]
      · have s222n : (orient A B a) < 0 := lt_of_le_of_ne (le_of_not_gt s222) n3
        by_cases s262 : 0 < (orient A a z)
        ·
          have s263 : (orient R a z) < 0 := by
            by_contra hn
            have s263n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
            have p264 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
            have p265 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s263n
            have p266 : 0 < (orient A a z) * (orient R a b) := mul_pos s262 h65
            linarith only [eq18, p264, p265, p266]
          have s267 : (orient B a z) < 0 := by
            by_contra hn
            have s267n : 0 < (orient B a z) := lt_of_le_of_ne (le_of_not_gt hn) n43.symm
            have p268 : 0 < (orient A B a) * (orient a b z) := mul_pos_of_neg_of_neg s222n h77
            have p269 : (orient A a b) * (orient B a z) < 0 := mul_neg_of_neg_of_pos h19 s267n
            have p270 : 0 < (orient A a z) * (orient B a b) := mul_pos s262 h40
            linarith only [eq22, p268, p269, p270]
          have s271 : (orient B a c) < 0 := by
            by_contra hn
            have s271n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
            have p272 : 0 < (orient A B a) * (orient a c z) := mul_pos_of_neg_of_neg s222n h79
            have p273 : (orient A a c) * (orient B a z) < 0 := mul_neg_of_pos_of_neg s221 s267
            have p274 : 0 < (orient A a z) * (orient B a c) := mul_pos s262 s271n
            linarith only [eq23, p272, p273, p274]
          have s275 : 0 < (orient K R z) := by
            by_contra hn
            have s275n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
            have p276 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s263
            have p277 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s275n
            have p278 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s209
            linarith only [eq7, p276, p277, p278]
          have s279 : (orient A K z) < 0 := by
            by_contra hn
            have s279n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
            have p280 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
            have p281 : 0 < (orient A K z) * (orient K R o) := mul_pos s279n s205
            have p282 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s201 s275
            linarith only [eq12, p280, p281, p282]
          have s283 : 0 < (orient K a z) := by
            by_contra hn
            have s283n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
            have p284 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
            have p285 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s279 s213
            have p286 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s201 s283n
            linarith only [eq13, p284, p285, p286]
          have p287 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s283
          have p288 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0n s263
          have p289 : 0 < (orient A a z) * (orient K R a) := mul_pos s262 s209
          linarith only [eq16, p287, p288, p289]
        · have s262n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s262) n22
          by_cases s290 : 0 < (orient A B c)
          ·
            have s291 : 0 < (orient A B z) := by
              by_contra hn
              have s291n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
              have p292 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
              have p293 : 0 < (orient A B c) * (orient B K z) := mul_pos s290 h34
              have p294 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s291n h32
              linarith only [eq14, p292, p293, p294]
            have s295 : (orient B a z) < 0 := by
              by_contra hn
              have s295n : 0 < (orient B a z) := lt_of_le_of_ne (le_of_not_gt hn) n43.symm
              linarith only [eq1, s222n, s291, s295n, s262n]
            have s296 : (orient B a c) < 0 := by
              by_contra hn
              have s296n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
              have p297 : 0 < (orient A B a) * (orient B c z) := mul_pos_of_neg_of_neg s222n h48
              have p298 : (orient A B c) * (orient B a z) < 0 := mul_neg_of_pos_of_neg s290 s295
              have p299 : 0 < (orient A B z) * (orient B a c) := mul_pos s291 s296n
              linarith only [eq15, p297, p298, p299]
            have p300 : 0 < (orient A B a) * (orient a c z) := mul_pos_of_neg_of_neg s222n h79
            have p301 : (orient A a c) * (orient B a z) < 0 := mul_neg_of_pos_of_neg s221 s295
            have p302 : 0 < (orient A a z) * (orient B a c) := mul_pos_of_neg_of_neg s262n s296
            linarith only [eq23, p300, p301, p302]
          · have s290n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt s290) n5
            have s303 : (orient A K c) < 0 := by
              by_contra hn
              have s303n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
              have p304 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s290n
              have p305 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s303n
              have p306 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
              linarith only [eq3, p304, p305, p306]
            have s307 : 0 < (orient K R c) := by
              by_contra hn
              have s307n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
              have p308 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
              have p309 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s307n
              have p310 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s303 h29
              linarith only [eq9, p308, p309, p310]
            have s311 : 0 < (orient A c z) := by
              by_contra hn
              have s311n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
              have p312 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s303 h48
              have p313 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s290n h63
              have p314 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s311n h32
              linarith only [eq24, p312, p313, p314]
            have s315 : (orient B a c) < 0 := by
              by_contra hn
              have s315n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
              have p316 : 0 < (orient A B c) * (orient a c z) := mul_pos_of_neg_of_neg s290n h79
              have p317 : (orient A a c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s221 h48
              have p318 : 0 < (orient A c z) * (orient B a c) := mul_pos s311 s315n
              linarith only [eq26, p316, p317, p318]
            have s319 : 0 < (orient B a z) := by
              by_contra hn
              have s319n : (orient B a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n43
              have p320 : 0 < (orient A B a) * (orient a c z) := mul_pos_of_neg_of_neg s222n h79
              have p321 : (orient A a c) * (orient B a z) < 0 := mul_neg_of_pos_of_neg s221 s319n
              have p322 : 0 < (orient A a z) * (orient B a c) := mul_pos_of_neg_of_neg s262n s315
              linarith only [eq23, p320, p321, p322]
            have s323 : (orient A B z) < 0 := by
              by_contra hn
              have s323n : 0 < (orient A B z) := lt_of_le_of_ne (le_of_not_gt hn) n7.symm
              linarith only [eq1, s222n, s323n, s319, s262n]
            have p324 : 0 < (orient A B a) * (orient B c z) := mul_pos_of_neg_of_neg s222n h48
            have p325 : (orient A B c) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s290n s319
            have p326 : 0 < (orient A B z) * (orient B a c) := mul_pos_of_neg_of_neg s323 s315
            linarith only [eq15, p324, p325, p326]
    · have s221n : (orient A a c) < 0 := lt_of_le_of_ne (le_of_not_gt s221) n20
      have s327 : (orient A K c) < 0 := by
        by_contra hn
        have s327n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
        have p328 : (orient A K R) * (orient A a c) < 0 := mul_neg_of_pos_of_neg h8 s221n
        have p329 : (orient A R a) * (orient A K c) < 0 := mul_neg_of_neg_of_pos h14 s327n
        have p330 : 0 < (orient A R c) * (orient A K a) := mul_pos_of_neg_of_neg h16 s0n
        linarith only [eq4, p328, p329, p330]
      have s331 : 0 < (orient K R c) := by
        by_contra hn
        have s331n : (orient K R c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n52
        have p332 : 0 < (orient A K R) * (orient B K c) := mul_pos h8 h32
        have p333 : (orient A B K) * (orient K R c) < 0 := mul_neg_of_pos_of_neg h1 s331n
        have p334 : (orient A K c) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s327 h29
        linarith only [eq9, p332, p333, p334]
      by_cases s335 : 0 < (orient A B a)
      ·
        by_cases s336 : 0 < (orient A a z)
        ·
          have s337 : (orient R a z) < 0 := by
            by_contra hn
            have s337n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
            have p338 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
            have p339 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s337n
            have p340 : 0 < (orient A a z) * (orient R a b) := mul_pos s336 h65
            linarith only [eq18, p338, p339, p340]
          have s341 : 0 < (orient K R z) := by
            by_contra hn
            have s341n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
            have p342 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s337
            have p343 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s341n
            have p344 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s209
            linarith only [eq7, p342, p343, p344]
          have s345 : (orient A K z) < 0 := by
            by_contra hn
            have s345n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
            have p346 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
            have p347 : 0 < (orient A K z) * (orient K R o) := mul_pos s345n s205
            have p348 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s201 s341
            linarith only [eq12, p346, p347, p348]
          have s349 : 0 < (orient K a z) := by
            by_contra hn
            have s349n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
            have p350 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
            have p351 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s345 s213
            have p352 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s201 s349n
            linarith only [eq13, p350, p351, p352]
          have p353 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s349
          have p354 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0n s337
          have p355 : 0 < (orient A a z) * (orient K R a) := mul_pos s336 s209
          linarith only [eq16, p353, p354, p355]
        · have s336n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s336) n22
          have s356 : 0 < (orient B a z) := by
            by_contra hn
            have s356n : (orient B a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n43
            have p357 : (orient A B a) * (orient a b z) < 0 := mul_neg_of_pos_of_neg s335 h77
            have p358 : 0 < (orient A a b) * (orient B a z) := mul_pos_of_neg_of_neg h19 s356n
            have p359 : (orient A a z) * (orient B a b) < 0 := mul_neg_of_neg_of_pos s336n h40
            linarith only [eq22, p357, p358, p359]
          by_cases s360 : 0 < (orient A B c)
          ·
            have s361 : 0 < (orient A B z) := by
              by_contra hn
              have s361n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
              have p362 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
              have p363 : 0 < (orient A B c) * (orient B K z) := mul_pos s360 h34
              have p364 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s361n h32
              linarith only [eq14, p362, p363, p364]
            have s365 : 0 < (orient B a c) := by
              by_contra hn
              have s365n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
              have p366 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s335 h48
              have p367 : 0 < (orient A B c) * (orient B a z) := mul_pos s360 s356
              have p368 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s361 s365n
              linarith only [eq15, p366, p367, p368]
            have s369 : 0 < (orient A c z) := by
              by_contra hn
              have s369n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
              have p370 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s360 h79
              have p371 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s221n h48
              have p372 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s369n s365
              linarith only [eq26, p370, p371, p372]
            have s373 : (orient K a c) < 0 := by
              by_contra hn
              have s373n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
              have p374 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s327 h79
              have p375 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s221n h63
              have p376 : 0 < (orient A c z) * (orient K a c) := mul_pos s369 s373n
              linarith only [eq25, p374, p375, p376]
            have s377 : (orient K a z) < 0 := by
              by_contra hn
              have s377n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
              have p378 : 0 < (orient A K a) * (orient a c z) := mul_pos_of_neg_of_neg s0n h79
              have p379 : (orient A a c) * (orient K a z) < 0 := mul_neg_of_neg_of_pos s221n s377n
              have p380 : 0 < (orient A a z) * (orient K a c) := mul_pos_of_neg_of_neg s336n s373
              linarith only [eq21, p378, p379, p380]
            have s381 : 0 < (orient A K z) := by
              by_contra hn
              have s381n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
              have p382 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
              have p383 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s381n s213
              have p384 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s201 s377
              linarith only [eq13, p382, p383, p384]
            have s385 : (orient R a z) < 0 := by
              by_contra hn
              have s385n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
              have p386 : 0 < (orient A R a) * (orient K a z) := mul_pos_of_neg_of_neg h14 s377
              have p387 : (orient A K a) * (orient R a z) < 0 := mul_neg_of_neg_of_pos s0n s385n
              have p388 : (orient A a z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s336n s209
              linarith only [eq16, p386, p387, p388]
            have s389 : 0 < (orient K R z) := by
              by_contra hn
              have s389n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
              have p390 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s385
              have p391 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s389n
              have p392 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s209
              linarith only [eq7, p390, p391, p392]
            have p393 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
            have p394 : 0 < (orient A K z) * (orient K R o) := mul_pos s381 s205
            have p395 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s201 s389
            linarith only [eq12, p393, p394, p395]
          · have s360n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt s360) n5
            have s396 : 0 < (orient A c z) := by
              by_contra hn
              have s396n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
              have p397 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s327 h48
              have p398 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s360n h63
              have p399 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s396n h32
              linarith only [eq24, p397, p398, p399]
            have s400 : (orient K a c) < 0 := by
              by_contra hn
              have s400n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
              have p401 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s327 h79
              have p402 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s221n h63
              have p403 : 0 < (orient A c z) * (orient K a c) := mul_pos s396 s400n
              linarith only [eq25, p401, p402, p403]
            have s404 : (orient K a z) < 0 := by
              by_contra hn
              have s404n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
              have p405 : 0 < (orient A K a) * (orient a c z) := mul_pos_of_neg_of_neg s0n h79
              have p406 : (orient A a c) * (orient K a z) < 0 := mul_neg_of_neg_of_pos s221n s404n
              have p407 : 0 < (orient A a z) * (orient K a c) := mul_pos_of_neg_of_neg s336n s400
              linarith only [eq21, p405, p406, p407]
            have s408 : 0 < (orient A K z) := by
              by_contra hn
              have s408n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
              have p409 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
              have p410 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s408n s213
              have p411 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s201 s404
              linarith only [eq13, p409, p410, p411]
            have s412 : (orient R a z) < 0 := by
              by_contra hn
              have s412n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
              have p413 : 0 < (orient A R a) * (orient K a z) := mul_pos_of_neg_of_neg h14 s404
              have p414 : (orient A K a) * (orient R a z) < 0 := mul_neg_of_neg_of_pos s0n s412n
              have p415 : (orient A a z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s336n s209
              linarith only [eq16, p413, p414, p415]
            have s416 : 0 < (orient K R z) := by
              by_contra hn
              have s416n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
              have p417 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s412
              have p418 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s416n
              have p419 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s209
              linarith only [eq7, p417, p418, p419]
            have p420 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
            have p421 : 0 < (orient A K z) * (orient K R o) := mul_pos s408 s205
            have p422 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s201 s416
            linarith only [eq12, p420, p421, p422]
      · have s335n : (orient A B a) < 0 := lt_of_le_of_ne (le_of_not_gt s335) n3
        have s423 : (orient A B c) < 0 := by
          by_contra hn
          have s423n : 0 < (orient A B c) := lt_of_le_of_ne (le_of_not_gt hn) n5.symm
          have p424 : (orient A B R) * (orient A a c) < 0 := mul_neg_of_pos_of_neg h2 s221n
          have p425 : (orient A R a) * (orient A B c) < 0 := mul_neg_of_neg_of_pos h14 s423n
          have p426 : 0 < (orient A R c) * (orient A B a) := mul_pos_of_neg_of_neg h16 s335n
          linarith only [eq6, p424, p425, p426]
        have s427 : 0 < (orient A c z) := by
          by_contra hn
          have s427n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
          have p428 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s327 h48
          have p429 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s423 h63
          have p430 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s427n h32
          linarith only [eq24, p428, p429, p430]
        have s431 : (orient K a c) < 0 := by
          by_contra hn
          have s431n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
          have p432 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s327 h79
          have p433 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s221n h63
          have p434 : 0 < (orient A c z) * (orient K a c) := mul_pos s427 s431n
          linarith only [eq25, p432, p433, p434]
        by_cases s435 : 0 < (orient A a z)
        ·
          have s436 : (orient R a z) < 0 := by
            by_contra hn
            have s436n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
            have p437 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
            have p438 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s436n
            have p439 : 0 < (orient A a z) * (orient R a b) := mul_pos s435 h65
            linarith only [eq18, p437, p438, p439]
          have s440 : (orient B a z) < 0 := by
            by_contra hn
            have s440n : 0 < (orient B a z) := lt_of_le_of_ne (le_of_not_gt hn) n43.symm
            have p441 : 0 < (orient A B a) * (orient a b z) := mul_pos_of_neg_of_neg s335n h77
            have p442 : (orient A a b) * (orient B a z) < 0 := mul_neg_of_neg_of_pos h19 s440n
            have p443 : 0 < (orient A a z) * (orient B a b) := mul_pos s435 h40
            linarith only [eq22, p441, p442, p443]
          have s444 : 0 < (orient K R z) := by
            by_contra hn
            have s444n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
            have p445 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s436
            have p446 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s444n
            have p447 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s209
            linarith only [eq7, p445, p446, p447]
          have s448 : (orient A K z) < 0 := by
            by_contra hn
            have s448n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
            have p449 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
            have p450 : 0 < (orient A K z) * (orient K R o) := mul_pos s448n s205
            have p451 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s201 s444
            linarith only [eq12, p449, p450, p451]
          have s452 : 0 < (orient K a z) := by
            by_contra hn
            have s452n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
            have p453 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
            have p454 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s448 s213
            have p455 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s201 s452n
            linarith only [eq13, p453, p454, p455]
          have p456 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s452
          have p457 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0n s436
          have p458 : 0 < (orient A a z) * (orient K R a) := mul_pos s435 s209
          linarith only [eq16, p456, p457, p458]
        · have s435n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s435) n22
          have s459 : (orient K a z) < 0 := by
            by_contra hn
            have s459n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
            have p460 : 0 < (orient A K a) * (orient a c z) := mul_pos_of_neg_of_neg s0n h79
            have p461 : (orient A a c) * (orient K a z) < 0 := mul_neg_of_neg_of_pos s221n s459n
            have p462 : 0 < (orient A a z) * (orient K a c) := mul_pos_of_neg_of_neg s435n s431
            linarith only [eq21, p460, p461, p462]
          have s463 : 0 < (orient A K z) := by
            by_contra hn
            have s463n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
            have p464 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
            have p465 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s463n s213
            have p466 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s201 s459
            linarith only [eq13, p464, p465, p466]
          have s467 : (orient R a z) < 0 := by
            by_contra hn
            have s467n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
            have p468 : 0 < (orient A R a) * (orient K a z) := mul_pos_of_neg_of_neg h14 s459
            have p469 : (orient A K a) * (orient R a z) < 0 := mul_neg_of_neg_of_pos s0n s467n
            have p470 : (orient A a z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s435n s209
            linarith only [eq16, p468, p469, p470]
          have s471 : 0 < (orient K R z) := by
            by_contra hn
            have s471n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
            have p472 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s467
            have p473 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s471n
            have p474 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s209
            linarith only [eq7, p472, p473, p474]
          have p475 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
          have p476 : 0 < (orient A K z) * (orient K R o) := mul_pos s463 s205
          have p477 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s201 s471
          linarith only [eq12, p475, p476, p477]
theorem ia_nine_point_bchord_certificate (A R K B a b c z o : Point)
    (h8 : 0 < (orient A K R))
    (h2 : 0 < (orient A B R))
    (h1 : 0 < (orient A B K))
    (h29 : 0 < (orient B K R))
    (h79 : (orient a c z) < 0)
    (h14 : (orient A R a) < 0)
    (h16 : (orient A R c) < 0)
    (h18 : (orient A R z) < 0)
    (h17 : (orient A R o) < 0)
    (h30 : 0 < (orient B K a))
    (h32 : 0 < (orient B K c))
    (h34 : 0 < (orient B K z))
    (h33 : 0 < (orient B K o))
    (h67 : 0 < (orient R a o))
    (h64 : 0 < (orient K o z))
    (h63 : 0 < (orient K c z))
    (h21 : (orient A a o) < 0)
    (h49 : (orient B o z) < 0)
    (h48 : (orient B c z) < 0)
    (h43 : 0 < (orient B a z))
    (n3 : (orient A B a) ≠ 0)
    (n5 : (orient A B c) ≠ 0)
    (n6 : (orient A B o) ≠ 0)
    (n7 : (orient A B z) ≠ 0)
    (n9 : (orient A K a) ≠ 0)
    (n11 : (orient A K c) ≠ 0)
    (n12 : (orient A K o) ≠ 0)
    (n13 : (orient A K z) ≠ 0)
    (n20 : (orient A a c) ≠ 0)
    (n22 : (orient A a z) ≠ 0)
    (n27 : (orient A c z) ≠ 0)
    (n35 : (orient B R a) ≠ 0)
    (n38 : (orient B R o) ≠ 0)
    (n39 : (orient B R z) ≠ 0)
    (n41 : (orient B a c) ≠ 0)
    (n42 : (orient B a o) ≠ 0)
    (n50 : (orient K R a) ≠ 0)
    (n53 : (orient K R o) ≠ 0)
    (n54 : (orient K R z) ≠ 0)
    (n56 : (orient K a c) ≠ 0)
    (n57 : (orient K a o) ≠ 0)
    (n58 : (orient K a z) ≠ 0)
    (n68 : (orient R a z) ≠ 0)
    : False := by
  have eq0 : ((orient A K a)) + -((orient A K z)) + -((orient K a z)) + ((orient A a z)) = 0 := by
    unfold orient
    ring
  have eq1 : ((orient A B a)) + -((orient A B c)) + -((orient B a c)) + ((orient A a c)) = 0 := by
    unfold orient
    ring
  have eq2 : ((orient A B a)) + -((orient A B o)) + -((orient B a o)) + ((orient A a o)) = 0 := by
    unfold orient
    ring
  have eq3 : -((orient K R a)) + ((orient K R o)) + -((orient K a o)) + ((orient R a o)) = 0 := by
    unfold orient
    ring
  have eq4 : -((orient B R a)) + ((orient B R z)) + -((orient B a z)) + ((orient R a z)) = 0 := by
    unfold orient
    ring
  have eq5 : -((orient B R a)) + ((orient B R o)) + -((orient B a o)) + ((orient R a o)) = 0 := by
    unfold orient
    ring
  have eq6 : -((orient A K R) * (orient A B a)) + ((orient A B R) * (orient A K a)) + -((orient A R a) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq7 : -((orient A K R) * (orient A B c)) + ((orient A B R) * (orient A K c)) + -((orient A R c) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq8 : -((orient A K R) * (orient A B z)) + ((orient A B R) * (orient A K z)) + -((orient A R z) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq9 : -((orient A K R) * (orient A B o)) + ((orient A B R) * (orient A K o)) + -((orient A R o) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq10 : -((orient A K R) * (orient A a c)) + -((orient A R a) * (orient A K c)) + ((orient A R c) * (orient A K a)) = 0 := by
    unfold orient
    ring
  have eq11 : -((orient A K R) * (orient A a o)) + -((orient A R a) * (orient A K o)) + ((orient A R o) * (orient A K a)) = 0 := by
    unfold orient
    ring
  have eq12 : -((orient A B R) * (orient A a z)) + -((orient A R a) * (orient A B z)) + ((orient A R z) * (orient A B a)) = 0 := by
    unfold orient
    ring
  have eq13 : -((orient A K R) * (orient B R a)) + ((orient A B R) * (orient K R a)) + ((orient A R a) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq14 : -((orient A K R) * (orient B R z)) + ((orient A B R) * (orient K R z)) + ((orient A R z) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq15 : ((orient A K R) * (orient B K o)) + -((orient A B K) * (orient K R o)) + -((orient A K o) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq16 : ((orient A K R) * (orient K o z)) + ((orient A K z) * (orient K R o)) + -((orient A K o) * (orient K R z)) = 0 := by
    unfold orient
    ring
  have eq17 : ((orient A B K) * (orient K a c)) + -((orient A K a) * (orient B K c)) + ((orient A K c) * (orient B K a)) = 0 := by
    unfold orient
    ring
  have eq18 : ((orient A K a) * (orient K o z)) + ((orient A K z) * (orient K a o)) + -((orient A K o) * (orient K a z)) = 0 := by
    unfold orient
    ring
  have eq19 : -((orient A B R) * (orient B K o)) + ((orient A B K) * (orient B R o)) + ((orient A B o) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq20 : -((orient A B K) * (orient B c z)) + ((orient A B c) * (orient B K z)) + -((orient A B z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq21 : -((orient A B a) * (orient B c z)) + ((orient A B c) * (orient B a z)) + -((orient A B z) * (orient B a c)) = 0 := by
    unfold orient
    ring
  have eq22 : ((orient A B a) * (orient B o z)) + ((orient A B z) * (orient B a o)) + -((orient A B o) * (orient B a z)) = 0 := by
    unfold orient
    ring
  have eq23 : -((orient A R a) * (orient K a z)) + ((orient A K a) * (orient R a z)) + ((orient A a z) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq24 : -((orient A R a) * (orient K a o)) + ((orient A K a) * (orient R a o)) + ((orient A a o) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq25 : -((orient A R a) * (orient B a z)) + ((orient A B a) * (orient R a z)) + ((orient A a z) * (orient B R a)) = 0 := by
    unfold orient
    ring
  have eq26 : -((orient A R a) * (orient B a o)) + ((orient A B a) * (orient R a o)) + ((orient A a o) * (orient B R a)) = 0 := by
    unfold orient
    ring
  have eq27 : -((orient A K a) * (orient B a o)) + ((orient A B a) * (orient K a o)) + ((orient A a o) * (orient B K a)) = 0 := by
    unfold orient
    ring
  have eq28 : ((orient A K a) * (orient a c z)) + -((orient A a c) * (orient K a z)) + ((orient A a z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have eq29 : ((orient A B a) * (orient a c z)) + -((orient A a c) * (orient B a z)) + ((orient A a z) * (orient B a c)) = 0 := by
    unfold orient
    ring
  have eq30 : -((orient A K c) * (orient B c z)) + ((orient A B c) * (orient K c z)) + ((orient A c z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq31 : -((orient A K c) * (orient a c z)) + ((orient A a c) * (orient K c z)) + -((orient A c z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have eq32 : -((orient A B c) * (orient a c z)) + ((orient A a c) * (orient B c z)) + -((orient A c z) * (orient B a c)) = 0 := by
    unfold orient
    ring
  by_cases s0 : 0 < (orient A K a)
  ·
    have s1 : 0 < (orient A B a) := by
      by_contra hn
      have s1n : (orient A B a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n3
      have p2 : (orient A K R) * (orient A B a) < 0 := mul_neg_of_pos_of_neg h8 s1n
      have p3 : 0 < (orient A B R) * (orient A K a) := mul_pos h2 s0
      have p4 : (orient A R a) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h14 h1
      linarith only [eq6, p2, p3, p4]
    by_cases s5 : 0 < (orient A a c)
    ·
      have s6 : 0 < (orient A K c) := by
        by_contra hn
        have s6n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n11
        have p7 : 0 < (orient A K R) * (orient A a c) := mul_pos h8 s5
        have p8 : 0 < (orient A R a) * (orient A K c) := mul_pos_of_neg_of_neg h14 s6n
        have p9 : (orient A R c) * (orient A K a) < 0 := mul_neg_of_neg_of_pos h16 s0
        linarith only [eq10, p7, p8, p9]
      have s10 : 0 < (orient A B c) := by
        by_contra hn
        have s10n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
        have p11 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s10n
        have p12 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s6
        have p13 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
        linarith only [eq7, p11, p12, p13]
      have s14 : 0 < (orient A B z) := by
        by_contra hn
        have s14n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
        have p15 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
        have p16 : 0 < (orient A B c) * (orient B K z) := mul_pos s10 h34
        have p17 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s14n h32
        linarith only [eq20, p15, p16, p17]
      have s18 : 0 < (orient B a c) := by
        by_contra hn
        have s18n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
        have p19 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s1 h48
        have p20 : 0 < (orient A B c) * (orient B a z) := mul_pos s10 h43
        have p21 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s14 s18n
        linarith only [eq21, p19, p20, p21]
      have s22 : 0 < (orient A a z) := by
        by_contra hn
        have s22n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n22
        have p23 : (orient A B a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s1 h79
        have p24 : 0 < (orient A a c) * (orient B a z) := mul_pos s5 h43
        have p25 : (orient A a z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s22n s18
        linarith only [eq29, p23, p24, p25]
      have s26 : (orient A c z) < 0 := by
        by_contra hn
        have s26n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
        have p27 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s6 h48
        have p28 : 0 < (orient A B c) * (orient K c z) := mul_pos s10 h63
        have p29 : 0 < (orient A c z) * (orient B K c) := mul_pos s26n h32
        linarith only [eq30, p27, p28, p29]
      have s30 : (orient K a c) < 0 := by
        by_contra hn
        have s30n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
        have p31 : (orient A K c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s6 h79
        have p32 : 0 < (orient A a c) * (orient K c z) := mul_pos s5 h63
        have p33 : (orient A c z) * (orient K a c) < 0 := mul_neg_of_neg_of_pos s26 s30n
        linarith only [eq31, p31, p32, p33]
      have s34 : (orient K a z) < 0 := by
        by_contra hn
        have s34n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
        have p35 : (orient A K a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s0 h79
        have p36 : 0 < (orient A a c) * (orient K a z) := mul_pos s5 s34n
        have p37 : (orient A a z) * (orient K a c) < 0 := mul_neg_of_pos_of_neg s22 s30
        linarith only [eq28, p35, p36, p37]
      have s38 : 0 < (orient A K z) := by
        by_contra hn
        have s38n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
        linarith only [eq0, s0, s38n, s34, s22]
      by_cases s39 : 0 < (orient B R a)
      ·
        have s40 : 0 < (orient K R a) := by
          by_contra hn
          have s40n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
          have p41 : 0 < (orient A K R) * (orient B R a) := mul_pos h8 s39
          have p42 : (orient A B R) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h2 s40n
          have p43 : (orient A R a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h14 h29
          linarith only [eq13, p41, p42, p43]
        have s44 : (orient R a z) < 0 := by
          by_contra hn
          have s44n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
          have p45 : (orient A R a) * (orient B a z) < 0 := mul_neg_of_neg_of_pos h14 h43
          have p46 : 0 < (orient A B a) * (orient R a z) := mul_pos s1 s44n
          have p47 : 0 < (orient A a z) * (orient B R a) := mul_pos s22 s39
          linarith only [eq25, p45, p46, p47]
        have s48 : 0 < (orient B R z) := by
          by_contra hn
          have s48n : (orient B R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n39
          linarith only [eq4, s39, s48n, h43, s44]
        have s49 : 0 < (orient K R z) := by
          by_contra hn
          have s49n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
          have p50 : 0 < (orient A K R) * (orient B R z) := mul_pos h8 s48
          have p51 : (orient A B R) * (orient K R z) < 0 := mul_neg_of_pos_of_neg h2 s49n
          have p52 : (orient A R z) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h18 h29
          linarith only [eq14, p50, p51, p52]
        by_cases s53 : 0 < (orient A K o)
        ·
          have s54 : 0 < (orient A B o) := by
            by_contra hn
            have s54n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
            have p55 : (orient A K R) * (orient A B o) < 0 := mul_neg_of_pos_of_neg h8 s54n
            have p56 : 0 < (orient A B R) * (orient A K o) := mul_pos h2 s53
            have p57 : (orient A R o) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h17 h1
            linarith only [eq9, p55, p56, p57]
          have s58 : (orient K a o) < 0 := by
            by_contra hn
            have s58n : 0 < (orient K a o) := lt_of_le_of_ne (le_of_not_gt hn) n57.symm
            have p59 : 0 < (orient A K a) * (orient K o z) := mul_pos s0 h64
            have p60 : 0 < (orient A K z) * (orient K a o) := mul_pos s38 s58n
            have p61 : (orient A K o) * (orient K a z) < 0 := mul_neg_of_pos_of_neg s53 s34
            linarith only [eq18, p59, p60, p61]
          have s62 : 0 < (orient B a o) := by
            by_contra hn
            have s62n : (orient B a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n42
            have p63 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s1 h49
            have p64 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s14 s62n
            have p65 : 0 < (orient A B o) * (orient B a z) := mul_pos s54 h43
            linarith only [eq22, p63, p64, p65]
          have p66 : 0 < (orient A K a) * (orient B a o) := mul_pos s0 s62
          have p67 : (orient A B a) * (orient K a o) < 0 := mul_neg_of_pos_of_neg s1 s58
          have p68 : (orient A a o) * (orient B K a) < 0 := mul_neg_of_neg_of_pos h21 h30
          linarith only [eq27, p66, p67, p68]
        · have s53n : (orient A K o) < 0 := lt_of_le_of_ne (le_of_not_gt s53) n12
          have s69 : 0 < (orient K R o) := by
            by_contra hn
            have s69n : (orient K R o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n53
            have p70 : 0 < (orient A K R) * (orient B K o) := mul_pos h8 h33
            have p71 : (orient A B K) * (orient K R o) < 0 := mul_neg_of_pos_of_neg h1 s69n
            have p72 : (orient A K o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s53n h29
            linarith only [eq15, p70, p71, p72]
          have p73 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
          have p74 : 0 < (orient A K z) * (orient K R o) := mul_pos s38 s69
          have p75 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s53n s49
          linarith only [eq16, p73, p74, p75]
      · have s39n : (orient B R a) < 0 := lt_of_le_of_ne (le_of_not_gt s39) n35
        have s76 : (orient B a o) < 0 := by
          by_contra hn
          have s76n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
          have p77 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s76n
          have p78 : 0 < (orient A B a) * (orient R a o) := mul_pos s1 h67
          have p79 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s39n
          linarith only [eq26, p77, p78, p79]
        have s80 : (orient B R o) < 0 := by
          by_contra hn
          have s80n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
          linarith only [eq5, s39n, s80n, s76, h67]
        have s81 : 0 < (orient A B o) := by
          by_contra hn
          have s81n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
          have p82 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
          have p83 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s80
          have p84 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s81n h29
          linarith only [eq19, p82, p83, p84]
        have p85 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s1 h49
        have p86 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s14 s76
        have p87 : 0 < (orient A B o) * (orient B a z) := mul_pos s81 h43
        linarith only [eq22, p85, p86, p87]
    · have s5n : (orient A a c) < 0 := lt_of_le_of_ne (le_of_not_gt s5) n20
      by_cases s88 : 0 < (orient K a z)
      ·
        by_cases s89 : 0 < (orient A B c)
        ·
          have s90 : 0 < (orient A B z) := by
            by_contra hn
            have s90n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
            have p91 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
            have p92 : 0 < (orient A B c) * (orient B K z) := mul_pos s89 h34
            have p93 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s90n h32
            linarith only [eq20, p91, p92, p93]
          have s94 : 0 < (orient B a c) := by
            by_contra hn
            have s94n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
            have p95 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s1 h48
            have p96 : 0 < (orient A B c) * (orient B a z) := mul_pos s89 h43
            have p97 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s90 s94n
            linarith only [eq21, p95, p96, p97]
          have s98 : 0 < (orient A c z) := by
            by_contra hn
            have s98n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
            have p99 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s89 h79
            have p100 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s5n h48
            have p101 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s98n s94
            linarith only [eq32, p99, p100, p101]
          have s102 : (orient A K c) < 0 := by
            by_contra hn
            have s102n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
            have p103 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s102n h48
            have p104 : 0 < (orient A B c) * (orient K c z) := mul_pos s89 h63
            have p105 : 0 < (orient A c z) * (orient B K c) := mul_pos s98 h32
            linarith only [eq30, p103, p104, p105]
          have s106 : (orient K a c) < 0 := by
            by_contra hn
            have s106n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
            have p107 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s102 h79
            have p108 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s5n h63
            have p109 : 0 < (orient A c z) * (orient K a c) := mul_pos s98 s106n
            linarith only [eq31, p107, p108, p109]
          have p110 : (orient A B K) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h1 s106
          have p111 : 0 < (orient A K a) * (orient B K c) := mul_pos s0 h32
          have p112 : (orient A K c) * (orient B K a) < 0 := mul_neg_of_neg_of_pos s102 h30
          linarith only [eq17, p110, p111, p112]
        · have s89n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt s89) n5
          have s113 : (orient A K c) < 0 := by
            by_contra hn
            have s113n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
            have p114 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s89n
            have p115 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s113n
            have p116 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
            linarith only [eq7, p114, p115, p116]
          have s117 : 0 < (orient K a c) := by
            by_contra hn
            have s117n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
            have p118 : (orient A B K) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h1 s117n
            have p119 : 0 < (orient A K a) * (orient B K c) := mul_pos s0 h32
            have p120 : (orient A K c) * (orient B K a) < 0 := mul_neg_of_neg_of_pos s113 h30
            linarith only [eq17, p118, p119, p120]
          have s121 : 0 < (orient A c z) := by
            by_contra hn
            have s121n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
            have p122 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s113 h48
            have p123 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s89n h63
            have p124 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s121n h32
            linarith only [eq30, p122, p123, p124]
          have p125 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s113 h79
          have p126 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s5n h63
          have p127 : 0 < (orient A c z) * (orient K a c) := mul_pos s121 s117
          linarith only [eq31, p125, p126, p127]
      · have s88n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt s88) n58
        by_cases s128 : 0 < (orient A K z)
        ·
          have s129 : 0 < (orient A B z) := by
            by_contra hn
            have s129n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
            have p130 : (orient A K R) * (orient A B z) < 0 := mul_neg_of_pos_of_neg h8 s129n
            have p131 : 0 < (orient A B R) * (orient A K z) := mul_pos h2 s128
            have p132 : (orient A R z) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h18 h1
            linarith only [eq8, p130, p131, p132]
          by_cases s133 : 0 < (orient B R a)
          ·
            have s134 : 0 < (orient K R a) := by
              by_contra hn
              have s134n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
              have p135 : 0 < (orient A K R) * (orient B R a) := mul_pos h8 s133
              have p136 : (orient A B R) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h2 s134n
              have p137 : (orient A R a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h14 h29
              linarith only [eq13, p135, p136, p137]
            by_cases s138 : 0 < (orient A B c)
            ·
              have s139 : 0 < (orient B a c) := by
                by_contra hn
                have s139n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
                have p140 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s1 h48
                have p141 : 0 < (orient A B c) * (orient B a z) := mul_pos s138 h43
                have p142 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s129 s139n
                linarith only [eq21, p140, p141, p142]
              have s143 : 0 < (orient A c z) := by
                by_contra hn
                have s143n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
                have p144 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s138 h79
                have p145 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s5n h48
                have p146 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s143n s139
                linarith only [eq32, p144, p145, p146]
              have s147 : (orient A K c) < 0 := by
                by_contra hn
                have s147n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
                have p148 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s147n h48
                have p149 : 0 < (orient A B c) * (orient K c z) := mul_pos s138 h63
                have p150 : 0 < (orient A c z) * (orient B K c) := mul_pos s143 h32
                linarith only [eq30, p148, p149, p150]
              have s151 : (orient K a c) < 0 := by
                by_contra hn
                have s151n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
                have p152 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s147 h79
                have p153 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s5n h63
                have p154 : 0 < (orient A c z) * (orient K a c) := mul_pos s143 s151n
                linarith only [eq31, p152, p153, p154]
              have p155 : (orient A B K) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h1 s151
              have p156 : 0 < (orient A K a) * (orient B K c) := mul_pos s0 h32
              have p157 : (orient A K c) * (orient B K a) < 0 := mul_neg_of_neg_of_pos s147 h30
              linarith only [eq17, p155, p156, p157]
            · have s138n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt s138) n5
              have s158 : (orient A K c) < 0 := by
                by_contra hn
                have s158n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
                have p159 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s138n
                have p160 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s158n
                have p161 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
                linarith only [eq7, p159, p160, p161]
              have s162 : 0 < (orient K a c) := by
                by_contra hn
                have s162n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
                have p163 : (orient A B K) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h1 s162n
                have p164 : 0 < (orient A K a) * (orient B K c) := mul_pos s0 h32
                have p165 : (orient A K c) * (orient B K a) < 0 := mul_neg_of_neg_of_pos s158 h30
                linarith only [eq17, p163, p164, p165]
              have s166 : 0 < (orient A a z) := by
                by_contra hn
                have s166n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n22
                have p167 : (orient A K a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s0 h79
                have p168 : 0 < (orient A a c) * (orient K a z) := mul_pos_of_neg_of_neg s5n s88n
                have p169 : (orient A a z) * (orient K a c) < 0 := mul_neg_of_neg_of_pos s166n s162
                linarith only [eq28, p167, p168, p169]
              have s170 : 0 < (orient A c z) := by
                by_contra hn
                have s170n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
                have p171 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s158 h48
                have p172 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s138n h63
                have p173 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s170n h32
                linarith only [eq30, p171, p172, p173]
              have p174 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s158 h79
              have p175 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s5n h63
              have p176 : 0 < (orient A c z) * (orient K a c) := mul_pos s170 s162
              linarith only [eq31, p174, p175, p176]
          · have s133n : (orient B R a) < 0 := lt_of_le_of_ne (le_of_not_gt s133) n35
            have s177 : (orient B a o) < 0 := by
              by_contra hn
              have s177n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
              have p178 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s177n
              have p179 : 0 < (orient A B a) * (orient R a o) := mul_pos s1 h67
              have p180 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s133n
              linarith only [eq26, p178, p179, p180]
            have s181 : (orient B R o) < 0 := by
              by_contra hn
              have s181n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
              linarith only [eq5, s133n, s181n, s177, h67]
            have s182 : 0 < (orient A B o) := by
              by_contra hn
              have s182n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
              have p183 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
              have p184 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s181
              have p185 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s182n h29
              linarith only [eq19, p183, p184, p185]
            have p186 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s1 h49
            have p187 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s129 s177
            have p188 : 0 < (orient A B o) * (orient B a z) := mul_pos s182 h43
            linarith only [eq22, p186, p187, p188]
        · have s128n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt s128) n13
          have s189 : (orient A a z) < 0 := by
            by_contra hn
            have s189n : 0 < (orient A a z) := lt_of_le_of_ne (le_of_not_gt hn) n22.symm
            linarith only [eq0, s0, s128n, s88n, s189n]
          have s190 : (orient K a c) < 0 := by
            by_contra hn
            have s190n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
            have p191 : (orient A K a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s0 h79
            have p192 : 0 < (orient A a c) * (orient K a z) := mul_pos_of_neg_of_neg s5n s88n
            have p193 : (orient A a z) * (orient K a c) < 0 := mul_neg_of_neg_of_pos s189 s190n
            linarith only [eq28, p191, p192, p193]
          have s194 : 0 < (orient A K c) := by
            by_contra hn
            have s194n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n11
            have p195 : (orient A B K) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h1 s190
            have p196 : 0 < (orient A K a) * (orient B K c) := mul_pos s0 h32
            have p197 : (orient A K c) * (orient B K a) < 0 := mul_neg_of_neg_of_pos s194n h30
            linarith only [eq17, p195, p196, p197]
          have s198 : 0 < (orient A B c) := by
            by_contra hn
            have s198n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
            have p199 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s198n
            have p200 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s194
            have p201 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
            linarith only [eq7, p199, p200, p201]
          have s202 : 0 < (orient A B z) := by
            by_contra hn
            have s202n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
            have p203 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
            have p204 : 0 < (orient A B c) * (orient B K z) := mul_pos s198 h34
            have p205 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s202n h32
            linarith only [eq20, p203, p204, p205]
          have s206 : 0 < (orient B a c) := by
            by_contra hn
            have s206n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
            have p207 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s1 h48
            have p208 : 0 < (orient A B c) * (orient B a z) := mul_pos s198 h43
            have p209 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s202 s206n
            linarith only [eq21, p207, p208, p209]
          have s210 : (orient A c z) < 0 := by
            by_contra hn
            have s210n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
            have p211 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s194 h48
            have p212 : 0 < (orient A B c) * (orient K c z) := mul_pos s198 h63
            have p213 : 0 < (orient A c z) * (orient B K c) := mul_pos s210n h32
            linarith only [eq30, p211, p212, p213]
          have p214 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s198 h79
          have p215 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s5n h48
          have p216 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s210 s206
          linarith only [eq32, p214, p215, p216]
  · have s0n : (orient A K a) < 0 := lt_of_le_of_ne (le_of_not_gt s0) n9
    have s217 : (orient A K o) < 0 := by
      by_contra hn
      have s217n : 0 < (orient A K o) := lt_of_le_of_ne (le_of_not_gt hn) n12.symm
      have p218 : (orient A K R) * (orient A a o) < 0 := mul_neg_of_pos_of_neg h8 h21
      have p219 : (orient A R a) * (orient A K o) < 0 := mul_neg_of_neg_of_pos h14 s217n
      have p220 : 0 < (orient A R o) * (orient A K a) := mul_pos_of_neg_of_neg h17 s0n
      linarith only [eq11, p218, p219, p220]
    have s221 : 0 < (orient K R o) := by
      by_contra hn
      have s221n : (orient K R o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n53
      have p222 : 0 < (orient A K R) * (orient B K o) := mul_pos h8 h33
      have p223 : (orient A B K) * (orient K R o) < 0 := mul_neg_of_pos_of_neg h1 s221n
      have p224 : (orient A K o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s217 h29
      linarith only [eq15, p222, p223, p224]
    by_cases s225 : 0 < (orient A B a)
    ·
      by_cases s226 : 0 < (orient A a c)
      ·
        by_cases s227 : 0 < (orient A a z)
        ·
          have s228 : 0 < (orient A B z) := by
            by_contra hn
            have s228n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
            have p229 : 0 < (orient A B R) * (orient A a z) := mul_pos h2 s227
            have p230 : 0 < (orient A R a) * (orient A B z) := mul_pos_of_neg_of_neg h14 s228n
            have p231 : (orient A R z) * (orient A B a) < 0 := mul_neg_of_neg_of_pos h18 s225
            linarith only [eq12, p229, p230, p231]
          have s232 : 0 < (orient B a c) := by
            by_contra hn
            have s232n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
            have p233 : (orient A B a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s225 h79
            have p234 : 0 < (orient A a c) * (orient B a z) := mul_pos s226 h43
            have p235 : (orient A a z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s227 s232n
            linarith only [eq29, p233, p234, p235]
          by_cases s236 : 0 < (orient A K c)
          ·
            have s237 : 0 < (orient A B c) := by
              by_contra hn
              have s237n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
              have p238 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s237n
              have p239 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s236
              have p240 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
              linarith only [eq7, p238, p239, p240]
            have s241 : (orient K a c) < 0 := by
              by_contra hn
              have s241n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
              have p242 : 0 < (orient A B K) * (orient K a c) := mul_pos h1 s241n
              have p243 : (orient A K a) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s0n h32
              have p244 : 0 < (orient A K c) * (orient B K a) := mul_pos s236 h30
              linarith only [eq17, p242, p243, p244]
            have s245 : (orient A c z) < 0 := by
              by_contra hn
              have s245n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
              have p246 : (orient A K c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s236 h48
              have p247 : 0 < (orient A B c) * (orient K c z) := mul_pos s237 h63
              have p248 : 0 < (orient A c z) * (orient B K c) := mul_pos s245n h32
              linarith only [eq30, p246, p247, p248]
            by_cases s249 : 0 < (orient K R a)
            ·
              have s250 : 0 < (orient K a o) := by
                by_contra hn
                have s250n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
                have p251 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s250n
                have p252 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
                have p253 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s249
                linarith only [eq24, p251, p252, p253]
              by_cases s254 : 0 < (orient B R a)
              ·
                have s255 : (orient R a z) < 0 := by
                  by_contra hn
                  have s255n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
                  have p256 : (orient A R a) * (orient B a z) < 0 := mul_neg_of_neg_of_pos h14 h43
                  have p257 : 0 < (orient A B a) * (orient R a z) := mul_pos s225 s255n
                  have p258 : 0 < (orient A a z) * (orient B R a) := mul_pos s227 s254
                  linarith only [eq25, p256, p257, p258]
                have s259 : 0 < (orient B R z) := by
                  by_contra hn
                  have s259n : (orient B R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n39
                  linarith only [eq4, s254, s259n, h43, s255]
                have s260 : 0 < (orient K R z) := by
                  by_contra hn
                  have s260n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
                  have p261 : 0 < (orient A K R) * (orient B R z) := mul_pos h8 s259
                  have p262 : (orient A B R) * (orient K R z) < 0 := mul_neg_of_pos_of_neg h2 s260n
                  have p263 : (orient A R z) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h18 h29
                  linarith only [eq14, p261, p262, p263]
                have s264 : (orient A K z) < 0 := by
                  by_contra hn
                  have s264n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
                  have p265 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
                  have p266 : 0 < (orient A K z) * (orient K R o) := mul_pos s264n s221
                  have p267 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s217 s260
                  linarith only [eq16, p265, p266, p267]
                have s268 : 0 < (orient K a z) := by
                  by_contra hn
                  have s268n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
                  have p269 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
                  have p270 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s264 s250
                  have p271 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s217 s268n
                  linarith only [eq18, p269, p270, p271]
                have p272 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s268
                have p273 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0n s255
                have p274 : 0 < (orient A a z) * (orient K R a) := mul_pos s227 s249
                linarith only [eq23, p272, p273, p274]
              · have s254n : (orient B R a) < 0 := lt_of_le_of_ne (le_of_not_gt s254) n35
                have s275 : (orient B a o) < 0 := by
                  by_contra hn
                  have s275n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
                  have p276 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s275n
                  have p277 : 0 < (orient A B a) * (orient R a o) := mul_pos s225 h67
                  have p278 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s254n
                  linarith only [eq26, p276, p277, p278]
                have s279 : (orient B R o) < 0 := by
                  by_contra hn
                  have s279n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
                  linarith only [eq5, s254n, s279n, s275, h67]
                have s280 : 0 < (orient A B o) := by
                  by_contra hn
                  have s280n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
                  have p281 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                  have p282 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s279
                  have p283 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s280n h29
                  linarith only [eq19, p281, p282, p283]
                have p284 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s225 h49
                have p285 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s228 s275
                have p286 : 0 < (orient A B o) * (orient B a z) := mul_pos s280 h43
                linarith only [eq22, p284, p285, p286]
            · have s249n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt s249) n50
              have s287 : 0 < (orient K a o) := by
                by_contra hn
                have s287n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
                linarith only [eq3, s249n, s221, s287n, h67]
              have s288 : (orient B R a) < 0 := by
                by_contra hn
                have s288n : 0 < (orient B R a) := lt_of_le_of_ne (le_of_not_gt hn) n35.symm
                have p289 : 0 < (orient A K R) * (orient B R a) := mul_pos h8 s288n
                have p290 : (orient A B R) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h2 s249n
                have p291 : (orient A R a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h14 h29
                linarith only [eq13, p289, p290, p291]
              have s292 : (orient B a o) < 0 := by
                by_contra hn
                have s292n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
                have p293 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s292n
                have p294 : 0 < (orient A B a) * (orient R a o) := mul_pos s225 h67
                have p295 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s288
                linarith only [eq26, p293, p294, p295]
              have s296 : (orient B R o) < 0 := by
                by_contra hn
                have s296n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
                linarith only [eq5, s288, s296n, s292, h67]
              have s297 : 0 < (orient A B o) := by
                by_contra hn
                have s297n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
                have p298 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                have p299 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s296
                have p300 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s297n h29
                linarith only [eq19, p298, p299, p300]
              have p301 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s225 h49
              have p302 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s228 s292
              have p303 : 0 < (orient A B o) * (orient B a z) := mul_pos s297 h43
              linarith only [eq22, p301, p302, p303]
          · have s236n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt s236) n11
            by_cases s304 : 0 < (orient K R a)
            ·
              have s305 : 0 < (orient K a o) := by
                by_contra hn
                have s305n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
                have p306 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s305n
                have p307 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
                have p308 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s304
                linarith only [eq24, p306, p307, p308]
              by_cases s309 : 0 < (orient B R a)
              ·
                have s310 : (orient R a z) < 0 := by
                  by_contra hn
                  have s310n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
                  have p311 : (orient A R a) * (orient B a z) < 0 := mul_neg_of_neg_of_pos h14 h43
                  have p312 : 0 < (orient A B a) * (orient R a z) := mul_pos s225 s310n
                  have p313 : 0 < (orient A a z) * (orient B R a) := mul_pos s227 s309
                  linarith only [eq25, p311, p312, p313]
                have s314 : 0 < (orient B R z) := by
                  by_contra hn
                  have s314n : (orient B R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n39
                  linarith only [eq4, s309, s314n, h43, s310]
                have s315 : 0 < (orient K R z) := by
                  by_contra hn
                  have s315n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
                  have p316 : 0 < (orient A K R) * (orient B R z) := mul_pos h8 s314
                  have p317 : (orient A B R) * (orient K R z) < 0 := mul_neg_of_pos_of_neg h2 s315n
                  have p318 : (orient A R z) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h18 h29
                  linarith only [eq14, p316, p317, p318]
                have s319 : (orient A K z) < 0 := by
                  by_contra hn
                  have s319n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
                  have p320 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
                  have p321 : 0 < (orient A K z) * (orient K R o) := mul_pos s319n s221
                  have p322 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s217 s315
                  linarith only [eq16, p320, p321, p322]
                have s323 : 0 < (orient K a z) := by
                  by_contra hn
                  have s323n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
                  have p324 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
                  have p325 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s319 s305
                  have p326 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s217 s323n
                  linarith only [eq18, p324, p325, p326]
                have p327 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s323
                have p328 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0n s310
                have p329 : 0 < (orient A a z) * (orient K R a) := mul_pos s227 s304
                linarith only [eq23, p327, p328, p329]
              · have s309n : (orient B R a) < 0 := lt_of_le_of_ne (le_of_not_gt s309) n35
                have s330 : (orient B a o) < 0 := by
                  by_contra hn
                  have s330n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
                  have p331 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s330n
                  have p332 : 0 < (orient A B a) * (orient R a o) := mul_pos s225 h67
                  have p333 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s309n
                  linarith only [eq26, p331, p332, p333]
                have s334 : (orient B R o) < 0 := by
                  by_contra hn
                  have s334n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
                  linarith only [eq5, s309n, s334n, s330, h67]
                have s335 : 0 < (orient A B o) := by
                  by_contra hn
                  have s335n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
                  have p336 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                  have p337 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s334
                  have p338 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s335n h29
                  linarith only [eq19, p336, p337, p338]
                have p339 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s225 h49
                have p340 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s228 s330
                have p341 : 0 < (orient A B o) * (orient B a z) := mul_pos s335 h43
                linarith only [eq22, p339, p340, p341]
            · have s304n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt s304) n50
              have s342 : 0 < (orient K a o) := by
                by_contra hn
                have s342n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
                linarith only [eq3, s304n, s221, s342n, h67]
              have s343 : (orient B R a) < 0 := by
                by_contra hn
                have s343n : 0 < (orient B R a) := lt_of_le_of_ne (le_of_not_gt hn) n35.symm
                have p344 : 0 < (orient A K R) * (orient B R a) := mul_pos h8 s343n
                have p345 : (orient A B R) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h2 s304n
                have p346 : (orient A R a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h14 h29
                linarith only [eq13, p344, p345, p346]
              have s347 : (orient B a o) < 0 := by
                by_contra hn
                have s347n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
                have p348 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s347n
                have p349 : 0 < (orient A B a) * (orient R a o) := mul_pos s225 h67
                have p350 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s343
                linarith only [eq26, p348, p349, p350]
              have s351 : (orient B R o) < 0 := by
                by_contra hn
                have s351n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
                linarith only [eq5, s343, s351n, s347, h67]
              have s352 : 0 < (orient A B o) := by
                by_contra hn
                have s352n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
                have p353 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                have p354 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s351
                have p355 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s352n h29
                linarith only [eq19, p353, p354, p355]
              have p356 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s225 h49
              have p357 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s228 s347
              have p358 : 0 < (orient A B o) * (orient B a z) := mul_pos s352 h43
              linarith only [eq22, p356, p357, p358]
        · have s227n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s227) n22
          have s359 : (orient B a c) < 0 := by
            by_contra hn
            have s359n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
            have p360 : (orient A B a) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s225 h79
            have p361 : 0 < (orient A a c) * (orient B a z) := mul_pos s226 h43
            have p362 : (orient A a z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s227n s359n
            linarith only [eq29, p360, p361, p362]
          have s363 : 0 < (orient A B c) := by
            by_contra hn
            have s363n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
            linarith only [eq1, s225, s363n, s359, s226]
          have s364 : 0 < (orient A B z) := by
            by_contra hn
            have s364n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
            have p365 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
            have p366 : 0 < (orient A B c) * (orient B K z) := mul_pos s363 h34
            have p367 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s364n h32
            linarith only [eq20, p365, p366, p367]
          have p368 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s225 h48
          have p369 : 0 < (orient A B c) * (orient B a z) := mul_pos s363 h43
          have p370 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s364 s359
          linarith only [eq21, p368, p369, p370]
      · have s226n : (orient A a c) < 0 := lt_of_le_of_ne (le_of_not_gt s226) n20
        have s371 : (orient A K c) < 0 := by
          by_contra hn
          have s371n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
          have p372 : (orient A K R) * (orient A a c) < 0 := mul_neg_of_pos_of_neg h8 s226n
          have p373 : (orient A R a) * (orient A K c) < 0 := mul_neg_of_neg_of_pos h14 s371n
          have p374 : 0 < (orient A R c) * (orient A K a) := mul_pos_of_neg_of_neg h16 s0n
          linarith only [eq10, p372, p373, p374]
        by_cases s375 : 0 < (orient A a z)
        ·
          have s376 : 0 < (orient A B z) := by
            by_contra hn
            have s376n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
            have p377 : 0 < (orient A B R) * (orient A a z) := mul_pos h2 s375
            have p378 : 0 < (orient A R a) * (orient A B z) := mul_pos_of_neg_of_neg h14 s376n
            have p379 : (orient A R z) * (orient A B a) < 0 := mul_neg_of_neg_of_pos h18 s225
            linarith only [eq12, p377, p378, p379]
          by_cases s380 : 0 < (orient K R a)
          ·
            have s381 : 0 < (orient K a o) := by
              by_contra hn
              have s381n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
              have p382 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s381n
              have p383 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
              have p384 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s380
              linarith only [eq24, p382, p383, p384]
            by_cases s385 : 0 < (orient A c z)
            ·
              have s386 : (orient K a c) < 0 := by
                by_contra hn
                have s386n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
                have p387 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s371 h79
                have p388 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s226n h63
                have p389 : 0 < (orient A c z) * (orient K a c) := mul_pos s385 s386n
                linarith only [eq31, p387, p388, p389]
              by_cases s390 : 0 < (orient B R a)
              ·
                have s391 : (orient R a z) < 0 := by
                  by_contra hn
                  have s391n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
                  have p392 : (orient A R a) * (orient B a z) < 0 := mul_neg_of_neg_of_pos h14 h43
                  have p393 : 0 < (orient A B a) * (orient R a z) := mul_pos s225 s391n
                  have p394 : 0 < (orient A a z) * (orient B R a) := mul_pos s375 s390
                  linarith only [eq25, p392, p393, p394]
                have s395 : 0 < (orient B R z) := by
                  by_contra hn
                  have s395n : (orient B R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n39
                  linarith only [eq4, s390, s395n, h43, s391]
                have s396 : 0 < (orient K R z) := by
                  by_contra hn
                  have s396n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
                  have p397 : 0 < (orient A K R) * (orient B R z) := mul_pos h8 s395
                  have p398 : (orient A B R) * (orient K R z) < 0 := mul_neg_of_pos_of_neg h2 s396n
                  have p399 : (orient A R z) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h18 h29
                  linarith only [eq14, p397, p398, p399]
                have s400 : (orient A K z) < 0 := by
                  by_contra hn
                  have s400n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
                  have p401 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
                  have p402 : 0 < (orient A K z) * (orient K R o) := mul_pos s400n s221
                  have p403 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s217 s396
                  linarith only [eq16, p401, p402, p403]
                have s404 : 0 < (orient K a z) := by
                  by_contra hn
                  have s404n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
                  have p405 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
                  have p406 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s400 s381
                  have p407 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s217 s404n
                  linarith only [eq18, p405, p406, p407]
                have p408 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s404
                have p409 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0n s391
                have p410 : 0 < (orient A a z) * (orient K R a) := mul_pos s375 s380
                linarith only [eq23, p408, p409, p410]
              · have s390n : (orient B R a) < 0 := lt_of_le_of_ne (le_of_not_gt s390) n35
                have s411 : (orient B a o) < 0 := by
                  by_contra hn
                  have s411n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
                  have p412 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s411n
                  have p413 : 0 < (orient A B a) * (orient R a o) := mul_pos s225 h67
                  have p414 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s390n
                  linarith only [eq26, p412, p413, p414]
                have s415 : (orient B R o) < 0 := by
                  by_contra hn
                  have s415n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
                  linarith only [eq5, s390n, s415n, s411, h67]
                have s416 : 0 < (orient A B o) := by
                  by_contra hn
                  have s416n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
                  have p417 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                  have p418 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s415
                  have p419 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s416n h29
                  linarith only [eq19, p417, p418, p419]
                have p420 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s225 h49
                have p421 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s376 s411
                have p422 : 0 < (orient A B o) * (orient B a z) := mul_pos s416 h43
                linarith only [eq22, p420, p421, p422]
            · have s385n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt s385) n27
              have s423 : 0 < (orient A B c) := by
                by_contra hn
                have s423n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
                have p424 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s371 h48
                have p425 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s423n h63
                have p426 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s385n h32
                linarith only [eq30, p424, p425, p426]
              have s427 : 0 < (orient K a c) := by
                by_contra hn
                have s427n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
                have p428 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s371 h79
                have p429 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s226n h63
                have p430 : 0 < (orient A c z) * (orient K a c) := mul_pos_of_neg_of_neg s385n s427n
                linarith only [eq31, p428, p429, p430]
              have s431 : (orient B a c) < 0 := by
                by_contra hn
                have s431n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
                have p432 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s423 h79
                have p433 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s226n h48
                have p434 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s385n s431n
                linarith only [eq32, p432, p433, p434]
              have p435 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s225 h48
              have p436 : 0 < (orient A B c) * (orient B a z) := mul_pos s423 h43
              have p437 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s376 s431
              linarith only [eq21, p435, p436, p437]
          · have s380n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt s380) n50
            have s438 : 0 < (orient K a o) := by
              by_contra hn
              have s438n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
              linarith only [eq3, s380n, s221, s438n, h67]
            have s439 : (orient B R a) < 0 := by
              by_contra hn
              have s439n : 0 < (orient B R a) := lt_of_le_of_ne (le_of_not_gt hn) n35.symm
              have p440 : 0 < (orient A K R) * (orient B R a) := mul_pos h8 s439n
              have p441 : (orient A B R) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h2 s380n
              have p442 : (orient A R a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h14 h29
              linarith only [eq13, p440, p441, p442]
            have s443 : (orient B a o) < 0 := by
              by_contra hn
              have s443n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
              have p444 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s443n
              have p445 : 0 < (orient A B a) * (orient R a o) := mul_pos s225 h67
              have p446 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s439
              linarith only [eq26, p444, p445, p446]
            have s447 : (orient B R o) < 0 := by
              by_contra hn
              have s447n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
              linarith only [eq5, s439, s447n, s443, h67]
            have s448 : 0 < (orient A B o) := by
              by_contra hn
              have s448n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
              have p449 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
              have p450 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s447
              have p451 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s448n h29
              linarith only [eq19, p449, p450, p451]
            have p452 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s225 h49
            have p453 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s376 s443
            have p454 : 0 < (orient A B o) * (orient B a z) := mul_pos s448 h43
            linarith only [eq22, p452, p453, p454]
        · have s375n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s375) n22
          by_cases s455 : 0 < (orient K a z)
          ·
            have s456 : (orient A K z) < 0 := by
              by_contra hn
              have s456n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
              linarith only [eq0, s0n, s456n, s455, s375n]
            have s457 : 0 < (orient K a c) := by
              by_contra hn
              have s457n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
              have p458 : 0 < (orient A K a) * (orient a c z) := mul_pos_of_neg_of_neg s0n h79
              have p459 : (orient A a c) * (orient K a z) < 0 := mul_neg_of_neg_of_pos s226n s455
              have p460 : 0 < (orient A a z) * (orient K a c) := mul_pos_of_neg_of_neg s375n s457n
              linarith only [eq28, p458, p459, p460]
            have s461 : (orient A c z) < 0 := by
              by_contra hn
              have s461n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
              have p462 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s371 h79
              have p463 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s226n h63
              have p464 : 0 < (orient A c z) * (orient K a c) := mul_pos s461n s457
              linarith only [eq31, p462, p463, p464]
            have s465 : 0 < (orient A B c) := by
              by_contra hn
              have s465n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n5
              have p466 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s371 h48
              have p467 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s465n h63
              have p468 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s461 h32
              linarith only [eq30, p466, p467, p468]
            have s469 : (orient B a c) < 0 := by
              by_contra hn
              have s469n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
              have p470 : (orient A B c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s465 h79
              have p471 : 0 < (orient A a c) * (orient B c z) := mul_pos_of_neg_of_neg s226n h48
              have p472 : (orient A c z) * (orient B a c) < 0 := mul_neg_of_neg_of_pos s461 s469n
              linarith only [eq32, p470, p471, p472]
            have s473 : 0 < (orient A B z) := by
              by_contra hn
              have s473n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
              have p474 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
              have p475 : 0 < (orient A B c) * (orient B K z) := mul_pos s465 h34
              have p476 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s473n h32
              linarith only [eq20, p474, p475, p476]
            have p477 : (orient A B a) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s225 h48
            have p478 : 0 < (orient A B c) * (orient B a z) := mul_pos s465 h43
            have p479 : (orient A B z) * (orient B a c) < 0 := mul_neg_of_pos_of_neg s473 s469
            linarith only [eq21, p477, p478, p479]
          · have s455n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt s455) n58
            by_cases s480 : 0 < (orient A B z)
            ·
              by_cases s481 : 0 < (orient K a o)
              ·
                have s482 : 0 < (orient A K z) := by
                  by_contra hn
                  have s482n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
                  have p483 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
                  have p484 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s482n s481
                  have p485 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s217 s455n
                  linarith only [eq18, p483, p484, p485]
                have s486 : (orient K R z) < 0 := by
                  by_contra hn
                  have s486n : 0 < (orient K R z) := lt_of_le_of_ne (le_of_not_gt hn) n54.symm
                  have p487 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
                  have p488 : 0 < (orient A K z) * (orient K R o) := mul_pos s482 s221
                  have p489 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s217 s486n
                  linarith only [eq16, p487, p488, p489]
                have s490 : (orient B R z) < 0 := by
                  by_contra hn
                  have s490n : 0 < (orient B R z) := lt_of_le_of_ne (le_of_not_gt hn) n39.symm
                  have p491 : 0 < (orient A K R) * (orient B R z) := mul_pos h8 s490n
                  have p492 : (orient A B R) * (orient K R z) < 0 := mul_neg_of_pos_of_neg h2 s486
                  have p493 : (orient A R z) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h18 h29
                  linarith only [eq14, p491, p492, p493]
                by_cases s494 : 0 < (orient B R a)
                ·
                  have s495 : 0 < (orient R a z) := by
                    by_contra hn
                    have s495n : (orient R a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n68
                    linarith only [eq4, s494, s490, h43, s495n]
                  have s496 : 0 < (orient K R a) := by
                    by_contra hn
                    have s496n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
                    have p497 : 0 < (orient A K R) * (orient B R a) := mul_pos h8 s494
                    have p498 : (orient A B R) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h2 s496n
                    have p499 : (orient A R a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos h14 h29
                    linarith only [eq13, p497, p498, p499]
                  have p500 : 0 < (orient A R a) * (orient K a z) := mul_pos_of_neg_of_neg h14 s455n
                  have p501 : (orient A K a) * (orient R a z) < 0 := mul_neg_of_neg_of_pos s0n s495
                  have p502 : (orient A a z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s375n s496
                  linarith only [eq23, p500, p501, p502]
                · have s494n : (orient B R a) < 0 := lt_of_le_of_ne (le_of_not_gt s494) n35
                  have s503 : (orient R a z) < 0 := by
                    by_contra hn
                    have s503n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
                    have p504 : (orient A R a) * (orient B a z) < 0 := mul_neg_of_neg_of_pos h14 h43
                    have p505 : 0 < (orient A B a) * (orient R a z) := mul_pos s225 s503n
                    have p506 : 0 < (orient A a z) * (orient B R a) := mul_pos_of_neg_of_neg s375n s494n
                    linarith only [eq25, p504, p505, p506]
                  have s507 : (orient B a o) < 0 := by
                    by_contra hn
                    have s507n : 0 < (orient B a o) := lt_of_le_of_ne (le_of_not_gt hn) n42.symm
                    have p508 : (orient A R a) * (orient B a o) < 0 := mul_neg_of_neg_of_pos h14 s507n
                    have p509 : 0 < (orient A B a) * (orient R a o) := mul_pos s225 h67
                    have p510 : 0 < (orient A a o) * (orient B R a) := mul_pos_of_neg_of_neg h21 s494n
                    linarith only [eq26, p508, p509, p510]
                  have s511 : (orient B R o) < 0 := by
                    by_contra hn
                    have s511n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
                    linarith only [eq5, s494n, s511n, s507, h67]
                  have s512 : 0 < (orient A B o) := by
                    by_contra hn
                    have s512n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
                    have p513 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                    have p514 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s511
                    have p515 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s512n h29
                    linarith only [eq19, p513, p514, p515]
                  have p516 : (orient A B a) * (orient B o z) < 0 := mul_neg_of_pos_of_neg s225 h49
                  have p517 : (orient A B z) * (orient B a o) < 0 := mul_neg_of_pos_of_neg s480 s507
                  have p518 : 0 < (orient A B o) * (orient B a z) := mul_pos s512 h43
                  linarith only [eq22, p516, p517, p518]
              · have s481n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt s481) n57
                have s519 : 0 < (orient K R a) := by
                  by_contra hn
                  have s519n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
                  linarith only [eq3, s519n, s221, s481n, h67]
                have s520 : (orient A K z) < 0 := by
                  by_contra hn
                  have s520n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
                  have p521 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
                  have p522 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_pos_of_neg s520n s481n
                  have p523 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s217 s455n
                  linarith only [eq18, p521, p522, p523]
                have s524 : (orient R a z) < 0 := by
                  by_contra hn
                  have s524n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
                  have p525 : 0 < (orient A R a) * (orient K a z) := mul_pos_of_neg_of_neg h14 s455n
                  have p526 : (orient A K a) * (orient R a z) < 0 := mul_neg_of_neg_of_pos s0n s524n
                  have p527 : (orient A a z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s375n s519
                  linarith only [eq23, p525, p526, p527]
                have p528 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s481n
                have p529 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
                have p530 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s519
                linarith only [eq24, p528, p529, p530]
            · have s480n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt s480) n7
              have s531 : (orient A K z) < 0 := by
                by_contra hn
                have s531n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
                have p532 : (orient A K R) * (orient A B z) < 0 := mul_neg_of_pos_of_neg h8 s480n
                have p533 : 0 < (orient A B R) * (orient A K z) := mul_pos h2 s531n
                have p534 : (orient A R z) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h18 h1
                linarith only [eq8, p532, p533, p534]
              have s535 : (orient K a o) < 0 := by
                by_contra hn
                have s535n : 0 < (orient K a o) := lt_of_le_of_ne (le_of_not_gt hn) n57.symm
                have p536 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
                have p537 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s531 s535n
                have p538 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s217 s455n
                linarith only [eq18, p536, p537, p538]
              have s539 : (orient A B c) < 0 := by
                by_contra hn
                have s539n : 0 < (orient A B c) := lt_of_le_of_ne (le_of_not_gt hn) n5.symm
                have p540 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
                have p541 : 0 < (orient A B c) * (orient B K z) := mul_pos s539n h34
                have p542 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s480n h32
                linarith only [eq20, p540, p541, p542]
              have s543 : (orient K R a) < 0 := by
                by_contra hn
                have s543n : 0 < (orient K R a) := lt_of_le_of_ne (le_of_not_gt hn) n50.symm
                have p544 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s535
                have p545 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
                have p546 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s543n
                linarith only [eq24, p544, p545, p546]
              have s547 : 0 < (orient B a o) := by
                by_contra hn
                have s547n : (orient B a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n42
                have p548 : 0 < (orient A K a) * (orient B a o) := mul_pos_of_neg_of_neg s0n s547n
                have p549 : (orient A B a) * (orient K a o) < 0 := mul_neg_of_pos_of_neg s225 s535
                have p550 : (orient A a o) * (orient B K a) < 0 := mul_neg_of_neg_of_pos h21 h30
                linarith only [eq27, p548, p549, p550]
              have s551 : 0 < (orient A c z) := by
                by_contra hn
                have s551n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
                have p552 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s371 h48
                have p553 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s539 h63
                have p554 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s551n h32
                linarith only [eq30, p552, p553, p554]
              have s555 : (orient K a c) < 0 := by
                by_contra hn
                have s555n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
                have p556 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s371 h79
                have p557 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s226n h63
                have p558 : 0 < (orient A c z) * (orient K a c) := mul_pos s551 s555n
                linarith only [eq31, p556, p557, p558]
              linarith only [eq3, s543, s221, s535, h67]
    · have s225n : (orient A B a) < 0 := lt_of_le_of_ne (le_of_not_gt s225) n3
      by_cases s559 : 0 < (orient A a c)
      ·
        by_cases s560 : 0 < (orient A a z)
        ·
          by_cases s561 : 0 < (orient A B c)
          ·
            have s562 : 0 < (orient A B z) := by
              by_contra hn
              have s562n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
              have p563 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
              have p564 : 0 < (orient A B c) * (orient B K z) := mul_pos s561 h34
              have p565 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s562n h32
              linarith only [eq20, p563, p564, p565]
            by_cases s566 : 0 < (orient B a o)
            ·
              have s567 : (orient A B o) < 0 := by
                by_contra hn
                have s567n : 0 < (orient A B o) := lt_of_le_of_ne (le_of_not_gt hn) n6.symm
                linarith only [eq2, s225n, s567n, s566, h21]
              have s568 : 0 < (orient B R o) := by
                by_contra hn
                have s568n : (orient B R o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n38
                have p569 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                have p570 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s568n
                have p571 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s567 h29
                linarith only [eq19, p569, p570, p571]
              have p572 : 0 < (orient A B a) * (orient B o z) := mul_pos_of_neg_of_neg s225n h49
              have p573 : 0 < (orient A B z) * (orient B a o) := mul_pos s562 s566
              have p574 : (orient A B o) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s567 h43
              linarith only [eq22, p572, p573, p574]
            · have s566n : (orient B a o) < 0 := lt_of_le_of_ne (le_of_not_gt s566) n42
              have s575 : (orient B R a) < 0 := by
                by_contra hn
                have s575n : 0 < (orient B R a) := lt_of_le_of_ne (le_of_not_gt hn) n35.symm
                have p576 : 0 < (orient A R a) * (orient B a o) := mul_pos_of_neg_of_neg h14 s566n
                have p577 : (orient A B a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s225n h67
                have p578 : (orient A a o) * (orient B R a) < 0 := mul_neg_of_neg_of_pos h21 s575n
                linarith only [eq26, p576, p577, p578]
              have s579 : (orient K a o) < 0 := by
                by_contra hn
                have s579n : 0 < (orient K a o) := lt_of_le_of_ne (le_of_not_gt hn) n57.symm
                have p580 : 0 < (orient A K a) * (orient B a o) := mul_pos_of_neg_of_neg s0n s566n
                have p581 : (orient A B a) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s225n s579n
                have p582 : (orient A a o) * (orient B K a) < 0 := mul_neg_of_neg_of_pos h21 h30
                linarith only [eq27, p580, p581, p582]
              have s583 : 0 < (orient K R a) := by
                by_contra hn
                have s583n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
                linarith only [eq3, s583n, s221, s579, h67]
              have s584 : (orient B R o) < 0 := by
                by_contra hn
                have s584n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
                linarith only [eq5, s575, s584n, s566n, h67]
              have s585 : 0 < (orient A B o) := by
                by_contra hn
                have s585n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
                have p586 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                have p587 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s584
                have p588 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s585n h29
                linarith only [eq19, p586, p587, p588]
              have p589 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s579
              have p590 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
              have p591 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s583
              linarith only [eq24, p589, p590, p591]
          · have s561n : (orient A B c) < 0 := lt_of_le_of_ne (le_of_not_gt s561) n5
            have s592 : (orient A K c) < 0 := by
              by_contra hn
              have s592n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
              have p593 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s561n
              have p594 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s592n
              have p595 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
              linarith only [eq7, p593, p594, p595]
            have s596 : 0 < (orient A c z) := by
              by_contra hn
              have s596n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
              have p597 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s592 h48
              have p598 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s561n h63
              have p599 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s596n h32
              linarith only [eq30, p597, p598, p599]
            have s600 : (orient B a c) < 0 := by
              by_contra hn
              have s600n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
              have p601 : 0 < (orient A B c) * (orient a c z) := mul_pos_of_neg_of_neg s561n h79
              have p602 : (orient A a c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s559 h48
              have p603 : 0 < (orient A c z) * (orient B a c) := mul_pos s596 s600n
              linarith only [eq32, p601, p602, p603]
            have s604 : 0 < (orient A B z) := by
              by_contra hn
              have s604n : (orient A B z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n7
              have p605 : 0 < (orient A B a) * (orient B c z) := mul_pos_of_neg_of_neg s225n h48
              have p606 : (orient A B c) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s561n h43
              have p607 : 0 < (orient A B z) * (orient B a c) := mul_pos_of_neg_of_neg s604n s600
              linarith only [eq21, p605, p606, p607]
            by_cases s608 : 0 < (orient B a o)
            ·
              have s609 : (orient A B o) < 0 := by
                by_contra hn
                have s609n : 0 < (orient A B o) := lt_of_le_of_ne (le_of_not_gt hn) n6.symm
                linarith only [eq2, s225n, s609n, s608, h21]
              have s610 : 0 < (orient B R o) := by
                by_contra hn
                have s610n : (orient B R o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n38
                have p611 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                have p612 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s610n
                have p613 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s609 h29
                linarith only [eq19, p611, p612, p613]
              have p614 : 0 < (orient A B a) * (orient B o z) := mul_pos_of_neg_of_neg s225n h49
              have p615 : 0 < (orient A B z) * (orient B a o) := mul_pos s604 s608
              have p616 : (orient A B o) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s609 h43
              linarith only [eq22, p614, p615, p616]
            · have s608n : (orient B a o) < 0 := lt_of_le_of_ne (le_of_not_gt s608) n42
              have s617 : (orient B R a) < 0 := by
                by_contra hn
                have s617n : 0 < (orient B R a) := lt_of_le_of_ne (le_of_not_gt hn) n35.symm
                have p618 : 0 < (orient A R a) * (orient B a o) := mul_pos_of_neg_of_neg h14 s608n
                have p619 : (orient A B a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s225n h67
                have p620 : (orient A a o) * (orient B R a) < 0 := mul_neg_of_neg_of_pos h21 s617n
                linarith only [eq26, p618, p619, p620]
              have s621 : (orient K a o) < 0 := by
                by_contra hn
                have s621n : 0 < (orient K a o) := lt_of_le_of_ne (le_of_not_gt hn) n57.symm
                have p622 : 0 < (orient A K a) * (orient B a o) := mul_pos_of_neg_of_neg s0n s608n
                have p623 : (orient A B a) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s225n s621n
                have p624 : (orient A a o) * (orient B K a) < 0 := mul_neg_of_neg_of_pos h21 h30
                linarith only [eq27, p622, p623, p624]
              have s625 : 0 < (orient K R a) := by
                by_contra hn
                have s625n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
                linarith only [eq3, s625n, s221, s621, h67]
              have s626 : (orient B R o) < 0 := by
                by_contra hn
                have s626n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
                linarith only [eq5, s617, s626n, s608n, h67]
              have s627 : 0 < (orient A B o) := by
                by_contra hn
                have s627n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
                have p628 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
                have p629 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s626
                have p630 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s627n h29
                linarith only [eq19, p628, p629, p630]
              have p631 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s621
              have p632 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
              have p633 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s625
              linarith only [eq24, p631, p632, p633]
        · have s560n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s560) n22
          have s634 : (orient A B z) < 0 := by
            by_contra hn
            have s634n : 0 < (orient A B z) := lt_of_le_of_ne (le_of_not_gt hn) n7.symm
            have p635 : (orient A B R) * (orient A a z) < 0 := mul_neg_of_pos_of_neg h2 s560n
            have p636 : (orient A R a) * (orient A B z) < 0 := mul_neg_of_neg_of_pos h14 s634n
            have p637 : 0 < (orient A R z) * (orient A B a) := mul_pos_of_neg_of_neg h18 s225n
            linarith only [eq12, p635, p636, p637]
          have s638 : (orient A B c) < 0 := by
            by_contra hn
            have s638n : 0 < (orient A B c) := lt_of_le_of_ne (le_of_not_gt hn) n5.symm
            have p639 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
            have p640 : 0 < (orient A B c) * (orient B K z) := mul_pos s638n h34
            have p641 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s634 h32
            linarith only [eq20, p639, p640, p641]
          have s642 : 0 < (orient B a c) := by
            by_contra hn
            have s642n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
            have p643 : 0 < (orient A B a) * (orient B c z) := mul_pos_of_neg_of_neg s225n h48
            have p644 : (orient A B c) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s638 h43
            have p645 : 0 < (orient A B z) * (orient B a c) := mul_pos_of_neg_of_neg s634 s642n
            linarith only [eq21, p643, p644, p645]
          have s646 : (orient A c z) < 0 := by
            by_contra hn
            have s646n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
            have p647 : 0 < (orient A B c) * (orient a c z) := mul_pos_of_neg_of_neg s638 h79
            have p648 : (orient A a c) * (orient B c z) < 0 := mul_neg_of_pos_of_neg s559 h48
            have p649 : 0 < (orient A c z) * (orient B a c) := mul_pos s646n s642
            linarith only [eq32, p647, p648, p649]
          have s650 : (orient A K c) < 0 := by
            by_contra hn
            have s650n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
            have p651 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s638
            have p652 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s650n
            have p653 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
            linarith only [eq7, p651, p652, p653]
          have s654 : (orient A K z) < 0 := by
            by_contra hn
            have s654n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
            have p655 : (orient A K R) * (orient A B z) < 0 := mul_neg_of_pos_of_neg h8 s634
            have p656 : 0 < (orient A B R) * (orient A K z) := mul_pos h2 s654n
            have p657 : (orient A R z) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h18 h1
            linarith only [eq8, p655, p656, p657]
          have p658 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s650 h48
          have p659 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s638 h63
          have p660 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s646 h32
          linarith only [eq30, p658, p659, p660]
      · have s559n : (orient A a c) < 0 := lt_of_le_of_ne (le_of_not_gt s559) n20
        have s661 : (orient A K c) < 0 := by
          by_contra hn
          have s661n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
          have p662 : (orient A K R) * (orient A a c) < 0 := mul_neg_of_pos_of_neg h8 s559n
          have p663 : (orient A R a) * (orient A K c) < 0 := mul_neg_of_neg_of_pos h14 s661n
          have p664 : 0 < (orient A R c) * (orient A K a) := mul_pos_of_neg_of_neg h16 s0n
          linarith only [eq10, p662, p663, p664]
        by_cases s665 : 0 < (orient A a z)
        ·
          have s666 : (orient B a c) < 0 := by
            by_contra hn
            have s666n : 0 < (orient B a c) := lt_of_le_of_ne (le_of_not_gt hn) n41.symm
            have p667 : 0 < (orient A B a) * (orient a c z) := mul_pos_of_neg_of_neg s225n h79
            have p668 : (orient A a c) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s559n h43
            have p669 : 0 < (orient A a z) * (orient B a c) := mul_pos s665 s666n
            linarith only [eq29, p667, p668, p669]
          by_cases s670 : 0 < (orient B a o)
          ·
            have s671 : (orient A B o) < 0 := by
              by_contra hn
              have s671n : 0 < (orient A B o) := lt_of_le_of_ne (le_of_not_gt hn) n6.symm
              linarith only [eq2, s225n, s671n, s670, h21]
            have s672 : 0 < (orient B R o) := by
              by_contra hn
              have s672n : (orient B R o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n38
              have p673 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
              have p674 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s672n
              have p675 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s671 h29
              linarith only [eq19, p673, p674, p675]
            have s676 : (orient A B z) < 0 := by
              by_contra hn
              have s676n : 0 < (orient A B z) := lt_of_le_of_ne (le_of_not_gt hn) n7.symm
              have p677 : 0 < (orient A B a) * (orient B o z) := mul_pos_of_neg_of_neg s225n h49
              have p678 : 0 < (orient A B z) * (orient B a o) := mul_pos s676n s670
              have p679 : (orient A B o) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s671 h43
              linarith only [eq22, p677, p678, p679]
            have s680 : (orient A K z) < 0 := by
              by_contra hn
              have s680n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
              have p681 : (orient A K R) * (orient A B z) < 0 := mul_neg_of_pos_of_neg h8 s676
              have p682 : 0 < (orient A B R) * (orient A K z) := mul_pos h2 s680n
              have p683 : (orient A R z) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h18 h1
              linarith only [eq8, p681, p682, p683]
            have s684 : (orient A B c) < 0 := by
              by_contra hn
              have s684n : 0 < (orient A B c) := lt_of_le_of_ne (le_of_not_gt hn) n5.symm
              have p685 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
              have p686 : 0 < (orient A B c) * (orient B K z) := mul_pos s684n h34
              have p687 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s676 h32
              linarith only [eq20, p685, p686, p687]
            have p688 : 0 < (orient A B a) * (orient B c z) := mul_pos_of_neg_of_neg s225n h48
            have p689 : (orient A B c) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s684 h43
            have p690 : 0 < (orient A B z) * (orient B a c) := mul_pos_of_neg_of_neg s676 s666
            linarith only [eq21, p688, p689, p690]
          · have s670n : (orient B a o) < 0 := lt_of_le_of_ne (le_of_not_gt s670) n42
            have s691 : (orient B R a) < 0 := by
              by_contra hn
              have s691n : 0 < (orient B R a) := lt_of_le_of_ne (le_of_not_gt hn) n35.symm
              have p692 : 0 < (orient A R a) * (orient B a o) := mul_pos_of_neg_of_neg h14 s670n
              have p693 : (orient A B a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s225n h67
              have p694 : (orient A a o) * (orient B R a) < 0 := mul_neg_of_neg_of_pos h21 s691n
              linarith only [eq26, p692, p693, p694]
            have s695 : (orient K a o) < 0 := by
              by_contra hn
              have s695n : 0 < (orient K a o) := lt_of_le_of_ne (le_of_not_gt hn) n57.symm
              have p696 : 0 < (orient A K a) * (orient B a o) := mul_pos_of_neg_of_neg s0n s670n
              have p697 : (orient A B a) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s225n s695n
              have p698 : (orient A a o) * (orient B K a) < 0 := mul_neg_of_neg_of_pos h21 h30
              linarith only [eq27, p696, p697, p698]
            have s699 : 0 < (orient K R a) := by
              by_contra hn
              have s699n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
              linarith only [eq3, s699n, s221, s695, h67]
            have s700 : (orient B R o) < 0 := by
              by_contra hn
              have s700n : 0 < (orient B R o) := lt_of_le_of_ne (le_of_not_gt hn) n38.symm
              linarith only [eq5, s691, s700n, s670n, h67]
            have s701 : 0 < (orient A B o) := by
              by_contra hn
              have s701n : (orient A B o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n6
              have p702 : 0 < (orient A B R) * (orient B K o) := mul_pos h2 h33
              have p703 : (orient A B K) * (orient B R o) < 0 := mul_neg_of_pos_of_neg h1 s700
              have p704 : (orient A B o) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s701n h29
              linarith only [eq19, p702, p703, p704]
            have p705 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s695
            have p706 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
            have p707 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s699
            linarith only [eq24, p705, p706, p707]
        · have s665n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s665) n22
          have s708 : (orient A B z) < 0 := by
            by_contra hn
            have s708n : 0 < (orient A B z) := lt_of_le_of_ne (le_of_not_gt hn) n7.symm
            have p709 : (orient A B R) * (orient A a z) < 0 := mul_neg_of_pos_of_neg h2 s665n
            have p710 : (orient A R a) * (orient A B z) < 0 := mul_neg_of_neg_of_pos h14 s708n
            have p711 : 0 < (orient A R z) * (orient A B a) := mul_pos_of_neg_of_neg h18 s225n
            linarith only [eq12, p709, p710, p711]
          have s712 : (orient A B c) < 0 := by
            by_contra hn
            have s712n : 0 < (orient A B c) := lt_of_le_of_ne (le_of_not_gt hn) n5.symm
            have p713 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
            have p714 : 0 < (orient A B c) * (orient B K z) := mul_pos s712n h34
            have p715 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s708 h32
            linarith only [eq20, p713, p714, p715]
          have s716 : 0 < (orient B a c) := by
            by_contra hn
            have s716n : (orient B a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n41
            have p717 : 0 < (orient A B a) * (orient B c z) := mul_pos_of_neg_of_neg s225n h48
            have p718 : (orient A B c) * (orient B a z) < 0 := mul_neg_of_neg_of_pos s712 h43
            have p719 : 0 < (orient A B z) * (orient B a c) := mul_pos_of_neg_of_neg s708 s716n
            linarith only [eq21, p717, p718, p719]
          have s720 : 0 < (orient A c z) := by
            by_contra hn
            have s720n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
            have p721 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s661 h48
            have p722 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s712 h63
            have p723 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s720n h32
            linarith only [eq30, p721, p722, p723]
          have s724 : (orient K a c) < 0 := by
            by_contra hn
            have s724n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
            have p725 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s661 h79
            have p726 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s559n h63
            have p727 : 0 < (orient A c z) * (orient K a c) := mul_pos s720 s724n
            linarith only [eq31, p725, p726, p727]
          have s728 : (orient A K z) < 0 := by
            by_contra hn
            have s728n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
            have p729 : (orient A K R) * (orient A B z) < 0 := mul_neg_of_pos_of_neg h8 s708
            have p730 : 0 < (orient A B R) * (orient A K z) := mul_pos h2 s728n
            have p731 : (orient A R z) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h18 h1
            linarith only [eq8, p729, p730, p731]
          have s732 : (orient K a z) < 0 := by
            by_contra hn
            have s732n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
            have p733 : 0 < (orient A K a) * (orient a c z) := mul_pos_of_neg_of_neg s0n h79
            have p734 : (orient A a c) * (orient K a z) < 0 := mul_neg_of_neg_of_pos s559n s732n
            have p735 : 0 < (orient A a z) * (orient K a c) := mul_pos_of_neg_of_neg s665n s724
            linarith only [eq28, p733, p734, p735]
          have s736 : (orient K a o) < 0 := by
            by_contra hn
            have s736n : 0 < (orient K a o) := lt_of_le_of_ne (le_of_not_gt hn) n57.symm
            have p737 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0n h64
            have p738 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s728 s736n
            have p739 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s217 s732
            linarith only [eq18, p737, p738, p739]
          have s740 : (orient K R a) < 0 := by
            by_contra hn
            have s740n : 0 < (orient K R a) := lt_of_le_of_ne (le_of_not_gt hn) n50.symm
            have p741 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s736
            have p742 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0n h67
            have p743 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s740n
            linarith only [eq24, p741, p742, p743]
          linarith only [eq3, s740, s221, s736, h67]
end JSP198.Nicolas
#print axioms JSP198.Nicolas.ia_nine_point_bfirst_certificate
#print axioms JSP198.Nicolas.ia_nine_point_bchord_certificate
