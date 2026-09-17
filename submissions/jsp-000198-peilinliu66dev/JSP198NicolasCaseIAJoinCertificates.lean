/- Released under the MIT license. Explicit ring and sign proofs; no SAT premise. -/
import JSP198NicolasCaseIASupport
noncomputable section
open Classical Horton
namespace JSP198.Nicolas
theorem ia_nine_point_entryB_certificate (A R K B a b c z o : Point)
    (h8 : 0 < (orient A K R))
    (h2 : 0 < (orient A B R))
    (h1 : 0 < (orient A B K))
    (h29 : 0 < (orient B K R))
    (h77 : (orient a b z) < 0)
    (h79 : (orient a c z) < 0)
    (h14 : (orient A R a) < 0)
    (h15 : (orient A R b) < 0)
    (h16 : (orient A R c) < 0)
    (h18 : (orient A R z) < 0)
    (h17 : (orient A R o) < 0)
    (h31 : 0 < (orient B K b))
    (h32 : 0 < (orient B K c))
    (h34 : 0 < (orient B K z))
    (h67 : 0 < (orient R a o))
    (h70 : (orient R b o) < 0)
    (h65 : 0 < (orient R a b))
    (h64 : 0 < (orient K o z))
    (h63 : 0 < (orient K c z))
    (h21 : (orient A a o) < 0)
    (h19 : (orient A a b) < 0)
    (h48 : (orient B c z) < 0)
    (h3 : (orient A B a) < 0)
    (n5 : (orient A B c) ≠ 0)
    (n7 : (orient A B z) ≠ 0)
    (n9 : (orient A K a) ≠ 0)
    (n10 : (orient A K b) ≠ 0)
    (n11 : (orient A K c) ≠ 0)
    (n12 : (orient A K o) ≠ 0)
    (n13 : (orient A K z) ≠ 0)
    (n20 : (orient A a c) ≠ 0)
    (n22 : (orient A a z) ≠ 0)
    (n27 : (orient A c z) ≠ 0)
    (n50 : (orient K R a) ≠ 0)
    (n51 : (orient K R b) ≠ 0)
    (n53 : (orient K R o) ≠ 0)
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
  have eq2 : -((orient A K R) * (orient A B a)) + ((orient A B R) * (orient A K a)) + -((orient A R a) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq3 : -((orient A K R) * (orient A B c)) + ((orient A B R) * (orient A K c)) + -((orient A R c) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq4 : -((orient A K R) * (orient A a b)) + -((orient A R a) * (orient A K b)) + ((orient A R b) * (orient A K a)) = 0 := by
    unfold orient
    ring
  have eq5 : -((orient A B R) * (orient A a z)) + -((orient A R a) * (orient A B z)) + ((orient A R z) * (orient A B a)) = 0 := by
    unfold orient
    ring
  have eq6 : ((orient A K R) * (orient R a b)) + -((orient A R a) * (orient K R b)) + ((orient A R b) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq7 : ((orient A K R) * (orient R a z)) + -((orient A R a) * (orient K R z)) + ((orient A R z) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq8 : ((orient A K R) * (orient R b o)) + -((orient A R b) * (orient K R o)) + ((orient A R o) * (orient K R b)) = 0 := by
    unfold orient
    ring
  have eq9 : ((orient A K R) * (orient B K b)) + -((orient A B K) * (orient K R b)) + -((orient A K b) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq10 : ((orient A K R) * (orient K o z)) + ((orient A K z) * (orient K R o)) + -((orient A K o) * (orient K R z)) = 0 := by
    unfold orient
    ring
  have eq11 : ((orient A K a) * (orient K o z)) + ((orient A K z) * (orient K a o)) + -((orient A K o) * (orient K a z)) = 0 := by
    unfold orient
    ring
  have eq12 : -((orient A B K) * (orient B c z)) + ((orient A B c) * (orient B K z)) + -((orient A B z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq13 : -((orient A R a) * (orient K a z)) + ((orient A K a) * (orient R a z)) + ((orient A a z) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq14 : -((orient A R a) * (orient K a o)) + ((orient A K a) * (orient R a o)) + ((orient A a o) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq15 : ((orient A R a) * (orient a b z)) + -((orient A a b) * (orient R a z)) + ((orient A a z) * (orient R a b)) = 0 := by
    unfold orient
    ring
  have eq16 : ((orient A K a) * (orient a c z)) + -((orient A a c) * (orient K a z)) + ((orient A a z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have eq17 : -((orient A K c) * (orient B c z)) + ((orient A B c) * (orient K c z)) + ((orient A c z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq18 : -((orient A K c) * (orient a c z)) + ((orient A a c) * (orient K c z)) + -((orient A c z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have s0 : (orient A K a) < 0 := by
    by_contra hn
    have s0n : 0 < (orient A K a) := lt_of_le_of_ne (le_of_not_gt hn) n9.symm
    have p1 : (orient A K R) * (orient A B a) < 0 := mul_neg_of_pos_of_neg h8 h3
    have p2 : 0 < (orient A B R) * (orient A K a) := mul_pos h2 s0n
    have p3 : (orient A R a) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h14 h1
    linarith only [eq2, p1, p2, p3]
  have s4 : (orient A K b) < 0 := by
    by_contra hn
    have s4n : 0 < (orient A K b) := lt_of_le_of_ne (le_of_not_gt hn) n10.symm
    have p5 : (orient A K R) * (orient A a b) < 0 := mul_neg_of_pos_of_neg h8 h19
    have p6 : (orient A R a) * (orient A K b) < 0 := mul_neg_of_neg_of_pos h14 s4n
    have p7 : 0 < (orient A R b) * (orient A K a) := mul_pos_of_neg_of_neg h15 s0
    linarith only [eq4, p5, p6, p7]
  have s8 : 0 < (orient K R b) := by
    by_contra hn
    have s8n : (orient K R b) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n51
    have p9 : 0 < (orient A K R) * (orient B K b) := mul_pos h8 h31
    have p10 : (orient A B K) * (orient K R b) < 0 := mul_neg_of_pos_of_neg h1 s8n
    have p11 : (orient A K b) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s4 h29
    linarith only [eq9, p9, p10, p11]
  have s12 : 0 < (orient K R a) := by
    by_contra hn
    have s12n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
    have p13 : 0 < (orient A K R) * (orient R a b) := mul_pos h8 h65
    have p14 : (orient A R a) * (orient K R b) < 0 := mul_neg_of_neg_of_pos h14 s8
    have p15 : 0 < (orient A R b) * (orient K R a) := mul_pos_of_neg_of_neg h15 s12n
    linarith only [eq6, p13, p14, p15]
  have s16 : 0 < (orient K R o) := by
    by_contra hn
    have s16n : (orient K R o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n53
    have p17 : (orient A K R) * (orient R b o) < 0 := mul_neg_of_pos_of_neg h8 h70
    have p18 : 0 < (orient A R b) * (orient K R o) := mul_pos_of_neg_of_neg h15 s16n
    have p19 : (orient A R o) * (orient K R b) < 0 := mul_neg_of_neg_of_pos h17 s8
    linarith only [eq8, p17, p18, p19]
  have s20 : 0 < (orient K a o) := by
    by_contra hn
    have s20n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
    have p21 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s20n
    have p22 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s0 h67
    have p23 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s12
    linarith only [eq14, p21, p22, p23]
  have s24 : (orient A K o) < 0 := by
    by_contra hn
    have s24n : 0 < (orient A K o) := lt_of_le_of_ne (le_of_not_gt hn) n12.symm
    linarith only [eq0, s0, s24n, s20, h21]
  by_cases s25 : 0 < (orient A a c)
  ·
    by_cases s26 : 0 < (orient A a z)
    ·
      have s27 : (orient R a z) < 0 := by
        by_contra hn
        have s27n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
        have p28 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
        have p29 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s27n
        have p30 : 0 < (orient A a z) * (orient R a b) := mul_pos s26 h65
        linarith only [eq15, p28, p29, p30]
      have s31 : 0 < (orient K R z) := by
        by_contra hn
        have s31n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
        have p32 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s27
        have p33 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s31n
        have p34 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s12
        linarith only [eq7, p32, p33, p34]
      have s35 : (orient A K z) < 0 := by
        by_contra hn
        have s35n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
        have p36 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
        have p37 : 0 < (orient A K z) * (orient K R o) := mul_pos s35n s16
        have p38 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s24 s31
        linarith only [eq10, p36, p37, p38]
      have s39 : 0 < (orient K a z) := by
        by_contra hn
        have s39n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
        have p40 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0 h64
        have p41 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s35 s20
        have p42 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s24 s39n
        linarith only [eq11, p40, p41, p42]
      have p43 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s39
      have p44 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0 s27
      have p45 : 0 < (orient A a z) * (orient K R a) := mul_pos s26 s12
      linarith only [eq13, p43, p44, p45]
    · have s26n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s26) n22
      have s46 : (orient A c z) < 0 := by
        by_contra hn
        have s46n : 0 < (orient A c z) := lt_of_le_of_ne (le_of_not_gt hn) n27.symm
        linarith only [eq1, s25, s26n, h79, s46n]
      have s47 : (orient A B z) < 0 := by
        by_contra hn
        have s47n : 0 < (orient A B z) := lt_of_le_of_ne (le_of_not_gt hn) n7.symm
        have p48 : (orient A B R) * (orient A a z) < 0 := mul_neg_of_pos_of_neg h2 s26n
        have p49 : (orient A R a) * (orient A B z) < 0 := mul_neg_of_neg_of_pos h14 s47n
        have p50 : 0 < (orient A R z) * (orient A B a) := mul_pos_of_neg_of_neg h18 h3
        linarith only [eq5, p48, p49, p50]
      have s51 : (orient A B c) < 0 := by
        by_contra hn
        have s51n : 0 < (orient A B c) := lt_of_le_of_ne (le_of_not_gt hn) n5.symm
        have p52 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
        have p53 : 0 < (orient A B c) * (orient B K z) := mul_pos s51n h34
        have p54 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s47 h32
        linarith only [eq12, p52, p53, p54]
      have s55 : 0 < (orient A K c) := by
        by_contra hn
        have s55n : (orient A K c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n11
        have p56 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s55n h48
        have p57 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s51 h63
        have p58 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s46 h32
        linarith only [eq17, p56, p57, p58]
      have s59 : (orient K a c) < 0 := by
        by_contra hn
        have s59n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
        have p60 : (orient A K c) * (orient a c z) < 0 := mul_neg_of_pos_of_neg s55 h79
        have p61 : 0 < (orient A a c) * (orient K c z) := mul_pos s25 h63
        have p62 : (orient A c z) * (orient K a c) < 0 := mul_neg_of_neg_of_pos s46 s59n
        linarith only [eq18, p60, p61, p62]
      have p63 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s51
      have p64 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s55
      have p65 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
      linarith only [eq3, p63, p64, p65]
  · have s25n : (orient A a c) < 0 := lt_of_le_of_ne (le_of_not_gt s25) n20
    by_cases s66 : 0 < (orient A a z)
    ·
      have s67 : (orient R a z) < 0 := by
        by_contra hn
        have s67n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
        have p68 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
        have p69 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s67n
        have p70 : 0 < (orient A a z) * (orient R a b) := mul_pos s66 h65
        linarith only [eq15, p68, p69, p70]
      have s71 : 0 < (orient K R z) := by
        by_contra hn
        have s71n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
        have p72 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s67
        have p73 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s71n
        have p74 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s12
        linarith only [eq7, p72, p73, p74]
      have s75 : (orient A K z) < 0 := by
        by_contra hn
        have s75n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
        have p76 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
        have p77 : 0 < (orient A K z) * (orient K R o) := mul_pos s75n s16
        have p78 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s24 s71
        linarith only [eq10, p76, p77, p78]
      have s79 : 0 < (orient K a z) := by
        by_contra hn
        have s79n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
        have p80 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0 h64
        have p81 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s75 s20
        have p82 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s24 s79n
        linarith only [eq11, p80, p81, p82]
      have p83 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s79
      have p84 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s0 s67
      have p85 : 0 < (orient A a z) * (orient K R a) := mul_pos s66 s12
      linarith only [eq13, p83, p84, p85]
    · have s66n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s66) n22
      have s86 : (orient A B z) < 0 := by
        by_contra hn
        have s86n : 0 < (orient A B z) := lt_of_le_of_ne (le_of_not_gt hn) n7.symm
        have p87 : (orient A B R) * (orient A a z) < 0 := mul_neg_of_pos_of_neg h2 s66n
        have p88 : (orient A R a) * (orient A B z) < 0 := mul_neg_of_neg_of_pos h14 s86n
        have p89 : 0 < (orient A R z) * (orient A B a) := mul_pos_of_neg_of_neg h18 h3
        linarith only [eq5, p87, p88, p89]
      have s90 : (orient A B c) < 0 := by
        by_contra hn
        have s90n : 0 < (orient A B c) := lt_of_le_of_ne (le_of_not_gt hn) n5.symm
        have p91 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
        have p92 : 0 < (orient A B c) * (orient B K z) := mul_pos s90n h34
        have p93 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s86 h32
        linarith only [eq12, p91, p92, p93]
      have s94 : (orient A K c) < 0 := by
        by_contra hn
        have s94n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
        have p95 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s90
        have p96 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s94n
        have p97 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
        linarith only [eq3, p95, p96, p97]
      have s98 : 0 < (orient A c z) := by
        by_contra hn
        have s98n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
        have p99 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s94 h48
        have p100 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s90 h63
        have p101 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s98n h32
        linarith only [eq17, p99, p100, p101]
      have s102 : (orient K a c) < 0 := by
        by_contra hn
        have s102n : 0 < (orient K a c) := lt_of_le_of_ne (le_of_not_gt hn) n56.symm
        have p103 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s94 h79
        have p104 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s25n h63
        have p105 : 0 < (orient A c z) * (orient K a c) := mul_pos s98 s102n
        linarith only [eq18, p103, p104, p105]
      have s106 : (orient K a z) < 0 := by
        by_contra hn
        have s106n : 0 < (orient K a z) := lt_of_le_of_ne (le_of_not_gt hn) n58.symm
        have p107 : 0 < (orient A K a) * (orient a c z) := mul_pos_of_neg_of_neg s0 h79
        have p108 : (orient A a c) * (orient K a z) < 0 := mul_neg_of_neg_of_pos s25n s106n
        have p109 : 0 < (orient A a z) * (orient K a c) := mul_pos_of_neg_of_neg s66n s102
        linarith only [eq16, p107, p108, p109]
      have s110 : 0 < (orient A K z) := by
        by_contra hn
        have s110n : (orient A K z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n13
        have p111 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s0 h64
        have p112 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s110n s20
        have p113 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s24 s106
        linarith only [eq11, p111, p112, p113]
      have s114 : (orient R a z) < 0 := by
        by_contra hn
        have s114n : 0 < (orient R a z) := lt_of_le_of_ne (le_of_not_gt hn) n68.symm
        have p115 : 0 < (orient A R a) * (orient K a z) := mul_pos_of_neg_of_neg h14 s106
        have p116 : (orient A K a) * (orient R a z) < 0 := mul_neg_of_neg_of_pos s0 s114n
        have p117 : (orient A a z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos s66n s12
        linarith only [eq13, p115, p116, p117]
      have s118 : 0 < (orient K R z) := by
        by_contra hn
        have s118n : (orient K R z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n54
        have p119 : (orient A K R) * (orient R a z) < 0 := mul_neg_of_pos_of_neg h8 s114
        have p120 : 0 < (orient A R a) * (orient K R z) := mul_pos_of_neg_of_neg h14 s118n
        have p121 : (orient A R z) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h18 s12
        linarith only [eq7, p119, p120, p121]
      have p122 : 0 < (orient A K R) * (orient K o z) := mul_pos h8 h64
      have p123 : 0 < (orient A K z) * (orient K R o) := mul_pos s110 s16
      have p124 : (orient A K o) * (orient K R z) < 0 := mul_neg_of_neg_of_pos s24 s118
      linarith only [eq10, p122, p123, p124]
theorem ia_nine_point_exitA_certificate (A R K B a b c z o : Point)
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
    (h34 : 0 < (orient B K z))
    (h67 : 0 < (orient R a o))
    (h65 : 0 < (orient R a b))
    (h64 : 0 < (orient K o z))
    (h63 : 0 < (orient K c z))
    (h21 : (orient A a o) < 0)
    (h19 : (orient A a b) < 0)
    (h48 : (orient B c z) < 0)
    (h7 : (orient A B z) < 0)
    (n5 : (orient A B c) ≠ 0)
    (n9 : (orient A K a) ≠ 0)
    (n11 : (orient A K c) ≠ 0)
    (n12 : (orient A K o) ≠ 0)
    (n13 : (orient A K z) ≠ 0)
    (n20 : (orient A a c) ≠ 0)
    (n22 : (orient A a z) ≠ 0)
    (n27 : (orient A c z) ≠ 0)
    (n50 : (orient K R a) ≠ 0)
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
  have eq3 : -((orient A K R) * (orient A B z)) + ((orient A B R) * (orient A K z)) + -((orient A R z) * (orient A B K)) = 0 := by
    unfold orient
    ring
  have eq4 : -((orient A K R) * (orient A a c)) + -((orient A R a) * (orient A K c)) + ((orient A R c) * (orient A K a)) = 0 := by
    unfold orient
    ring
  have eq5 : ((orient A K R) * (orient B K a)) + -((orient A B K) * (orient K R a)) + -((orient A K a) * (orient B K R)) = 0 := by
    unfold orient
    ring
  have eq6 : ((orient A B K) * (orient K a c)) + -((orient A K a) * (orient B K c)) + ((orient A K c) * (orient B K a)) = 0 := by
    unfold orient
    ring
  have eq7 : ((orient A K a) * (orient K o z)) + ((orient A K z) * (orient K a o)) + -((orient A K o) * (orient K a z)) = 0 := by
    unfold orient
    ring
  have eq8 : -((orient A B K) * (orient B c z)) + ((orient A B c) * (orient B K z)) + -((orient A B z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq9 : -((orient A R a) * (orient K a z)) + ((orient A K a) * (orient R a z)) + ((orient A a z) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq10 : -((orient A R a) * (orient K a o)) + ((orient A K a) * (orient R a o)) + ((orient A a o) * (orient K R a)) = 0 := by
    unfold orient
    ring
  have eq11 : ((orient A R a) * (orient a b z)) + -((orient A a b) * (orient R a z)) + ((orient A a z) * (orient R a b)) = 0 := by
    unfold orient
    ring
  have eq12 : ((orient A K a) * (orient a c z)) + -((orient A a c) * (orient K a z)) + ((orient A a z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have eq13 : -((orient A K c) * (orient B c z)) + ((orient A B c) * (orient K c z)) + ((orient A c z) * (orient B K c)) = 0 := by
    unfold orient
    ring
  have eq14 : -((orient A K c) * (orient a c z)) + ((orient A a c) * (orient K c z)) + -((orient A c z) * (orient K a c)) = 0 := by
    unfold orient
    ring
  have s0 : (orient A K z) < 0 := by
    by_contra hn
    have s0n : 0 < (orient A K z) := lt_of_le_of_ne (le_of_not_gt hn) n13.symm
    have p1 : (orient A K R) * (orient A B z) < 0 := mul_neg_of_pos_of_neg h8 h7
    have p2 : 0 < (orient A B R) * (orient A K z) := mul_pos h2 s0n
    have p3 : (orient A R z) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h18 h1
    linarith only [eq3, p1, p2, p3]
  have s4 : (orient A B c) < 0 := by
    by_contra hn
    have s4n : 0 < (orient A B c) := lt_of_le_of_ne (le_of_not_gt hn) n5.symm
    have p5 : (orient A B K) * (orient B c z) < 0 := mul_neg_of_pos_of_neg h1 h48
    have p6 : 0 < (orient A B c) * (orient B K z) := mul_pos s4n h34
    have p7 : (orient A B z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos h7 h32
    linarith only [eq8, p5, p6, p7]
  have s8 : (orient A K c) < 0 := by
    by_contra hn
    have s8n : 0 < (orient A K c) := lt_of_le_of_ne (le_of_not_gt hn) n11.symm
    have p9 : (orient A K R) * (orient A B c) < 0 := mul_neg_of_pos_of_neg h8 s4
    have p10 : 0 < (orient A B R) * (orient A K c) := mul_pos h2 s8n
    have p11 : (orient A R c) * (orient A B K) < 0 := mul_neg_of_neg_of_pos h16 h1
    linarith only [eq2, p9, p10, p11]
  have s12 : 0 < (orient A c z) := by
    by_contra hn
    have s12n : (orient A c z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n27
    have p13 : 0 < (orient A K c) * (orient B c z) := mul_pos_of_neg_of_neg s8 h48
    have p14 : (orient A B c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s4 h63
    have p15 : (orient A c z) * (orient B K c) < 0 := mul_neg_of_neg_of_pos s12n h32
    linarith only [eq13, p13, p14, p15]
  by_cases s16 : 0 < (orient A K a)
  ·
    have s17 : (orient A a c) < 0 := by
      by_contra hn
      have s17n : 0 < (orient A a c) := lt_of_le_of_ne (le_of_not_gt hn) n20.symm
      have p18 : 0 < (orient A K R) * (orient A a c) := mul_pos h8 s17n
      have p19 : 0 < (orient A R a) * (orient A K c) := mul_pos_of_neg_of_neg h14 s8
      have p20 : (orient A R c) * (orient A K a) < 0 := mul_neg_of_neg_of_pos h16 s16
      linarith only [eq4, p18, p19, p20]
    have s21 : 0 < (orient K a c) := by
      by_contra hn
      have s21n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
      have p22 : (orient A B K) * (orient K a c) < 0 := mul_neg_of_pos_of_neg h1 s21n
      have p23 : 0 < (orient A K a) * (orient B K c) := mul_pos s16 h32
      have p24 : (orient A K c) * (orient B K a) < 0 := mul_neg_of_neg_of_pos s8 h30
      linarith only [eq6, p22, p23, p24]
    have p25 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s8 h79
    have p26 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s17 h63
    have p27 : 0 < (orient A c z) * (orient K a c) := mul_pos s12 s21
    linarith only [eq14, p25, p26, p27]
  · have s16n : (orient A K a) < 0 := lt_of_le_of_ne (le_of_not_gt s16) n9
    have s28 : 0 < (orient K R a) := by
      by_contra hn
      have s28n : (orient K R a) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n50
      have p29 : 0 < (orient A K R) * (orient B K a) := mul_pos h8 h30
      have p30 : (orient A B K) * (orient K R a) < 0 := mul_neg_of_pos_of_neg h1 s28n
      have p31 : (orient A K a) * (orient B K R) < 0 := mul_neg_of_neg_of_pos s16n h29
      linarith only [eq5, p29, p30, p31]
    have s32 : 0 < (orient K a o) := by
      by_contra hn
      have s32n : (orient K a o) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n57
      have p33 : 0 < (orient A R a) * (orient K a o) := mul_pos_of_neg_of_neg h14 s32n
      have p34 : (orient A K a) * (orient R a o) < 0 := mul_neg_of_neg_of_pos s16n h67
      have p35 : (orient A a o) * (orient K R a) < 0 := mul_neg_of_neg_of_pos h21 s28
      linarith only [eq10, p33, p34, p35]
    have s36 : (orient A K o) < 0 := by
      by_contra hn
      have s36n : 0 < (orient A K o) := lt_of_le_of_ne (le_of_not_gt hn) n12.symm
      linarith only [eq0, s16n, s36n, s32, h21]
    have s37 : 0 < (orient K a z) := by
      by_contra hn
      have s37n : (orient K a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n58
      have p38 : (orient A K a) * (orient K o z) < 0 := mul_neg_of_neg_of_pos s16n h64
      have p39 : (orient A K z) * (orient K a o) < 0 := mul_neg_of_neg_of_pos s0 s32
      have p40 : 0 < (orient A K o) * (orient K a z) := mul_pos_of_neg_of_neg s36 s37n
      linarith only [eq7, p38, p39, p40]
    by_cases s41 : 0 < (orient A a z)
    ·
      have s42 : 0 < (orient R a z) := by
        by_contra hn
        have s42n : (orient R a z) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n68
        have p43 : (orient A R a) * (orient K a z) < 0 := mul_neg_of_neg_of_pos h14 s37
        have p44 : 0 < (orient A K a) * (orient R a z) := mul_pos_of_neg_of_neg s16n s42n
        have p45 : 0 < (orient A a z) * (orient K R a) := mul_pos s41 s28
        linarith only [eq9, p43, p44, p45]
      have p46 : 0 < (orient A R a) * (orient a b z) := mul_pos_of_neg_of_neg h14 h77
      have p47 : (orient A a b) * (orient R a z) < 0 := mul_neg_of_neg_of_pos h19 s42
      have p48 : 0 < (orient A a z) * (orient R a b) := mul_pos s41 h65
      linarith only [eq11, p46, p47, p48]
    · have s41n : (orient A a z) < 0 := lt_of_le_of_ne (le_of_not_gt s41) n22
      have s49 : (orient A a c) < 0 := by
        by_contra hn
        have s49n : 0 < (orient A a c) := lt_of_le_of_ne (le_of_not_gt hn) n20.symm
        linarith only [eq1, s49n, s41n, h79, s12]
      have s50 : 0 < (orient K a c) := by
        by_contra hn
        have s50n : (orient K a c) < 0 := lt_of_le_of_ne (le_of_not_gt hn) n56
        have p51 : 0 < (orient A K a) * (orient a c z) := mul_pos_of_neg_of_neg s16n h79
        have p52 : (orient A a c) * (orient K a z) < 0 := mul_neg_of_neg_of_pos s49 s37
        have p53 : 0 < (orient A a z) * (orient K a c) := mul_pos_of_neg_of_neg s41n s50n
        linarith only [eq12, p51, p52, p53]
      have p54 : 0 < (orient A K c) * (orient a c z) := mul_pos_of_neg_of_neg s8 h79
      have p55 : (orient A a c) * (orient K c z) < 0 := mul_neg_of_neg_of_pos s49 h63
      have p56 : 0 < (orient A c z) * (orient K a c) := mul_pos s12 s50
      linarith only [eq14, p54, p55, p56]
end JSP198.Nicolas
#print axioms JSP198.Nicolas.ia_nine_point_entryB_certificate
#print axioms JSP198.Nicolas.ia_nine_point_exitA_certificate
