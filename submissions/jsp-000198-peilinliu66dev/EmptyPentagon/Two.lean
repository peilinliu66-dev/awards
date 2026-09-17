/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Two.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Definitions
import EmptyPentagon.Certificate
import EmptyPentagon.Interp
import EmptyPentagon.TriangleInterior
import EmptyPentagon.Pentagon
import EmptyPentagon.Signs
import EmptyPentagon.Final
import EmptyPentagon.Third

noncomputable section
open Classical
namespace Horton

set_option linter.unusedVariables false

/-- Five points of `S` in convex position (all ten orientations positive for the cyclic order
`a, b, c, d, e`) such that every other point of `S` lies weakly beyond one of the five edge lines
give an empty convex pentagon of `S`. -/
theorem pent5_of_signs (S : Finset Point) (a b c d e : Point)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (he : e ∈ S)
    (n012 : 0 < orient a b c) (n013 : 0 < orient a b d) (n014 : 0 < orient a b e)
    (n023 : 0 < orient a c d) (n024 : 0 < orient a c e) (n034 : 0 < orient a d e)
    (n123 : 0 < orient b c d) (n124 : 0 < orient b c e) (n134 : 0 < orient b d e)
    (n234 : 0 < orient c d e)
    (hsep : ∀ q ∈ S, q ≠ a → q ≠ b → q ≠ c → q ≠ d → q ≠ e →
      orient a b q ≤ 0 ∨ orient b c q ≤ 0 ∨ orient c d q ≤ 0 ∨ orient d e q ≤ 0 ∨
        orient e a q ≤ 0) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  have nab : a ≠ b := by intro h; rw [h, orient_self_pair] at n012; exact lt_irrefl _ n012
  have nac : a ≠ c := by intro h; rw [h, orient_self_left] at n012; exact lt_irrefl _ n012
  have nad : a ≠ d := by intro h; rw [h, orient_self_left] at n013; exact lt_irrefl _ n013
  have nae : a ≠ e := by intro h; rw [h, orient_self_left] at n014; exact lt_irrefl _ n014
  have nbc : b ≠ c := by intro h; rw [h, orient_self_right] at n012; exact lt_irrefl _ n012
  have nbd : b ≠ d := by intro h; rw [h, orient_self_right] at n013; exact lt_irrefl _ n013
  have nbe : b ≠ e := by intro h; rw [h, orient_self_right] at n014; exact lt_irrefl _ n014
  have ncd : c ≠ d := by intro h; rw [h, orient_self_right] at n023; exact lt_irrefl _ n023
  have nce : c ≠ e := by intro h; rw [h, orient_self_right] at n024; exact lt_irrefl _ n024
  have nde : d ≠ e := by intro h; rw [h, orient_self_right] at n034; exact lt_irrefl _ n034
  have e10 : 0 < orient b c a := by linarith [orient_cyc a b c]
  have e20 : 0 < orient c d a := by linarith [orient_cyc a c d]
  have e21 : 0 < orient c d b := by linarith [orient_cyc b c d]
  have e30 : 0 < orient d e a := by linarith [orient_cyc a d e]
  have e31 : 0 < orient d e b := by linarith [orient_cyc b d e]
  have e32 : 0 < orient d e c := by linarith [orient_cyc c d e]
  have e41 : 0 < orient e a b := by linarith [orient_cyc a b e, orient_cyc b e a]
  have e42 : 0 < orient e a c := by linarith [orient_cyc a c e, orient_cyc c e a]
  have e43 : 0 < orient e a d := by linarith [orient_cyc a d e, orient_cyc d e a]
  set W : Fin 5 → Point := ![a, b, c, d, e] with hW
  have hWinj : Function.Injective W := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [hW, nab, nac, nad, nae, nbc, nbd, nbe, ncd, nce, nde, nab.symm, nac.symm, nad.symm,
        nae.symm, nbc.symm, nbd.symm, nbe.symm, ncd.symm, nce.symm, nde.symm] at hxy ⊢
  have hWS : ∀ k : Fin 5, W k ∈ S := by
    intro k; fin_cases k <;> simp [hW, ha, hb, hc, hd, he]
  have hWccw : ∀ k j : Fin 5, j ≠ k → j ≠ k + 1 → 0 < orient (W k) (W (k + 1)) (W j) := by
    intro k j hjk hjk1
    fin_cases k <;> fin_cases j <;> simp [hW] at hjk hjk1 ⊢ <;> assumption
  refine emptyPentagon_of_data S W hWinj hWS hWccw ?_
  intro q hqS hqW
  have hqa : q ≠ a := by have h := hqW 0; simpa [hW] using h
  have hqb : q ≠ b := by have h := hqW 1; simpa [hW] using h
  have hqc : q ≠ c := by have h := hqW 2; simpa [hW] using h
  have hqd : q ≠ d := by have h := hqW 3; simpa [hW] using h
  have hqe : q ≠ e := by have h := hqW 4; simpa [hW] using h
  rcases hsep q hqS hqa hqb hqc hqd hqe with h | h | h | h | h
  · exact ⟨a, b, nab, by intro k; fin_cases k <;>
      simp [hW, orient_self_left, orient_self_right, n012.le, n013.le, n014.le], h⟩
  · exact ⟨b, c, nbc, by intro k; fin_cases k <;>
      simp [hW, orient_self_left, orient_self_right, e10.le, n123.le, n124.le], h⟩
  · exact ⟨c, d, ncd, by intro k; fin_cases k <;>
      simp [hW, orient_self_left, orient_self_right, e20.le, e21.le, n234.le], h⟩
  · exact ⟨d, e, nde, by intro k; fin_cases k <;>
      simp [hW, orient_self_left, orient_self_right, e30.le, e31.le, e32.le], h⟩
  · exact ⟨e, a, nae.symm, by intro k; fin_cases k <;>
      simp [hW, orient_self_left, orient_self_right, e41.le, e42.le, e43.le], h⟩



/-- The five sign conditions of `InB` for the edge `u → v`, with `w` the vertex before `u` and
`x` the vertex after `v`. -/
def RegA (M u v w x Z : Point) : Prop :=
  0 < orient M u Z ∧ orient M v Z < 0 ∧ orient u v Z < 0 ∧ orient w u Z < 0 ∧ orient v x Z < 0

/-- The nine comparisons available for an outer point of the regions `B (i+3)`, `B (i+4)`. -/
def RDig (A D E M Q S3 Z : Point) : Prop :=
  orient D M Z < 0 ∧ orient D E Z < 0 ∧ 0 < orient A E Z ∧ 0 < orient A D Z ∧ 0 < orient A M Z ∧
    orient A Q Z < 0 ∧ orient A S3 Z < 0 ∧ orient M Q Z < 0 ∧ orient M S3 Z < 0

/-- The nine comparisons available for an outer point of the regions `B (i+1)`, `B (i+2)`. -/
def LDig (B C D M Q S3 Z : Point) : Prop :=
  orient B M Z < 0 ∧ orient B C Z < 0 ∧ orient C D Z < 0 ∧ orient B D Z < 0 ∧ 0 < orient B Q Z ∧
    0 < orient B S3 Z ∧ 0 < orient D M Z ∧ 0 < orient M Q Z ∧ 0 < orient M S3 Z

/-- An outer point lies in one of the four regions other than `B i`, together with its digest. -/
def RegAll (A B C D E M Q S3 Z : Point) : Prop :=
  (RegA M B C A D Z ∧ LDig B C D M Q S3 Z) ∨ (RegA M C D B E Z ∧ LDig B C D M Q S3 Z) ∨
    (RegA M D E C A Z ∧ RDig A D E M Q S3 Z) ∨ (RegA M E A D B Z ∧ RDig A D E M Q S3 Z)


set_option maxHeartbeats 2000000 in
/-- Each outer point of a region other than `B i` satisfies its nine-fact digest. -/
theorem regAll_of_reg (S : Finset Point) (hgp : GeneralPosition S)
    (A B C D E M Q S3 Z : Point)
    (mA : A ∈ S) (mB : B ∈ S) (mC : C ∈ S) (mD : D ∈ S) (mE : E ∈ S) (mM : M ∈ S) (mQ : Q ∈ S) (mS3 : S3 ∈ S) (mZ : Z ∈ S)
    (neAB : A ≠ B) (neAC : A ≠ C) (neAD : A ≠ D) (neAE : A ≠ E)
    (neAM : A ≠ M) (neAQ : A ≠ Q) (neAS3 : A ≠ S3) (neAZ : A ≠ Z)
    (neBC : B ≠ C) (neBD : B ≠ D) (neBE : B ≠ E) (neBM : B ≠ M)
    (neBQ : B ≠ Q) (neBS3 : B ≠ S3) (neBZ : B ≠ Z) (neCD : C ≠ D)
    (neCE : C ≠ E) (neCM : C ≠ M) (neCQ : C ≠ Q) (neCS3 : C ≠ S3)
    (neCZ : C ≠ Z) (neDE : D ≠ E) (neDM : D ≠ M) (neDQ : D ≠ Q)
    (neDS3 : D ≠ S3) (neDZ : D ≠ Z) (neEM : E ≠ M) (neEQ : E ≠ Q)
    (neES3 : E ≠ S3) (neEZ : E ≠ Z) (neMQ : M ≠ Q) (neMS3 : M ≠ S3)
    (neMZ : M ≠ Z) (neQS3 : Q ≠ S3) (neQZ : Q ≠ Z) (neS3Z : S3 ≠ Z)
    (bABC : 0 < orient A B C) (bABD : 0 < orient A B D) (bABE : 0 < orient A B E)
    (bACD : 0 < orient A C D) (bACE : 0 < orient A C E) (bADE : 0 < orient A D E)
    (bBCD : 0 < orient B C D) (bBCE : 0 < orient B C E) (bBDE : 0 < orient B D E)
    (bCDE : 0 < orient C D E) (bABM : 0 < orient A B M) (bBCM : 0 < orient B C M)
    (bCDM : 0 < orient C D M) (bDEM : 0 < orient D E M) (bAEM : orient A E M < 0)
    (bACM : 0 < orient A C M) (bBDM : 0 < orient B D M) (bCEM : 0 < orient C E M)
    (bADM : orient A D M < 0) (bBEM : orient B E M < 0) (bAMQ : orient A M Q < 0)
    (bBMQ : 0 < orient B M Q) (bABQ : orient A B Q < 0) (bAEQ : 0 < orient A E Q)
    (bBCQ : orient B C Q < 0) (bAMS : orient A M S3 < 0) (bBMS : 0 < orient B M S3)
    (bABS : orient A B S3 < 0) (bAES : 0 < orient A E S3) (bBCS : orient B C S3 < 0)
    (bAQS : orient A Q S3 < 0) (bBQS : 0 < orient B Q S3) (bACQ : orient A C Q < 0)
    (bACS : orient A C S3 < 0) (bBEQ : 0 < orient B E Q) (bBES : 0 < orient B E S3)
    (bCEQ : 0 < orient C E Q) (bCES : 0 < orient C E S3) (bCMQ : 0 < orient C M Q)
    (bCMS : 0 < orient C M S3) (bCQS : 0 < orient C Q S3) (bEMQ : orient E M Q < 0)
    (bEMS : orient E M S3 < 0) (bEQS : orient E Q S3 < 0)
    (hreg : RegA M B C A D Z ∨ RegA M C D B E Z ∨ RegA M D E C A Z ∨
      RegA M E A D B Z) :
    RegAll A B C D E M Q S3 Z := by
  rcases hreg with hr | hr | hr | hr
  · obtain ⟨g1, g2, g3, g4, g5⟩ := id hr
    have gc1 : orient B M Z < 0 := by
      have e : orient B M Z = -orient M B Z := by unfold orient; ring
      linarith [g1]
    have gc2 : 0 < orient C M Z := by
      have e : orient C M Z = -orient M C Z := by unfold orient; ring
      linarith [g2]
    set pp1 : Fin 5 → Point := ![A, B, C, D, Z] with hpp1
    have gg1 : IndexedGP pp1 := by
      have h := indexedGP_vec5 S hgp A B C D Z mA mB mC mD mZ neAB neAC neAD neAZ neBC neBD neBZ neCD neCZ neDZ
      simpa [hpp1] using h
    have e1ACX : orient A C Z < 0 := by
      have h := sign_imp_neg [(0, 2, 3, true), (1, 2, 3, true), (1, 2, 4, false), (0, 1, 4, false), (2, 3, 4, false)] 0 2 4 (by decide +kernel) pp1 gg1
        (litHolds_cons (litHolds_pos pp1 0 2 3 (by simpa [hpp1] using bACD)) (litHolds_cons (litHolds_pos pp1 1 2 3 (by simpa [hpp1] using bBCD)) (litHolds_cons (litHolds_neg pp1 1 2 4 (by simpa [hpp1] using g3)) (litHolds_cons (litHolds_neg pp1 0 1 4 (by simpa [hpp1] using g4)) (litHolds_cons (litHolds_neg pp1 2 3 4 (by simpa [hpp1] using g5)) (litHolds_nil pp1))))))
      simpa [hpp1] using h
    have e1ADX : orient A D Z < 0 := by
      have h := sign_imp_neg [(0, 2, 3, true), (2, 3, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp1 gg1
        (litHolds_cons (litHolds_pos pp1 0 2 3 (by simpa [hpp1] using bACD)) (litHolds_cons (litHolds_neg pp1 2 3 4 (by simpa [hpp1] using g5)) (litHolds_cons (litHolds_neg pp1 0 2 4 (by simpa [hpp1] using e1ACX)) (litHolds_nil pp1))))
      simpa [hpp1] using h
    set pp2 : Fin 5 → Point := ![A, B, C, M, Z] with hpp2
    have gg2 : IndexedGP pp2 := by
      have h := indexedGP_vec5 S hgp A B C M Z mA mB mC mM mZ neAB neAC neAM neAZ neBC neBM neBZ neCM neCZ neMZ
      simpa [hpp2] using h
    have e1AMX : orient A M Z < 0 := by
      have h := sign_imp_neg [(1, 3, 4, false), (2, 3, 4, true), (1, 2, 4, false), (0, 1, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp2 gg2
        (litHolds_cons (litHolds_neg pp2 1 3 4 (by simpa [hpp2] using gc1)) (litHolds_cons (litHolds_pos pp2 2 3 4 (by simpa [hpp2] using gc2)) (litHolds_cons (litHolds_neg pp2 1 2 4 (by simpa [hpp2] using g3)) (litHolds_cons (litHolds_neg pp2 0 1 4 (by simpa [hpp2] using g4)) (litHolds_cons (litHolds_neg pp2 0 2 4 (by simpa [hpp2] using e1ACX)) (litHolds_nil pp2))))))
      simpa [hpp2] using h
    have e1BDX : orient B D Z < 0 := by
      have h := sign_imp_neg [(1, 2, 4, false), (0, 1, 4, false), (2, 3, 4, false), (0, 2, 4, false), (0, 3, 4, false)] 1 3 4 (by decide +kernel) pp1 gg1
        (litHolds_cons (litHolds_neg pp1 1 2 4 (by simpa [hpp1] using g3)) (litHolds_cons (litHolds_neg pp1 0 1 4 (by simpa [hpp1] using g4)) (litHolds_cons (litHolds_neg pp1 2 3 4 (by simpa [hpp1] using g5)) (litHolds_cons (litHolds_neg pp1 0 2 4 (by simpa [hpp1] using e1ACX)) (litHolds_cons (litHolds_neg pp1 0 3 4 (by simpa [hpp1] using e1ADX)) (litHolds_nil pp1))))))
      simpa [hpp1] using h
    set pp3 : Fin 5 → Point := ![A, B, M, Q, Z] with hpp3
    have gg3 : IndexedGP pp3 := by
      have h := indexedGP_vec5 S hgp A B M Q Z mA mB mM mQ mZ neAB neAM neAQ neAZ neBM neBQ neBZ neMQ neMZ neQZ
      simpa [hpp3] using h
    have e1BQX : 0 < orient B Q Z := by
      have h := sign_imp_pos [(0, 1, 2, true), (1, 2, 3, true), (0, 1, 3, false), (1, 2, 4, false), (0, 1, 4, false)] 1 3 4 (by decide +kernel) pp3 gg3
        (litHolds_cons (litHolds_pos pp3 0 1 2 (by simpa [hpp3] using bABM)) (litHolds_cons (litHolds_pos pp3 1 2 3 (by simpa [hpp3] using bBMQ)) (litHolds_cons (litHolds_neg pp3 0 1 3 (by simpa [hpp3] using bABQ)) (litHolds_cons (litHolds_neg pp3 1 2 4 (by simpa [hpp3] using gc1)) (litHolds_cons (litHolds_neg pp3 0 1 4 (by simpa [hpp3] using g4)) (litHolds_nil pp3))))))
      simpa [hpp3] using h
    set pp4 : Fin 5 → Point := ![A, B, M, S3, Z] with hpp4
    have gg4 : IndexedGP pp4 := by
      have h := indexedGP_vec5 S hgp A B M S3 Z mA mB mM mS3 mZ neAB neAM neAS3 neAZ neBM neBS3 neBZ neMS3 neMZ neS3Z
      simpa [hpp4] using h
    have e1BSX : 0 < orient B S3 Z := by
      have h := sign_imp_pos [(0, 1, 2, true), (1, 2, 3, true), (0, 1, 3, false), (1, 2, 4, false), (0, 1, 4, false)] 1 3 4 (by decide +kernel) pp4 gg4
        (litHolds_cons (litHolds_pos pp4 0 1 2 (by simpa [hpp4] using bABM)) (litHolds_cons (litHolds_pos pp4 1 2 3 (by simpa [hpp4] using bBMS)) (litHolds_cons (litHolds_neg pp4 0 1 3 (by simpa [hpp4] using bABS)) (litHolds_cons (litHolds_neg pp4 1 2 4 (by simpa [hpp4] using gc1)) (litHolds_cons (litHolds_neg pp4 0 1 4 (by simpa [hpp4] using g4)) (litHolds_nil pp4))))))
      simpa [hpp4] using h
    set pp5 : Fin 5 → Point := ![A, B, D, M, Z] with hpp5
    have gg5 : IndexedGP pp5 := by
      have h := indexedGP_vec5 S hgp A B D M Z mA mB mD mM mZ neAB neAD neAM neAZ neBD neBM neBZ neDM neDZ neMZ
      simpa [hpp5] using h
    have e1DMX : 0 < orient D M Z := by
      have h := sign_imp_pos [(0, 1, 3, true), (1, 2, 3, true), (0, 2, 3, false), (0, 3, 4, false), (1, 2, 4, false)] 2 3 4 (by decide +kernel) pp5 gg5
        (litHolds_cons (litHolds_pos pp5 0 1 3 (by simpa [hpp5] using bABM)) (litHolds_cons (litHolds_pos pp5 1 2 3 (by simpa [hpp5] using bBDM)) (litHolds_cons (litHolds_neg pp5 0 2 3 (by simpa [hpp5] using bADM)) (litHolds_cons (litHolds_neg pp5 0 3 4 (by simpa [hpp5] using e1AMX)) (litHolds_cons (litHolds_neg pp5 1 2 4 (by simpa [hpp5] using e1BDX)) (litHolds_nil pp5))))))
      simpa [hpp5] using h
    have e1MQX : 0 < orient M Q Z := by
      have h := sign_imp_pos [(1, 2, 3, true), (1, 2, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp3 gg3
        (litHolds_cons (litHolds_pos pp3 1 2 3 (by simpa [hpp3] using bBMQ)) (litHolds_cons (litHolds_neg pp3 1 2 4 (by simpa [hpp3] using gc1)) (litHolds_cons (litHolds_pos pp3 1 3 4 (by simpa [hpp3] using e1BQX)) (litHolds_nil pp3))))
      simpa [hpp3] using h
    have e1MSX : 0 < orient M S3 Z := by
      have h := sign_imp_pos [(1, 2, 3, true), (1, 2, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp4 gg4
        (litHolds_cons (litHolds_pos pp4 1 2 3 (by simpa [hpp4] using bBMS)) (litHolds_cons (litHolds_neg pp4 1 2 4 (by simpa [hpp4] using gc1)) (litHolds_cons (litHolds_pos pp4 1 3 4 (by simpa [hpp4] using e1BSX)) (litHolds_nil pp4))))
      simpa [hpp4] using h
    exact Or.inl ⟨hr, gc1, g3, g5, e1BDX, e1BQX, e1BSX, e1DMX, e1MQX, e1MSX⟩
  · obtain ⟨g1, g2, g3, g4, g5⟩ := id hr
    have gc1 : orient C M Z < 0 := by
      have e : orient C M Z = -orient M C Z := by unfold orient; ring
      linarith [g1]
    have gc2 : 0 < orient D M Z := by
      have e : orient D M Z = -orient M D Z := by unfold orient; ring
      linarith [g2]
    set pp6 : Fin 5 → Point := ![A, B, C, D, Z] with hpp6
    have gg6 : IndexedGP pp6 := by
      have h := indexedGP_vec5 S hgp A B C D Z mA mB mC mD mZ neAB neAC neAD neAZ neBC neBD neBZ neCD neCZ neDZ
      simpa [hpp6] using h
    have e2BDX : orient B D Z < 0 := by
      have h := sign_imp_neg [(1, 2, 3, true), (2, 3, 4, false), (1, 2, 4, false)] 1 3 4 (by decide +kernel) pp6 gg6
        (litHolds_cons (litHolds_pos pp6 1 2 3 (by simpa [hpp6] using bBCD)) (litHolds_cons (litHolds_neg pp6 2 3 4 (by simpa [hpp6] using g3)) (litHolds_cons (litHolds_neg pp6 1 2 4 (by simpa [hpp6] using g4)) (litHolds_nil pp6))))
      simpa [hpp6] using h
    set pp7 : Fin 5 → Point := ![A, B, D, E, Z] with hpp7
    have gg7 : IndexedGP pp7 := by
      have h := indexedGP_vec5 S hgp A B D E Z mA mB mD mE mZ neAB neAD neAE neAZ neBD neBE neBZ neDE neDZ neEZ
      simpa [hpp7] using h
    have e2BEX : orient B E Z < 0 := by
      have h := sign_imp_neg [(1, 2, 3, true), (2, 3, 4, false), (1, 2, 4, false)] 1 3 4 (by decide +kernel) pp7 gg7
        (litHolds_cons (litHolds_pos pp7 1 2 3 (by simpa [hpp7] using bBDE)) (litHolds_cons (litHolds_neg pp7 2 3 4 (by simpa [hpp7] using g5)) (litHolds_cons (litHolds_neg pp7 1 2 4 (by simpa [hpp7] using e2BDX)) (litHolds_nil pp7))))
      simpa [hpp7] using h
    set pp8 : Fin 5 → Point := ![A, B, C, M, Z] with hpp8
    have gg8 : IndexedGP pp8 := by
      have h := indexedGP_vec5 S hgp A B C M Z mA mB mC mM mZ neAB neAC neAM neAZ neBC neBM neBZ neCM neCZ neMZ
      simpa [hpp8] using h
    have e2BMX : orient B M Z < 0 := by
      have h := sign_imp_neg [(1, 2, 3, true), (2, 3, 4, false), (1, 2, 4, false)] 1 3 4 (by decide +kernel) pp8 gg8
        (litHolds_cons (litHolds_pos pp8 1 2 3 (by simpa [hpp8] using bBCM)) (litHolds_cons (litHolds_neg pp8 2 3 4 (by simpa [hpp8] using gc1)) (litHolds_cons (litHolds_neg pp8 1 2 4 (by simpa [hpp8] using g4)) (litHolds_nil pp8))))
      simpa [hpp8] using h
    set pp9 : Fin 5 → Point := ![B, C, E, Q, Z] with hpp9
    have gg9 : IndexedGP pp9 := by
      have h := indexedGP_vec5 S hgp B C E Q Z mB mC mE mQ mZ neBC neBE neBQ neBZ neCE neCQ neCZ neEQ neEZ neQZ
      simpa [hpp9] using h
    have e2BQX : 0 < orient B Q Z := by
      have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 2, 3, true), (0, 1, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp9 gg9
        (litHolds_cons (litHolds_pos pp9 0 1 2 (by simpa [hpp9] using bBCE)) (litHolds_cons (litHolds_neg pp9 0 1 3 (by simpa [hpp9] using bBCQ)) (litHolds_cons (litHolds_pos pp9 0 2 3 (by simpa [hpp9] using bBEQ)) (litHolds_cons (litHolds_neg pp9 0 1 4 (by simpa [hpp9] using g4)) (litHolds_cons (litHolds_neg pp9 0 2 4 (by simpa [hpp9] using e2BEX)) (litHolds_nil pp9))))))
      simpa [hpp9] using h
    set pp10 : Fin 5 → Point := ![B, C, E, S3, Z] with hpp10
    have gg10 : IndexedGP pp10 := by
      have h := indexedGP_vec5 S hgp B C E S3 Z mB mC mE mS3 mZ neBC neBE neBS3 neBZ neCE neCS3 neCZ neES3 neEZ neS3Z
      simpa [hpp10] using h
    have e2BSX : 0 < orient B S3 Z := by
      have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (0, 2, 3, true), (0, 1, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp10 gg10
        (litHolds_cons (litHolds_pos pp10 0 1 2 (by simpa [hpp10] using bBCE)) (litHolds_cons (litHolds_neg pp10 0 1 3 (by simpa [hpp10] using bBCS)) (litHolds_cons (litHolds_pos pp10 0 2 3 (by simpa [hpp10] using bBES)) (litHolds_cons (litHolds_neg pp10 0 1 4 (by simpa [hpp10] using g4)) (litHolds_cons (litHolds_neg pp10 0 2 4 (by simpa [hpp10] using e2BEX)) (litHolds_nil pp10))))))
      simpa [hpp10] using h
    set pp11 : Fin 5 → Point := ![A, B, M, Q, Z] with hpp11
    have gg11 : IndexedGP pp11 := by
      have h := indexedGP_vec5 S hgp A B M Q Z mA mB mM mQ mZ neAB neAM neAQ neAZ neBM neBQ neBZ neMQ neMZ neQZ
      simpa [hpp11] using h
    have e2MQX : 0 < orient M Q Z := by
      have h := sign_imp_pos [(1, 2, 3, true), (1, 2, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp11 gg11
        (litHolds_cons (litHolds_pos pp11 1 2 3 (by simpa [hpp11] using bBMQ)) (litHolds_cons (litHolds_neg pp11 1 2 4 (by simpa [hpp11] using e2BMX)) (litHolds_cons (litHolds_pos pp11 1 3 4 (by simpa [hpp11] using e2BQX)) (litHolds_nil pp11))))
      simpa [hpp11] using h
    set pp12 : Fin 5 → Point := ![A, B, M, S3, Z] with hpp12
    have gg12 : IndexedGP pp12 := by
      have h := indexedGP_vec5 S hgp A B M S3 Z mA mB mM mS3 mZ neAB neAM neAS3 neAZ neBM neBS3 neBZ neMS3 neMZ neS3Z
      simpa [hpp12] using h
    have e2MSX : 0 < orient M S3 Z := by
      have h := sign_imp_pos [(1, 2, 3, true), (1, 2, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp12 gg12
        (litHolds_cons (litHolds_pos pp12 1 2 3 (by simpa [hpp12] using bBMS)) (litHolds_cons (litHolds_neg pp12 1 2 4 (by simpa [hpp12] using e2BMX)) (litHolds_cons (litHolds_pos pp12 1 3 4 (by simpa [hpp12] using e2BSX)) (litHolds_nil pp12))))
      simpa [hpp12] using h
    exact Or.inr (Or.inl ⟨hr, e2BMX, g4, g3, e2BDX, e2BQX, e2BSX, gc2, e2MQX, e2MSX⟩)
  · obtain ⟨g1, g2, g3, g4, g5⟩ := id hr
    have gc1 : orient D M Z < 0 := by
      have e : orient D M Z = -orient M D Z := by unfold orient; ring
      linarith [g1]
    have gc2 : 0 < orient E M Z := by
      have e : orient E M Z = -orient M E Z := by unfold orient; ring
      linarith [g2]
    have gc5 : 0 < orient A E Z := by
      have e : orient A E Z = -orient E A Z := by unfold orient; ring
      linarith [g5]
    set pp13 : Fin 5 → Point := ![A, C, D, E, Z] with hpp13
    have gg13 : IndexedGP pp13 := by
      have h := indexedGP_vec5 S hgp A C D E Z mA mC mD mE mZ neAC neAD neAE neAZ neCD neCE neCZ neDE neDZ neEZ
      simpa [hpp13] using h
    have e3ACX : 0 < orient A C Z := by
      have h := sign_imp_pos [(0, 2, 3, true), (1, 2, 3, true), (2, 3, 4, false), (1, 2, 4, false), (0, 3, 4, true)] 0 1 4 (by decide +kernel) pp13 gg13
        (litHolds_cons (litHolds_pos pp13 0 2 3 (by simpa [hpp13] using bADE)) (litHolds_cons (litHolds_pos pp13 1 2 3 (by simpa [hpp13] using bCDE)) (litHolds_cons (litHolds_neg pp13 2 3 4 (by simpa [hpp13] using g3)) (litHolds_cons (litHolds_neg pp13 1 2 4 (by simpa [hpp13] using g4)) (litHolds_cons (litHolds_pos pp13 0 3 4 (by simpa [hpp13] using gc5)) (litHolds_nil pp13))))))
      simpa [hpp13] using h
    set pp14 : Fin 5 → Point := ![A, B, D, E, Z] with hpp14
    have gg14 : IndexedGP pp14 := by
      have h := indexedGP_vec5 S hgp A B D E Z mA mB mD mE mZ neAB neAD neAE neAZ neBD neBE neBZ neDE neDZ neEZ
      simpa [hpp14] using h
    have e3ADX : 0 < orient A D Z := by
      have h := sign_imp_pos [(0, 2, 3, true), (2, 3, 4, false), (0, 3, 4, true)] 0 2 4 (by decide +kernel) pp14 gg14
        (litHolds_cons (litHolds_pos pp14 0 2 3 (by simpa [hpp14] using bADE)) (litHolds_cons (litHolds_neg pp14 2 3 4 (by simpa [hpp14] using g3)) (litHolds_cons (litHolds_pos pp14 0 3 4 (by simpa [hpp14] using gc5)) (litHolds_nil pp14))))
      simpa [hpp14] using h
    set pp15 : Fin 5 → Point := ![A, B, E, M, Z] with hpp15
    have gg15 : IndexedGP pp15 := by
      have h := indexedGP_vec5 S hgp A B E M Z mA mB mE mM mZ neAB neAE neAM neAZ neBE neBM neBZ neEM neEZ neMZ
      simpa [hpp15] using h
    have e3AMX : 0 < orient A M Z := by
      have h := sign_imp_pos [(0, 2, 3, false), (2, 3, 4, true), (0, 2, 4, true)] 0 3 4 (by decide +kernel) pp15 gg15
        (litHolds_cons (litHolds_neg pp15 0 2 3 (by simpa [hpp15] using bAEM)) (litHolds_cons (litHolds_pos pp15 2 3 4 (by simpa [hpp15] using gc2)) (litHolds_cons (litHolds_pos pp15 0 2 4 (by simpa [hpp15] using gc5)) (litHolds_nil pp15))))
      simpa [hpp15] using h
    set pp16 : Fin 5 → Point := ![A, C, E, Q, Z] with hpp16
    have gg16 : IndexedGP pp16 := by
      have h := indexedGP_vec5 S hgp A C E Q Z mA mC mE mQ mZ neAC neAE neAQ neAZ neCE neCQ neCZ neEQ neEZ neQZ
      simpa [hpp16] using h
    have e3AQX : orient A Q Z < 0 := by
      have h := sign_imp_neg [(0, 1, 2, true), (0, 2, 3, true), (0, 1, 3, false), (0, 2, 4, true), (0, 1, 4, true)] 0 3 4 (by decide +kernel) pp16 gg16
        (litHolds_cons (litHolds_pos pp16 0 1 2 (by simpa [hpp16] using bACE)) (litHolds_cons (litHolds_pos pp16 0 2 3 (by simpa [hpp16] using bAEQ)) (litHolds_cons (litHolds_neg pp16 0 1 3 (by simpa [hpp16] using bACQ)) (litHolds_cons (litHolds_pos pp16 0 2 4 (by simpa [hpp16] using gc5)) (litHolds_cons (litHolds_pos pp16 0 1 4 (by simpa [hpp16] using e3ACX)) (litHolds_nil pp16))))))
      simpa [hpp16] using h
    set pp17 : Fin 5 → Point := ![A, C, E, S3, Z] with hpp17
    have gg17 : IndexedGP pp17 := by
      have h := indexedGP_vec5 S hgp A C E S3 Z mA mC mE mS3 mZ neAC neAE neAS3 neAZ neCE neCS3 neCZ neES3 neEZ neS3Z
      simpa [hpp17] using h
    have e3ASX : orient A S3 Z < 0 := by
      have h := sign_imp_neg [(0, 1, 2, true), (0, 2, 3, true), (0, 1, 3, false), (0, 2, 4, true), (0, 1, 4, true)] 0 3 4 (by decide +kernel) pp17 gg17
        (litHolds_cons (litHolds_pos pp17 0 1 2 (by simpa [hpp17] using bACE)) (litHolds_cons (litHolds_pos pp17 0 2 3 (by simpa [hpp17] using bAES)) (litHolds_cons (litHolds_neg pp17 0 1 3 (by simpa [hpp17] using bACS)) (litHolds_cons (litHolds_pos pp17 0 2 4 (by simpa [hpp17] using gc5)) (litHolds_cons (litHolds_pos pp17 0 1 4 (by simpa [hpp17] using e3ACX)) (litHolds_nil pp17))))))
      simpa [hpp17] using h
    set pp18 : Fin 5 → Point := ![A, B, M, Q, Z] with hpp18
    have gg18 : IndexedGP pp18 := by
      have h := indexedGP_vec5 S hgp A B M Q Z mA mB mM mQ mZ neAB neAM neAQ neAZ neBM neBQ neBZ neMQ neMZ neQZ
      simpa [hpp18] using h
    have e3MQX : orient M Q Z < 0 := by
      have h := sign_imp_neg [(0, 2, 3, false), (0, 2, 4, true), (0, 3, 4, false)] 2 3 4 (by decide +kernel) pp18 gg18
        (litHolds_cons (litHolds_neg pp18 0 2 3 (by simpa [hpp18] using bAMQ)) (litHolds_cons (litHolds_pos pp18 0 2 4 (by simpa [hpp18] using e3AMX)) (litHolds_cons (litHolds_neg pp18 0 3 4 (by simpa [hpp18] using e3AQX)) (litHolds_nil pp18))))
      simpa [hpp18] using h
    set pp19 : Fin 5 → Point := ![A, B, M, S3, Z] with hpp19
    have gg19 : IndexedGP pp19 := by
      have h := indexedGP_vec5 S hgp A B M S3 Z mA mB mM mS3 mZ neAB neAM neAS3 neAZ neBM neBS3 neBZ neMS3 neMZ neS3Z
      simpa [hpp19] using h
    have e3MSX : orient M S3 Z < 0 := by
      have h := sign_imp_neg [(0, 2, 3, false), (0, 2, 4, true), (0, 3, 4, false)] 2 3 4 (by decide +kernel) pp19 gg19
        (litHolds_cons (litHolds_neg pp19 0 2 3 (by simpa [hpp19] using bAMS)) (litHolds_cons (litHolds_pos pp19 0 2 4 (by simpa [hpp19] using e3AMX)) (litHolds_cons (litHolds_neg pp19 0 3 4 (by simpa [hpp19] using e3ASX)) (litHolds_nil pp19))))
      simpa [hpp19] using h
    exact Or.inr (Or.inr (Or.inl ⟨hr, gc1, g3, gc5, e3ADX, e3AMX, e3AQX, e3ASX, e3MQX, e3MSX⟩))
  · obtain ⟨g1, g2, g3, g4, g5⟩ := id hr
    have gc1 : orient E M Z < 0 := by
      have e : orient E M Z = -orient M E Z := by unfold orient; ring
      linarith [g1]
    have gc2 : 0 < orient A M Z := by
      have e : orient A M Z = -orient M A Z := by unfold orient; ring
      linarith [g2]
    have gc3 : 0 < orient A E Z := by
      have e : orient A E Z = -orient E A Z := by unfold orient; ring
      linarith [g3]
    set pp20 : Fin 5 → Point := ![A, B, D, E, Z] with hpp20
    have gg20 : IndexedGP pp20 := by
      have h := indexedGP_vec5 S hgp A B D E Z mA mB mD mE mZ neAB neAD neAE neAZ neBD neBE neBZ neDE neDZ neEZ
      simpa [hpp20] using h
    have e4ADX : 0 < orient A D Z := by
      have h := sign_imp_pos [(0, 2, 3, true), (0, 3, 4, true), (2, 3, 4, false)] 0 2 4 (by decide +kernel) pp20 gg20
        (litHolds_cons (litHolds_pos pp20 0 2 3 (by simpa [hpp20] using bADE)) (litHolds_cons (litHolds_pos pp20 0 3 4 (by simpa [hpp20] using gc3)) (litHolds_cons (litHolds_neg pp20 2 3 4 (by simpa [hpp20] using g4)) (litHolds_nil pp20))))
      simpa [hpp20] using h
    set pp21 : Fin 5 → Point := ![A, B, M, Q, Z] with hpp21
    have gg21 : IndexedGP pp21 := by
      have h := indexedGP_vec5 S hgp A B M Q Z mA mB mM mQ mZ neAB neAM neAQ neAZ neBM neBQ neBZ neMQ neMZ neQZ
      simpa [hpp21] using h
    have e4AQX : orient A Q Z < 0 := by
      have h := sign_imp_neg [(0, 1, 2, true), (0, 2, 3, false), (0, 1, 3, false), (0, 2, 4, true), (0, 1, 4, false)] 0 3 4 (by decide +kernel) pp21 gg21
        (litHolds_cons (litHolds_pos pp21 0 1 2 (by simpa [hpp21] using bABM)) (litHolds_cons (litHolds_neg pp21 0 2 3 (by simpa [hpp21] using bAMQ)) (litHolds_cons (litHolds_neg pp21 0 1 3 (by simpa [hpp21] using bABQ)) (litHolds_cons (litHolds_pos pp21 0 2 4 (by simpa [hpp21] using gc2)) (litHolds_cons (litHolds_neg pp21 0 1 4 (by simpa [hpp21] using g5)) (litHolds_nil pp21))))))
      simpa [hpp21] using h
    set pp22 : Fin 5 → Point := ![A, B, M, S3, Z] with hpp22
    have gg22 : IndexedGP pp22 := by
      have h := indexedGP_vec5 S hgp A B M S3 Z mA mB mM mS3 mZ neAB neAM neAS3 neAZ neBM neBS3 neBZ neMS3 neMZ neS3Z
      simpa [hpp22] using h
    have e4ASX : orient A S3 Z < 0 := by
      have h := sign_imp_neg [(0, 1, 2, true), (0, 2, 3, false), (0, 1, 3, false), (0, 2, 4, true), (0, 1, 4, false)] 0 3 4 (by decide +kernel) pp22 gg22
        (litHolds_cons (litHolds_pos pp22 0 1 2 (by simpa [hpp22] using bABM)) (litHolds_cons (litHolds_neg pp22 0 2 3 (by simpa [hpp22] using bAMS)) (litHolds_cons (litHolds_neg pp22 0 1 3 (by simpa [hpp22] using bABS)) (litHolds_cons (litHolds_pos pp22 0 2 4 (by simpa [hpp22] using gc2)) (litHolds_cons (litHolds_neg pp22 0 1 4 (by simpa [hpp22] using g5)) (litHolds_nil pp22))))))
      simpa [hpp22] using h
    set pp23 : Fin 5 → Point := ![A, B, C, M, Z] with hpp23
    have gg23 : IndexedGP pp23 := by
      have h := indexedGP_vec5 S hgp A B C M Z mA mB mC mM mZ neAB neAC neAM neAZ neBC neBM neBZ neCM neCZ neMZ
      simpa [hpp23] using h
    have e4BMX : 0 < orient B M Z := by
      have h := sign_imp_pos [(0, 1, 3, true), (0, 3, 4, true), (0, 1, 4, false)] 1 3 4 (by decide +kernel) pp23 gg23
        (litHolds_cons (litHolds_pos pp23 0 1 3 (by simpa [hpp23] using bABM)) (litHolds_cons (litHolds_pos pp23 0 3 4 (by simpa [hpp23] using gc2)) (litHolds_cons (litHolds_neg pp23 0 1 4 (by simpa [hpp23] using g5)) (litHolds_nil pp23))))
      simpa [hpp23] using h
    set pp24 : Fin 5 → Point := ![A, B, D, M, Z] with hpp24
    have gg24 : IndexedGP pp24 := by
      have h := indexedGP_vec5 S hgp A B D M Z mA mB mD mM mZ neAB neAD neAM neAZ neBD neBM neBZ neDM neDZ neMZ
      simpa [hpp24] using h
    have e4DMX : orient D M Z < 0 := by
      have h := sign_imp_neg [(0, 1, 3, true), (1, 2, 3, true), (0, 2, 3, false), (0, 2, 4, true), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp24 gg24
        (litHolds_cons (litHolds_pos pp24 0 1 3 (by simpa [hpp24] using bABM)) (litHolds_cons (litHolds_pos pp24 1 2 3 (by simpa [hpp24] using bBDM)) (litHolds_cons (litHolds_neg pp24 0 2 3 (by simpa [hpp24] using bADM)) (litHolds_cons (litHolds_pos pp24 0 2 4 (by simpa [hpp24] using e4ADX)) (litHolds_cons (litHolds_pos pp24 1 3 4 (by simpa [hpp24] using e4BMX)) (litHolds_nil pp24))))))
      simpa [hpp24] using h
    have e4MQX : orient M Q Z < 0 := by
      have h := sign_imp_neg [(0, 2, 3, false), (0, 2, 4, true), (0, 3, 4, false)] 2 3 4 (by decide +kernel) pp21 gg21
        (litHolds_cons (litHolds_neg pp21 0 2 3 (by simpa [hpp21] using bAMQ)) (litHolds_cons (litHolds_pos pp21 0 2 4 (by simpa [hpp21] using gc2)) (litHolds_cons (litHolds_neg pp21 0 3 4 (by simpa [hpp21] using e4AQX)) (litHolds_nil pp21))))
      simpa [hpp21] using h
    have e4MSX : orient M S3 Z < 0 := by
      have h := sign_imp_neg [(0, 2, 3, false), (0, 2, 4, true), (0, 3, 4, false)] 2 3 4 (by decide +kernel) pp22 gg22
        (litHolds_cons (litHolds_neg pp22 0 2 3 (by simpa [hpp22] using bAMS)) (litHolds_cons (litHolds_pos pp22 0 2 4 (by simpa [hpp22] using gc2)) (litHolds_cons (litHolds_neg pp22 0 3 4 (by simpa [hpp22] using e4ASX)) (litHolds_nil pp22))))
      simpa [hpp22] using h
    exact Or.inr (Or.inr (Or.inr ⟨hr, e4DMX, g4, gc3, e4ADX, gc2, e4AQX, e4ASX, e4MQX, e4MSX⟩))


set_option maxHeartbeats 2000000 in
/-- Harborth two-point case, both outer points beyond the line `Q → S3` (with `Z`
the one seen first from `S3`). -/
theorem two_RR (S : Finset Point) (hgp : GeneralPosition S)
    (A B C D E M Q S3 Z W : Point)
    (mA : A ∈ S) (mB : B ∈ S) (mC : C ∈ S) (mD : D ∈ S) (mE : E ∈ S) (mM : M ∈ S) (mQ : Q ∈ S) (mS3 : S3 ∈ S) (mZ : Z ∈ S) (mW : W ∈ S)
    (neAB : A ≠ B) (neAC : A ≠ C) (neAD : A ≠ D) (neAE : A ≠ E)
    (neAM : A ≠ M) (neAQ : A ≠ Q) (neAS3 : A ≠ S3) (neAZ : A ≠ Z)
    (neAW : A ≠ W) (neBC : B ≠ C) (neBD : B ≠ D) (neBE : B ≠ E)
    (neBM : B ≠ M) (neBQ : B ≠ Q) (neBS3 : B ≠ S3) (neBZ : B ≠ Z)
    (neBW : B ≠ W) (neCD : C ≠ D) (neCE : C ≠ E) (neCM : C ≠ M)
    (neCQ : C ≠ Q) (neCS3 : C ≠ S3) (neCZ : C ≠ Z) (neCW : C ≠ W)
    (neDE : D ≠ E) (neDM : D ≠ M) (neDQ : D ≠ Q) (neDS3 : D ≠ S3)
    (neDZ : D ≠ Z) (neDW : D ≠ W) (neEM : E ≠ M) (neEQ : E ≠ Q)
    (neES3 : E ≠ S3) (neEZ : E ≠ Z) (neEW : E ≠ W) (neMQ : M ≠ Q)
    (neMS3 : M ≠ S3) (neMZ : M ≠ Z) (neMW : M ≠ W) (neQS3 : Q ≠ S3)
    (neQZ : Q ≠ Z) (neQW : Q ≠ W) (neS3Z : S3 ≠ Z) (neS3W : S3 ≠ W)
    (neZW : Z ≠ W)
    (hSall : ∀ q ∈ S, q = A ∨ q = B ∨ q = C ∨ q = D ∨ q = E ∨ q = M ∨ q = Q ∨ q = S3 ∨ q = Z ∨ q = W)
    (bABC : 0 < orient A B C) (bABD : 0 < orient A B D) (bABE : 0 < orient A B E)
    (bACD : 0 < orient A C D) (bACE : 0 < orient A C E) (bADE : 0 < orient A D E)
    (bBCD : 0 < orient B C D) (bBCE : 0 < orient B C E) (bBDE : 0 < orient B D E)
    (bCDE : 0 < orient C D E) (bABM : 0 < orient A B M) (bBCM : 0 < orient B C M)
    (bCDM : 0 < orient C D M) (bDEM : 0 < orient D E M) (bAEM : orient A E M < 0)
    (bACM : 0 < orient A C M) (bBDM : 0 < orient B D M) (bCEM : 0 < orient C E M)
    (bADM : orient A D M < 0) (bBEM : orient B E M < 0) (bAMQ : orient A M Q < 0)
    (bBMQ : 0 < orient B M Q) (bABQ : orient A B Q < 0) (bAEQ : 0 < orient A E Q)
    (bBCQ : orient B C Q < 0) (bAMS : orient A M S3 < 0) (bBMS : 0 < orient B M S3)
    (bABS : orient A B S3 < 0) (bAES : 0 < orient A E S3) (bBCS : orient B C S3 < 0)
    (bAQS : orient A Q S3 < 0) (bBQS : 0 < orient B Q S3) (bACQ : orient A C Q < 0)
    (bACS : orient A C S3 < 0) (bBEQ : 0 < orient B E Q) (bBES : 0 < orient B E S3)
    (bCEQ : 0 < orient C E Q) (bCES : 0 < orient C E S3) (bCMQ : 0 < orient C M Q)
    (bCMS : 0 < orient C M S3) (bCQS : 0 < orient C Q S3) (bEMQ : orient E M Q < 0)
    (bEMS : orient E M S3 < 0) (bEQS : orient E Q S3 < 0)
    (hRegZ : RegAll A B C D E M Q S3 Z) (hRegW : RegAll A B C D E M Q S3 W)
    (hsame4 : RegA M E A D B Z → RegA M E A D B W →
      (0 < orient Z E W ∧ 0 < orient A Z W) ∨ (0 < orient W E Z ∧ 0 < orient A W Z))
    (hQSZ : orient Q S3 Z < 0) (hQSW : orient Q S3 W < 0) (hSZW : 0 < orient S3 Z W) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  have hDigZ : RDig A D E M Q S3 Z ∨ LDig B C D M Q S3 Z := by
    rcases hRegZ with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inl h
  have hDigW : RDig A D E M Q S3 W ∨ LDig B C D M Q S3 W := by
    rcases hRegW with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inl h
  rcases lt_or_gt_of_ne (hgp E mE S3 mS3 Z mZ neES3 neEZ neS3Z) with hESZ | hESZ
  · -- `Z` is outside the quadrilateral `E, S3, Q, A`: pentagon `A, E, Z, S3, Q`
    have hAEZ : 0 < orient A E Z := by
      rcases hDigZ with hd | hd
      · exact hd.2.2.1
      · obtain ⟨lz1, lz2, lz3, lz4, lz5, lz6, lz7, lz8, lz9⟩ := hd
        set pp1 : Fin 5 → Point := ![A, B, E, S3, Z] with hpp1
        have gg1 : IndexedGP pp1 := by
          have h := indexedGP_vec5 S hgp A B E S3 Z mA mB mE mS3 mZ neAB neAE neAS3 neAZ neBE neBS3 neBZ neES3 neEZ neS3Z
          simpa [hpp1] using h
        have uAEX : 0 < orient A E Z := by
          have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 3, true), (1, 2, 3, true), (1, 3, 4, true), (2, 3, 4, false)] 0 2 4 (by decide +kernel) pp1 gg1
            (litHolds_cons (litHolds_pos pp1 0 1 2 (by simpa [hpp1] using bABE)) (litHolds_cons (litHolds_pos pp1 0 2 3 (by simpa [hpp1] using bAES)) (litHolds_cons (litHolds_pos pp1 1 2 3 (by simpa [hpp1] using bBES)) (litHolds_cons (litHolds_pos pp1 1 3 4 (by simpa [hpp1] using lz6)) (litHolds_cons (litHolds_neg pp1 2 3 4 (by simpa [hpp1] using hESZ)) (litHolds_nil pp1))))))
          simpa [hpp1] using h
        exact uAEX
    set pp2 : Fin 5 → Point := ![A, E, Q, S3, Z] with hpp2
    have gg2 : IndexedGP pp2 := by
      have h := indexedGP_vec5 S hgp A E Q S3 Z mA mE mQ mS3 mZ neAE neAQ neAS3 neAZ neEQ neES3 neEZ neQS3 neQZ neS3Z
      simpa [hpp2] using h
    have p1AQX : orient A Q Z < 0 := by
      have h := sign_imp_neg [(0, 1, 2, true), (0, 1, 3, true), (0, 2, 3, false), (1, 2, 3, false), (2, 3, 4, false), (1, 3, 4, false), (0, 1, 4, true)] 0 2 4 (by decide +kernel) pp2 gg2
        (litHolds_cons (litHolds_pos pp2 0 1 2 (by simpa [hpp2] using bAEQ)) (litHolds_cons (litHolds_pos pp2 0 1 3 (by simpa [hpp2] using bAES)) (litHolds_cons (litHolds_neg pp2 0 2 3 (by simpa [hpp2] using bAQS)) (litHolds_cons (litHolds_neg pp2 1 2 3 (by simpa [hpp2] using bEQS)) (litHolds_cons (litHolds_neg pp2 2 3 4 (by simpa [hpp2] using hQSZ)) (litHolds_cons (litHolds_neg pp2 1 3 4 (by simpa [hpp2] using hESZ)) (litHolds_cons (litHolds_pos pp2 0 1 4 (by simpa [hpp2] using hAEZ)) (litHolds_nil pp2))))))))
      simpa [hpp2] using h
    have p1ASX : orient A S3 Z < 0 := by
      have h := sign_imp_neg [(0, 1, 3, true), (1, 2, 3, false), (2, 3, 4, false), (1, 3, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp2 gg2
        (litHolds_cons (litHolds_pos pp2 0 1 3 (by simpa [hpp2] using bAES)) (litHolds_cons (litHolds_neg pp2 1 2 3 (by simpa [hpp2] using bEQS)) (litHolds_cons (litHolds_neg pp2 2 3 4 (by simpa [hpp2] using hQSZ)) (litHolds_cons (litHolds_neg pp2 1 3 4 (by simpa [hpp2] using hESZ)) (litHolds_cons (litHolds_neg pp2 0 2 4 (by simpa [hpp2] using p1AQX)) (litHolds_nil pp2))))))
      simpa [hpp2] using h
    have p1EQX : orient E Q Z < 0 := by
      have h := sign_imp_neg [(2, 3, 4, false), (1, 3, 4, false), (0, 1, 4, true), (0, 2, 4, false), (0, 3, 4, false)] 1 2 4 (by decide +kernel) pp2 gg2
        (litHolds_cons (litHolds_neg pp2 2 3 4 (by simpa [hpp2] using hQSZ)) (litHolds_cons (litHolds_neg pp2 1 3 4 (by simpa [hpp2] using hESZ)) (litHolds_cons (litHolds_pos pp2 0 1 4 (by simpa [hpp2] using hAEZ)) (litHolds_cons (litHolds_neg pp2 0 2 4 (by simpa [hpp2] using p1AQX)) (litHolds_cons (litHolds_neg pp2 0 3 4 (by simpa [hpp2] using p1ASX)) (litHolds_nil pp2))))))
      simpa [hpp2] using h
    have p1c012 : 0 < orient A E Z := by
      have e : orient A E Z = orient A E Z := by unfold orient; ring
      linarith [hAEZ]
    have p1c013 : 0 < orient A E S3 := by
      have e : orient A E S3 = orient A E S3 := by unfold orient; ring
      linarith [bAES]
    have p1c014 : 0 < orient A E Q := by
      have e : orient A E Q = orient A E Q := by unfold orient; ring
      linarith [bAEQ]
    have p1c023 : 0 < orient A Z S3 := by
      have e : orient A Z S3 = -orient A S3 Z := by unfold orient; ring
      linarith [p1ASX]
    have p1c024 : 0 < orient A Z Q := by
      have e : orient A Z Q = -orient A Q Z := by unfold orient; ring
      linarith [p1AQX]
    have p1c034 : 0 < orient A S3 Q := by
      have e : orient A S3 Q = -orient A Q S3 := by unfold orient; ring
      linarith [bAQS]
    have p1c123 : 0 < orient E Z S3 := by
      have e : orient E Z S3 = -orient E S3 Z := by unfold orient; ring
      linarith [hESZ]
    have p1c124 : 0 < orient E Z Q := by
      have e : orient E Z Q = -orient E Q Z := by unfold orient; ring
      linarith [p1EQX]
    have p1c134 : 0 < orient E S3 Q := by
      have e : orient E S3 Q = -orient E Q S3 := by unfold orient; ring
      linarith [bEQS]
    have p1c234 : 0 < orient Z S3 Q := by
      have e : orient Z S3 Q = -orient Q S3 Z := by unfold orient; ring
      linarith [hQSZ]
    have p1sB : orient A E B < 0 := by
      have e : orient A E B = -orient A B E := by unfold orient; ring
      linarith [bABE]
    have p1sC : orient A E C < 0 := by
      have e : orient A E C = -orient A C E := by unfold orient; ring
      linarith [bACE]
    have p1sD : orient A E D < 0 := by
      have e : orient A E D = -orient A D E := by unfold orient; ring
      linarith [bADE]
    have p1sM : orient A E M < 0 := by
      have e : orient A E M = orient A E M := by unfold orient; ring
      linarith [bAEM]
    have p1sY : orient Z S3 W < 0 := by
      have e : orient Z S3 W = -orient S3 Z W := by unfold orient; ring
      linarith [hSZW]
    refine pent5_of_signs S A E Z S3 Q mA mE mZ mS3 mQ p1c012 p1c013 p1c014 p1c023 p1c024 p1c034 p1c123 p1c124 p1c134 p1c234 ?_
    intro q hq hq0 hq1 hq2 hq3 hq4
    rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq0
    · exact Or.inl (le_of_lt p1sB)
    · exact Or.inl (le_of_lt p1sC)
    · exact Or.inl (le_of_lt p1sD)
    · exact absurd rfl hq1
    · exact Or.inl (le_of_lt p1sM)
    · exact absurd rfl hq4
    · exact absurd rfl hq3
    · exact absurd rfl hq2
    · exact Or.inr (Or.inr (Or.inl (le_of_lt p1sY)))
  · -- `Z` is inside the quadrilateral `E, S3, Q, A`
    rcases hDigZ with hdz | hdz
    · obtain ⟨rz1, rz2, rz3, rz4, rz5, rz6, rz7, rz8, rz9⟩ := hdz
      rcases hDigW with hdw | hdw
      · obtain ⟨rw1, rw2, rw3, rw4, rw5, rw6, rw7, rw8, rw9⟩ := hdw
        rcases lt_or_gt_of_ne (hgp A mA Z mZ W mW neAZ neAW neZW) with hAZW | hAZW
        · -- `W` is angularly before `Z` from `A`
          rcases hRegZ with ⟨hrz, hdd⟩ | ⟨hrz, hdd⟩ | ⟨hrz, hdd⟩ | ⟨hrz, hdd⟩
          · exfalso
            obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
            linarith
          · exfalso
            obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
            linarith
          · obtain ⟨g1, g2, g3, g4, g5⟩ := id hrz
            have gc1 : orient D M Z < 0 := by
              have e : orient D M Z = -orient M D Z := by unfold orient; ring
              linarith [g1]
            have gc2 : 0 < orient E M Z := by
              have e : orient E M Z = -orient M E Z := by unfold orient; ring
              linarith [g2]
            have gc5 : 0 < orient A E Z := by
              have e : orient A E Z = -orient E A Z := by unfold orient; ring
              linarith [g5]
            rcases hRegW with ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩
            · exfalso
              obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
              linarith
            · exfalso
              obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
              linarith
            · obtain ⟨f1, f2, f3, f4, f5⟩ := id hrw
              have fc1 : orient D M W < 0 := by
                have e : orient D M W = -orient M D W := by unfold orient; ring
                linarith [f1]
              have fc2 : 0 < orient E M W := by
                have e : orient E M W = -orient M E W := by unfold orient; ring
                linarith [f2]
              have fc5 : 0 < orient A E W := by
                have e : orient A E W = -orient E A W := by unfold orient; ring
                linarith [f5]
              set pp3 : Fin 5 → Point := ![A, B, C, D, Z] with hpp3
              have gg3 : IndexedGP pp3 := by
                have h := indexedGP_vec5 S hgp A B C D Z mA mB mC mD mZ neAB neAC neAD neAZ neBC neBD neBZ neCD neCZ neDZ
                simpa [hpp3] using h
              have q33ACX : 0 < orient A C Z := by
                have h := sign_imp_pos [(0, 2, 3, true), (0, 3, 4, true), (2, 3, 4, false)] 0 2 4 (by decide +kernel) pp3 gg3
                  (litHolds_cons (litHolds_pos pp3 0 2 3 (by simpa [hpp3] using bACD)) (litHolds_cons (litHolds_pos pp3 0 3 4 (by simpa [hpp3] using rz4)) (litHolds_cons (litHolds_neg pp3 2 3 4 (by simpa [hpp3] using g4)) (litHolds_nil pp3))))
                simpa [hpp3] using h
              set pp4 : Fin 5 → Point := ![A, C, E, S3, Z] with hpp4
              have gg4 : IndexedGP pp4 := by
                have h := indexedGP_vec5 S hgp A C E S3 Z mA mC mE mS3 mZ neAC neAE neAS3 neAZ neCE neCS3 neCZ neES3 neEZ neS3Z
                simpa [hpp4] using h
              have q33CEX : 0 < orient C E Z := by
                have h := sign_imp_pos [(0, 1, 3, false), (2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false), (0, 1, 4, true)] 1 2 4 (by decide +kernel) pp4 gg4
                  (litHolds_cons (litHolds_neg pp4 0 1 3 (by simpa [hpp4] using bACS)) (litHolds_cons (litHolds_pos pp4 2 3 4 (by simpa [hpp4] using hESZ)) (litHolds_cons (litHolds_pos pp4 0 2 4 (by simpa [hpp4] using gc5)) (litHolds_cons (litHolds_neg pp4 0 3 4 (by simpa [hpp4] using rz7)) (litHolds_cons (litHolds_pos pp4 0 1 4 (by simpa [hpp4] using q33ACX)) (litHolds_nil pp4))))))
                simpa [hpp4] using h
              set pp5 : Fin 5 → Point := ![A, C, D, E, Z] with hpp5
              have gg5 : IndexedGP pp5 := by
                have h := indexedGP_vec5 S hgp A C D E Z mA mC mD mE mZ neAC neAD neAE neAZ neCD neCE neCZ neDE neDZ neEZ
                simpa [hpp5] using h
              have q33X : orient A C D < 0 := by
                have h := sign_imp_neg [(2, 3, 4, false), (0, 3, 4, true), (0, 2, 4, true), (1, 2, 4, false), (1, 3, 4, true)] 0 1 2 (by decide +kernel) pp5 gg5
                  (litHolds_cons (litHolds_neg pp5 2 3 4 (by simpa [hpp5] using g3)) (litHolds_cons (litHolds_pos pp5 0 3 4 (by simpa [hpp5] using gc5)) (litHolds_cons (litHolds_pos pp5 0 2 4 (by simpa [hpp5] using rz4)) (litHolds_cons (litHolds_neg pp5 1 2 4 (by simpa [hpp5] using g4)) (litHolds_cons (litHolds_pos pp5 1 3 4 (by simpa [hpp5] using q33CEX)) (litHolds_nil pp5))))))
                simpa [hpp5] using h
              exfalso
              linarith
            · obtain ⟨f1, f2, f3, f4, f5⟩ := id hrw
              have fc1 : orient E M W < 0 := by
                have e : orient E M W = -orient M E W := by unfold orient; ring
                linarith [f1]
              have fc2 : 0 < orient A M W := by
                have e : orient A M W = -orient M A W := by unfold orient; ring
                linarith [f2]
              have fc3 : 0 < orient A E W := by
                have e : orient A E W = -orient E A W := by unfold orient; ring
                linarith [f3]
              set pp6 : Fin 5 → Point := ![A, B, C, D, Z] with hpp6
              have gg6 : IndexedGP pp6 := by
                have h := indexedGP_vec5 S hgp A B C D Z mA mB mC mD mZ neAB neAC neAD neAZ neBC neBD neBZ neCD neCZ neDZ
                simpa [hpp6] using h
              have q34ACX : 0 < orient A C Z := by
                have h := sign_imp_pos [(0, 2, 3, true), (0, 3, 4, true), (2, 3, 4, false)] 0 2 4 (by decide +kernel) pp6 gg6
                  (litHolds_cons (litHolds_pos pp6 0 2 3 (by simpa [hpp6] using bACD)) (litHolds_cons (litHolds_pos pp6 0 3 4 (by simpa [hpp6] using rz4)) (litHolds_cons (litHolds_neg pp6 2 3 4 (by simpa [hpp6] using g4)) (litHolds_nil pp6))))
                simpa [hpp6] using h
              set pp7 : Fin 5 → Point := ![A, C, E, S3, Z] with hpp7
              have gg7 : IndexedGP pp7 := by
                have h := indexedGP_vec5 S hgp A C E S3 Z mA mC mE mS3 mZ neAC neAE neAS3 neAZ neCE neCS3 neCZ neES3 neEZ neS3Z
                simpa [hpp7] using h
              have q34CEX : 0 < orient C E Z := by
                have h := sign_imp_pos [(0, 1, 3, false), (2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false), (0, 1, 4, true)] 1 2 4 (by decide +kernel) pp7 gg7
                  (litHolds_cons (litHolds_neg pp7 0 1 3 (by simpa [hpp7] using bACS)) (litHolds_cons (litHolds_pos pp7 2 3 4 (by simpa [hpp7] using hESZ)) (litHolds_cons (litHolds_pos pp7 0 2 4 (by simpa [hpp7] using gc5)) (litHolds_cons (litHolds_neg pp7 0 3 4 (by simpa [hpp7] using rz7)) (litHolds_cons (litHolds_pos pp7 0 1 4 (by simpa [hpp7] using q34ACX)) (litHolds_nil pp7))))))
                simpa [hpp7] using h
              set pp8 : Fin 5 → Point := ![A, C, D, E, Z] with hpp8
              have gg8 : IndexedGP pp8 := by
                have h := indexedGP_vec5 S hgp A C D E Z mA mC mD mE mZ neAC neAD neAE neAZ neCD neCE neCZ neDE neDZ neEZ
                simpa [hpp8] using h
              have q34X : orient A C D < 0 := by
                have h := sign_imp_neg [(2, 3, 4, false), (0, 3, 4, true), (0, 2, 4, true), (1, 2, 4, false), (1, 3, 4, true)] 0 1 2 (by decide +kernel) pp8 gg8
                  (litHolds_cons (litHolds_neg pp8 2 3 4 (by simpa [hpp8] using g3)) (litHolds_cons (litHolds_pos pp8 0 3 4 (by simpa [hpp8] using gc5)) (litHolds_cons (litHolds_pos pp8 0 2 4 (by simpa [hpp8] using rz4)) (litHolds_cons (litHolds_neg pp8 1 2 4 (by simpa [hpp8] using g4)) (litHolds_cons (litHolds_pos pp8 1 3 4 (by simpa [hpp8] using q34CEX)) (litHolds_nil pp8))))))
                simpa [hpp8] using h
              exfalso
              linarith
          · obtain ⟨g1, g2, g3, g4, g5⟩ := id hrz
            have gc1 : orient E M Z < 0 := by
              have e : orient E M Z = -orient M E Z := by unfold orient; ring
              linarith [g1]
            have gc2 : 0 < orient A M Z := by
              have e : orient A M Z = -orient M A Z := by unfold orient; ring
              linarith [g2]
            have gc3 : 0 < orient A E Z := by
              have e : orient A E Z = -orient E A Z := by unfold orient; ring
              linarith [g3]
            rcases hRegW with ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩
            · exfalso
              obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
              linarith
            · exfalso
              obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
              linarith
            · obtain ⟨f1, f2, f3, f4, f5⟩ := id hrw
              have fc1 : orient D M W < 0 := by
                have e : orient D M W = -orient M D W := by unfold orient; ring
                linarith [f1]
              have fc2 : 0 < orient E M W := by
                have e : orient E M W = -orient M E W := by unfold orient; ring
                linarith [f2]
              have fc5 : 0 < orient A E W := by
                have e : orient A E W = -orient E A W := by unfold orient; ring
                linarith [f5]
              set pp9 : Fin 5 → Point := ![A, B, C, D, W] with hpp9
              have gg9 : IndexedGP pp9 := by
                have h := indexedGP_vec5 S hgp A B C D W mA mB mC mD mW neAB neAC neAD neAW neBC neBD neBW neCD neCW neDW
                simpa [hpp9] using h
              have p4ACY : 0 < orient A C W := by
                have h := sign_imp_pos [(0, 2, 3, true), (0, 3, 4, true), (2, 3, 4, false)] 0 2 4 (by decide +kernel) pp9 gg9
                  (litHolds_cons (litHolds_pos pp9 0 2 3 (by simpa [hpp9] using bACD)) (litHolds_cons (litHolds_pos pp9 0 3 4 (by simpa [hpp9] using rw4)) (litHolds_cons (litHolds_neg pp9 2 3 4 (by simpa [hpp9] using f4)) (litHolds_nil pp9))))
                simpa [hpp9] using h
              set pp10 : Fin 5 → Point := ![A, D, E, S3, Z] with hpp10
              have gg10 : IndexedGP pp10 := by
                have h := indexedGP_vec5 S hgp A D E S3 Z mA mD mE mS3 mZ neAD neAE neAS3 neAZ neDE neDS3 neDZ neES3 neEZ neS3Z
                simpa [hpp10] using h
              have p4ADS : 0 < orient A D S3 := by
                have h := sign_imp_pos [(2, 3, 4, true), (1, 2, 4, false), (0, 2, 4, true), (0, 1, 4, true), (0, 3, 4, false)] 0 1 3 (by decide +kernel) pp10 gg10
                  (litHolds_cons (litHolds_pos pp10 2 3 4 (by simpa [hpp10] using hESZ)) (litHolds_cons (litHolds_neg pp10 1 2 4 (by simpa [hpp10] using g4)) (litHolds_cons (litHolds_pos pp10 0 2 4 (by simpa [hpp10] using gc3)) (litHolds_cons (litHolds_pos pp10 0 1 4 (by simpa [hpp10] using rz4)) (litHolds_cons (litHolds_neg pp10 0 3 4 (by simpa [hpp10] using rz7)) (litHolds_nil pp10))))))
                simpa [hpp10] using h
              set pp11 : Fin 5 → Point := ![A, B, C, E, Z] with hpp11
              have gg11 : IndexedGP pp11 := by
                have h := indexedGP_vec5 S hgp A B C E Z mA mB mC mE mZ neAB neAC neAE neAZ neBC neBE neBZ neCE neCZ neEZ
                simpa [hpp11] using h
              have p4BEX : 0 < orient B E Z := by
                have h := sign_imp_pos [(0, 1, 3, true), (0, 3, 4, true), (0, 1, 4, false)] 1 3 4 (by decide +kernel) pp11 gg11
                  (litHolds_cons (litHolds_pos pp11 0 1 3 (by simpa [hpp11] using bABE)) (litHolds_cons (litHolds_pos pp11 0 3 4 (by simpa [hpp11] using gc3)) (litHolds_cons (litHolds_neg pp11 0 1 4 (by simpa [hpp11] using g5)) (litHolds_nil pp11))))
                simpa [hpp11] using h
              set pp12 : Fin 5 → Point := ![A, B, E, S3, Z] with hpp12
              have gg12 : IndexedGP pp12 := by
                have h := indexedGP_vec5 S hgp A B E S3 Z mA mB mE mS3 mZ neAB neAE neAS3 neAZ neBE neBS3 neBZ neES3 neEZ neS3Z
                simpa [hpp12] using h
              have p4BSX : orient B S3 Z < 0 := by
                have h := sign_imp_neg [(2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false), (0, 1, 4, false), (1, 2, 4, true)] 1 3 4 (by decide +kernel) pp12 gg12
                  (litHolds_cons (litHolds_pos pp12 2 3 4 (by simpa [hpp12] using hESZ)) (litHolds_cons (litHolds_pos pp12 0 2 4 (by simpa [hpp12] using gc3)) (litHolds_cons (litHolds_neg pp12 0 3 4 (by simpa [hpp12] using rz7)) (litHolds_cons (litHolds_neg pp12 0 1 4 (by simpa [hpp12] using g5)) (litHolds_cons (litHolds_pos pp12 1 2 4 (by simpa [hpp12] using p4BEX)) (litHolds_nil pp12))))))
                simpa [hpp12] using h
              set pp13 : Fin 5 → Point := ![A, C, E, S3, Z] with hpp13
              have gg13 : IndexedGP pp13 := by
                have h := indexedGP_vec5 S hgp A C E S3 Z mA mC mE mS3 mZ neAC neAE neAS3 neAZ neCE neCS3 neCZ neES3 neEZ neS3Z
                simpa [hpp13] using h
              have p4CEX : 0 < orient C E Z := by
                have h := sign_imp_pos [(0, 1, 2, true), (1, 2, 3, true), (2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false)] 1 2 4 (by decide +kernel) pp13 gg13
                  (litHolds_cons (litHolds_pos pp13 0 1 2 (by simpa [hpp13] using bACE)) (litHolds_cons (litHolds_pos pp13 1 2 3 (by simpa [hpp13] using bCES)) (litHolds_cons (litHolds_pos pp13 2 3 4 (by simpa [hpp13] using hESZ)) (litHolds_cons (litHolds_pos pp13 0 2 4 (by simpa [hpp13] using gc3)) (litHolds_cons (litHolds_neg pp13 0 3 4 (by simpa [hpp13] using rz7)) (litHolds_nil pp13))))))
                simpa [hpp13] using h
              set pp14 : Fin 5 → Point := ![A, C, D, E, W] with hpp14
              have gg14 : IndexedGP pp14 := by
                have h := indexedGP_vec5 S hgp A C D E W mA mC mD mE mW neAC neAD neAE neAW neCD neCE neCW neDE neDW neEW
                simpa [hpp14] using h
              have p4CEY : orient C E W < 0 := by
                have h := sign_imp_neg [(2, 3, 4, false), (0, 3, 4, true), (0, 2, 4, true), (1, 2, 4, false), (0, 1, 4, true)] 1 3 4 (by decide +kernel) pp14 gg14
                  (litHolds_cons (litHolds_neg pp14 2 3 4 (by simpa [hpp14] using f3)) (litHolds_cons (litHolds_pos pp14 0 3 4 (by simpa [hpp14] using fc5)) (litHolds_cons (litHolds_pos pp14 0 2 4 (by simpa [hpp14] using rw4)) (litHolds_cons (litHolds_neg pp14 1 2 4 (by simpa [hpp14] using f4)) (litHolds_cons (litHolds_pos pp14 0 1 4 (by simpa [hpp14] using p4ACY)) (litHolds_nil pp14))))))
                simpa [hpp14] using h
              set pp15 : Fin 5 → Point := ![A, B, C, S3, W] with hpp15
              have gg15 : IndexedGP pp15 := by
                have h := indexedGP_vec5 S hgp A B C S3 W mA mB mC mS3 mW neAB neAC neAS3 neAW neBC neBS3 neBW neCS3 neCW neS3W
                simpa [hpp15] using h
              have p4CSY : orient C S3 W < 0 := by
                have h := sign_imp_neg [(0, 2, 3, false), (0, 3, 4, false), (0, 2, 4, true)] 2 3 4 (by decide +kernel) pp15 gg15
                  (litHolds_cons (litHolds_neg pp15 0 2 3 (by simpa [hpp15] using bACS)) (litHolds_cons (litHolds_neg pp15 0 3 4 (by simpa [hpp15] using rw7)) (litHolds_cons (litHolds_pos pp15 0 2 4 (by simpa [hpp15] using p4ACY)) (litHolds_nil pp15))))
                simpa [hpp15] using h
              set pp16 : Fin 5 → Point := ![A, C, E, Z, W] with hpp16
              have gg16 : IndexedGP pp16 := by
                have h := indexedGP_vec5 S hgp A C E Z W mA mC mE mZ mW neAC neAE neAZ neAW neCE neCZ neCW neEZ neEW neZW
                simpa [hpp16] using h
              have p4CXY : orient C Z W < 0 := by
                have h := sign_imp_neg [(0, 1, 2, true), (0, 3, 4, false), (0, 1, 4, true), (1, 2, 3, true), (1, 2, 4, false)] 1 3 4 (by decide +kernel) pp16 gg16
                  (litHolds_cons (litHolds_pos pp16 0 1 2 (by simpa [hpp16] using bACE)) (litHolds_cons (litHolds_neg pp16 0 3 4 (by simpa [hpp16] using hAZW)) (litHolds_cons (litHolds_pos pp16 0 1 4 (by simpa [hpp16] using p4ACY)) (litHolds_cons (litHolds_pos pp16 1 2 3 (by simpa [hpp16] using p4CEX)) (litHolds_cons (litHolds_neg pp16 1 2 4 (by simpa [hpp16] using p4CEY)) (litHolds_nil pp16))))))
                simpa [hpp16] using h
              have p4DES : orient D E S3 < 0 := by
                have h := sign_imp_neg [(0, 1, 2, true), (2, 3, 4, true), (1, 2, 4, false), (0, 2, 4, true), (0, 3, 4, false)] 1 2 3 (by decide +kernel) pp10 gg10
                  (litHolds_cons (litHolds_pos pp10 0 1 2 (by simpa [hpp10] using bADE)) (litHolds_cons (litHolds_pos pp10 2 3 4 (by simpa [hpp10] using hESZ)) (litHolds_cons (litHolds_neg pp10 1 2 4 (by simpa [hpp10] using g4)) (litHolds_cons (litHolds_pos pp10 0 2 4 (by simpa [hpp10] using gc3)) (litHolds_cons (litHolds_neg pp10 0 3 4 (by simpa [hpp10] using rz7)) (litHolds_nil pp10))))))
                simpa [hpp10] using h
              have p4DSX : 0 < orient D S3 Z := by
                have h := sign_imp_pos [(2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false), (0, 1, 3, true), (1, 2, 3, false)] 1 3 4 (by decide +kernel) pp10 gg10
                  (litHolds_cons (litHolds_pos pp10 2 3 4 (by simpa [hpp10] using hESZ)) (litHolds_cons (litHolds_pos pp10 0 2 4 (by simpa [hpp10] using gc3)) (litHolds_cons (litHolds_neg pp10 0 3 4 (by simpa [hpp10] using rz7)) (litHolds_cons (litHolds_pos pp10 0 1 3 (by simpa [hpp10] using p4ADS)) (litHolds_cons (litHolds_neg pp10 1 2 3 (by simpa [hpp10] using p4DES)) (litHolds_nil pp10))))))
                simpa [hpp10] using h
              set pp17 : Fin 5 → Point := ![A, C, D, S3, W] with hpp17
              have gg17 : IndexedGP pp17 := by
                have h := indexedGP_vec5 S hgp A C D S3 W mA mC mD mS3 mW neAC neAD neAS3 neAW neCD neCS3 neCW neDS3 neDW neS3W
                simpa [hpp17] using h
              have p4DSY : orient D S3 W < 0 := by
                have h := sign_imp_neg [(0, 2, 4, true), (0, 3, 4, false), (1, 2, 4, false), (0, 1, 4, true), (1, 3, 4, false)] 2 3 4 (by decide +kernel) pp17 gg17
                  (litHolds_cons (litHolds_pos pp17 0 2 4 (by simpa [hpp17] using rw4)) (litHolds_cons (litHolds_neg pp17 0 3 4 (by simpa [hpp17] using rw7)) (litHolds_cons (litHolds_neg pp17 1 2 4 (by simpa [hpp17] using f4)) (litHolds_cons (litHolds_pos pp17 0 1 4 (by simpa [hpp17] using p4ACY)) (litHolds_cons (litHolds_neg pp17 1 3 4 (by simpa [hpp17] using p4CSY)) (litHolds_nil pp17))))))
                simpa [hpp17] using h
              set pp18 : Fin 5 → Point := ![A, C, D, Z, W] with hpp18
              have gg18 : IndexedGP pp18 := by
                have h := indexedGP_vec5 S hgp A C D Z W mA mC mD mZ mW neAC neAD neAZ neAW neCD neCZ neCW neDZ neDW neZW
                simpa [hpp18] using h
              have p4DXY : orient D Z W < 0 := by
                have h := sign_imp_neg [(0, 2, 4, true), (0, 3, 4, false), (1, 2, 4, false), (0, 1, 4, true), (1, 3, 4, false)] 2 3 4 (by decide +kernel) pp18 gg18
                  (litHolds_cons (litHolds_pos pp18 0 2 4 (by simpa [hpp18] using rw4)) (litHolds_cons (litHolds_neg pp18 0 3 4 (by simpa [hpp18] using hAZW)) (litHolds_cons (litHolds_neg pp18 1 2 4 (by simpa [hpp18] using f4)) (litHolds_cons (litHolds_pos pp18 0 1 4 (by simpa [hpp18] using p4ACY)) (litHolds_cons (litHolds_neg pp18 1 3 4 (by simpa [hpp18] using p4CXY)) (litHolds_nil pp18))))))
                simpa [hpp18] using h
              set pp19 : Fin 5 → Point := ![A, C, E, S3, W] with hpp19
              have gg19 : IndexedGP pp19 := by
                have h := indexedGP_vec5 S hgp A C E S3 W mA mC mE mS3 mW neAC neAE neAS3 neAW neCE neCS3 neCW neES3 neEW neS3W
                simpa [hpp19] using h
              have p4ESY : orient E S3 W < 0 := by
                have h := sign_imp_neg [(0, 2, 4, true), (0, 3, 4, false), (0, 1, 4, true), (1, 2, 4, false), (1, 3, 4, false)] 2 3 4 (by decide +kernel) pp19 gg19
                  (litHolds_cons (litHolds_pos pp19 0 2 4 (by simpa [hpp19] using fc5)) (litHolds_cons (litHolds_neg pp19 0 3 4 (by simpa [hpp19] using rw7)) (litHolds_cons (litHolds_pos pp19 0 1 4 (by simpa [hpp19] using p4ACY)) (litHolds_cons (litHolds_neg pp19 1 2 4 (by simpa [hpp19] using p4CEY)) (litHolds_cons (litHolds_neg pp19 1 3 4 (by simpa [hpp19] using p4CSY)) (litHolds_nil pp19))))))
                simpa [hpp19] using h
              have p4EXY : orient E Z W < 0 := by
                have h := sign_imp_neg [(0, 2, 4, true), (0, 3, 4, false), (0, 1, 4, true), (1, 2, 4, false), (1, 3, 4, false)] 2 3 4 (by decide +kernel) pp16 gg16
                  (litHolds_cons (litHolds_pos pp16 0 2 4 (by simpa [hpp16] using fc5)) (litHolds_cons (litHolds_neg pp16 0 3 4 (by simpa [hpp16] using hAZW)) (litHolds_cons (litHolds_pos pp16 0 1 4 (by simpa [hpp16] using p4ACY)) (litHolds_cons (litHolds_neg pp16 1 2 4 (by simpa [hpp16] using p4CEY)) (litHolds_cons (litHolds_neg pp16 1 3 4 (by simpa [hpp16] using p4CXY)) (litHolds_nil pp16))))))
                simpa [hpp16] using h
              have p4c012 : 0 < orient D W S3 := by
                have e : orient D W S3 = -orient D S3 W := by unfold orient; ring
                linarith [p4DSY]
              have p4c013 : 0 < orient D W Z := by
                have e : orient D W Z = -orient D Z W := by unfold orient; ring
                linarith [p4DXY]
              have p4c014 : 0 < orient D W E := by
                have e : orient D W E = -orient D E W := by unfold orient; ring
                linarith [f3]
              have p4c023 : 0 < orient D S3 Z := by
                have e : orient D S3 Z = orient D S3 Z := by unfold orient; ring
                linarith [p4DSX]
              have p4c024 : 0 < orient D S3 E := by
                have e : orient D S3 E = -orient D E S3 := by unfold orient; ring
                linarith [p4DES]
              have p4c034 : 0 < orient D Z E := by
                have e : orient D Z E = -orient D E Z := by unfold orient; ring
                linarith [g4]
              have p4c123 : 0 < orient W S3 Z := by
                have e : orient W S3 Z = orient S3 Z W := by unfold orient; ring
                linarith [hSZW]
              have p4c124 : 0 < orient W S3 E := by
                have e : orient W S3 E = -orient E S3 W := by unfold orient; ring
                linarith [p4ESY]
              have p4c134 : 0 < orient W Z E := by
                have e : orient W Z E = -orient E Z W := by unfold orient; ring
                linarith [p4EXY]
              have p4c234 : 0 < orient S3 Z E := by
                have e : orient S3 Z E = orient E S3 Z := by unfold orient; ring
                linarith [hESZ]
              have p4sA : orient S3 Z A < 0 := by
                have e : orient S3 Z A = orient A S3 Z := by unfold orient; ring
                linarith [rz7]
              have p4sB : orient S3 Z B < 0 := by
                have e : orient S3 Z B = orient B S3 Z := by unfold orient; ring
                linarith [p4BSX]
              have p4sC : orient D W C < 0 := by
                have e : orient D W C = orient C D W := by unfold orient; ring
                linarith [f4]
              have p4sM : orient S3 Z M < 0 := by
                have e : orient S3 Z M = orient M S3 Z := by unfold orient; ring
                linarith [rz9]
              have p4sQ : orient S3 Z Q < 0 := by
                have e : orient S3 Z Q = orient Q S3 Z := by unfold orient; ring
                linarith [hQSZ]
              refine pent5_of_signs S D W S3 Z E mD mW mS3 mZ mE p4c012 p4c013 p4c014 p4c023 p4c024 p4c034 p4c123 p4c124 p4c134 p4c234 ?_
              intro q hq hq0 hq1 hq2 hq3 hq4
              rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · exact Or.inr (Or.inr (Or.inl (le_of_lt p4sA)))
              · exact Or.inr (Or.inr (Or.inl (le_of_lt p4sB)))
              · exact Or.inl (le_of_lt p4sC)
              · exact absurd rfl hq0
              · exact absurd rfl hq4
              · exact Or.inr (Or.inr (Or.inl (le_of_lt p4sM)))
              · exact Or.inr (Or.inr (Or.inl (le_of_lt p4sQ)))
              · exact absurd rfl hq2
              · exact absurd rfl hq3
              · exact absurd rfl hq1
            · obtain ⟨f1, f2, f3, f4, f5⟩ := id hrw
              have fc1 : orient E M W < 0 := by
                have e : orient E M W = -orient M E W := by unfold orient; ring
                linarith [f1]
              have fc2 : 0 < orient A M W := by
                have e : orient A M W = -orient M A W := by unfold orient; ring
                linarith [f2]
              have fc3 : 0 < orient A E W := by
                have e : orient A E W = -orient E A W := by unfold orient; ring
                linarith [f3]
              rcases hsame4 hrz hrw with ⟨t1, t2⟩ | ⟨t1, t2⟩
              · exfalso
                linarith
              · have t1' : 0 < orient E Z W := by
                  have e : orient E Z W = orient W E Z := by unfold orient; ring
                  linarith
                set pp20 : Fin 5 → Point := ![A, D, E, S3, Z] with hpp20
                have gg20 : IndexedGP pp20 := by
                  have h := indexedGP_vec5 S hgp A D E S3 Z mA mD mE mS3 mZ neAD neAE neAS3 neAZ neDE neDS3 neDZ neES3 neEZ neS3Z
                  simpa [hpp20] using h
                have p5ADS : 0 < orient A D S3 := by
                  have h := sign_imp_pos [(2, 3, 4, true), (1, 2, 4, false), (0, 2, 4, true), (0, 1, 4, true), (0, 3, 4, false)] 0 1 3 (by decide +kernel) pp20 gg20
                    (litHolds_cons (litHolds_pos pp20 2 3 4 (by simpa [hpp20] using hESZ)) (litHolds_cons (litHolds_neg pp20 1 2 4 (by simpa [hpp20] using g4)) (litHolds_cons (litHolds_pos pp20 0 2 4 (by simpa [hpp20] using gc3)) (litHolds_cons (litHolds_pos pp20 0 1 4 (by simpa [hpp20] using rz4)) (litHolds_cons (litHolds_neg pp20 0 3 4 (by simpa [hpp20] using rz7)) (litHolds_nil pp20))))))
                  simpa [hpp20] using h
                set pp21 : Fin 5 → Point := ![A, B, C, E, Z] with hpp21
                have gg21 : IndexedGP pp21 := by
                  have h := indexedGP_vec5 S hgp A B C E Z mA mB mC mE mZ neAB neAC neAE neAZ neBC neBE neBZ neCE neCZ neEZ
                  simpa [hpp21] using h
                have p5BEX : 0 < orient B E Z := by
                  have h := sign_imp_pos [(0, 1, 3, true), (0, 3, 4, true), (0, 1, 4, false)] 1 3 4 (by decide +kernel) pp21 gg21
                    (litHolds_cons (litHolds_pos pp21 0 1 3 (by simpa [hpp21] using bABE)) (litHolds_cons (litHolds_pos pp21 0 3 4 (by simpa [hpp21] using gc3)) (litHolds_cons (litHolds_neg pp21 0 1 4 (by simpa [hpp21] using g5)) (litHolds_nil pp21))))
                  simpa [hpp21] using h
                set pp22 : Fin 5 → Point := ![A, B, E, S3, Z] with hpp22
                have gg22 : IndexedGP pp22 := by
                  have h := indexedGP_vec5 S hgp A B E S3 Z mA mB mE mS3 mZ neAB neAE neAS3 neAZ neBE neBS3 neBZ neES3 neEZ neS3Z
                  simpa [hpp22] using h
                have p5BSX : orient B S3 Z < 0 := by
                  have h := sign_imp_neg [(2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false), (0, 1, 4, false), (1, 2, 4, true)] 1 3 4 (by decide +kernel) pp22 gg22
                    (litHolds_cons (litHolds_pos pp22 2 3 4 (by simpa [hpp22] using hESZ)) (litHolds_cons (litHolds_pos pp22 0 2 4 (by simpa [hpp22] using gc3)) (litHolds_cons (litHolds_neg pp22 0 3 4 (by simpa [hpp22] using rz7)) (litHolds_cons (litHolds_neg pp22 0 1 4 (by simpa [hpp22] using g5)) (litHolds_cons (litHolds_pos pp22 1 2 4 (by simpa [hpp22] using p5BEX)) (litHolds_nil pp22))))))
                  simpa [hpp22] using h
                set pp23 : Fin 5 → Point := ![A, C, E, S3, Z] with hpp23
                have gg23 : IndexedGP pp23 := by
                  have h := indexedGP_vec5 S hgp A C E S3 Z mA mC mE mS3 mZ neAC neAE neAS3 neAZ neCE neCS3 neCZ neES3 neEZ neS3Z
                  simpa [hpp23] using h
                have p5CEX : 0 < orient C E Z := by
                  have h := sign_imp_pos [(0, 1, 2, true), (1, 2, 3, true), (2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false)] 1 2 4 (by decide +kernel) pp23 gg23
                    (litHolds_cons (litHolds_pos pp23 0 1 2 (by simpa [hpp23] using bACE)) (litHolds_cons (litHolds_pos pp23 1 2 3 (by simpa [hpp23] using bCES)) (litHolds_cons (litHolds_pos pp23 2 3 4 (by simpa [hpp23] using hESZ)) (litHolds_cons (litHolds_pos pp23 0 2 4 (by simpa [hpp23] using gc3)) (litHolds_cons (litHolds_neg pp23 0 3 4 (by simpa [hpp23] using rz7)) (litHolds_nil pp23))))))
                  simpa [hpp23] using h
                have p5CSX : orient C S3 Z < 0 := by
                  have h := sign_imp_neg [(0, 1, 3, false), (2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false), (1, 2, 4, true)] 1 3 4 (by decide +kernel) pp23 gg23
                    (litHolds_cons (litHolds_neg pp23 0 1 3 (by simpa [hpp23] using bACS)) (litHolds_cons (litHolds_pos pp23 2 3 4 (by simpa [hpp23] using hESZ)) (litHolds_cons (litHolds_pos pp23 0 2 4 (by simpa [hpp23] using gc3)) (litHolds_cons (litHolds_neg pp23 0 3 4 (by simpa [hpp23] using rz7)) (litHolds_cons (litHolds_pos pp23 1 2 4 (by simpa [hpp23] using p5CEX)) (litHolds_nil pp23))))))
                  simpa [hpp23] using h
                have p5DES : orient D E S3 < 0 := by
                  have h := sign_imp_neg [(0, 1, 2, true), (2, 3, 4, true), (1, 2, 4, false), (0, 2, 4, true), (0, 3, 4, false)] 1 2 3 (by decide +kernel) pp20 gg20
                    (litHolds_cons (litHolds_pos pp20 0 1 2 (by simpa [hpp20] using bADE)) (litHolds_cons (litHolds_pos pp20 2 3 4 (by simpa [hpp20] using hESZ)) (litHolds_cons (litHolds_neg pp20 1 2 4 (by simpa [hpp20] using g4)) (litHolds_cons (litHolds_pos pp20 0 2 4 (by simpa [hpp20] using gc3)) (litHolds_cons (litHolds_neg pp20 0 3 4 (by simpa [hpp20] using rz7)) (litHolds_nil pp20))))))
                  simpa [hpp20] using h
                have p5DSX : 0 < orient D S3 Z := by
                  have h := sign_imp_pos [(2, 3, 4, true), (0, 2, 4, true), (0, 3, 4, false), (0, 1, 3, true), (1, 2, 3, false)] 1 3 4 (by decide +kernel) pp20 gg20
                    (litHolds_cons (litHolds_pos pp20 2 3 4 (by simpa [hpp20] using hESZ)) (litHolds_cons (litHolds_pos pp20 0 2 4 (by simpa [hpp20] using gc3)) (litHolds_cons (litHolds_neg pp20 0 3 4 (by simpa [hpp20] using rz7)) (litHolds_cons (litHolds_pos pp20 0 1 3 (by simpa [hpp20] using p5ADS)) (litHolds_cons (litHolds_neg pp20 1 2 3 (by simpa [hpp20] using p5DES)) (litHolds_nil pp20))))))
                  simpa [hpp20] using h
                set pp24 : Fin 5 → Point := ![D, E, S3, Z, W] with hpp24
                have gg24 : IndexedGP pp24 := by
                  have h := indexedGP_vec5 S hgp D E S3 Z W mD mE mS3 mZ mW neDE neDS3 neDZ neDW neES3 neEZ neEW neS3Z neS3W neZW
                  simpa [hpp24] using h
                have p5DSY : 0 < orient D S3 W := by
                  have h := sign_imp_pos [(2, 3, 4, true), (1, 2, 3, true), (0, 1, 3, false), (0, 1, 4, false), (1, 3, 4, true), (0, 1, 2, false), (0, 2, 3, true)] 0 2 4 (by decide +kernel) pp24 gg24
                    (litHolds_cons (litHolds_pos pp24 2 3 4 (by simpa [hpp24] using hSZW)) (litHolds_cons (litHolds_pos pp24 1 2 3 (by simpa [hpp24] using hESZ)) (litHolds_cons (litHolds_neg pp24 0 1 3 (by simpa [hpp24] using g4)) (litHolds_cons (litHolds_neg pp24 0 1 4 (by simpa [hpp24] using f4)) (litHolds_cons (litHolds_pos pp24 1 3 4 (by simpa [hpp24] using t1')) (litHolds_cons (litHolds_neg pp24 0 1 2 (by simpa [hpp24] using p5DES)) (litHolds_cons (litHolds_pos pp24 0 2 3 (by simpa [hpp24] using p5DSX)) (litHolds_nil pp24))))))))
                  simpa [hpp24] using h
                set pp25 : Fin 5 → Point := ![A, D, E, Z, W] with hpp25
                have gg25 : IndexedGP pp25 := by
                  have h := indexedGP_vec5 S hgp A D E Z W mA mD mE mZ mW neAD neAE neAZ neAW neDE neDZ neDW neEZ neEW neZW
                  simpa [hpp25] using h
                have p5DXY : 0 < orient D Z W := by
                  have h := sign_imp_pos [(1, 2, 4, false), (0, 2, 4, true), (0, 1, 4, true), (0, 3, 4, false), (2, 3, 4, true)] 1 3 4 (by decide +kernel) pp25 gg25
                    (litHolds_cons (litHolds_neg pp25 1 2 4 (by simpa [hpp25] using f4)) (litHolds_cons (litHolds_pos pp25 0 2 4 (by simpa [hpp25] using fc3)) (litHolds_cons (litHolds_pos pp25 0 1 4 (by simpa [hpp25] using rw4)) (litHolds_cons (litHolds_neg pp25 0 3 4 (by simpa [hpp25] using hAZW)) (litHolds_cons (litHolds_pos pp25 2 3 4 (by simpa [hpp25] using t1')) (litHolds_nil pp25))))))
                  simpa [hpp25] using h
                set pp26 : Fin 5 → Point := ![A, E, S3, Z, W] with hpp26
                have gg26 : IndexedGP pp26 := by
                  have h := indexedGP_vec5 S hgp A E S3 Z W mA mE mS3 mZ mW neAE neAS3 neAZ neAW neES3 neEZ neEW neS3Z neS3W neZW
                  simpa [hpp26] using h
                have p5ESY : 0 < orient E S3 W := by
                  have h := sign_imp_pos [(1, 2, 3, true), (0, 1, 4, true), (0, 2, 4, false), (0, 3, 4, false), (1, 3, 4, true)] 1 2 4 (by decide +kernel) pp26 gg26
                    (litHolds_cons (litHolds_pos pp26 1 2 3 (by simpa [hpp26] using hESZ)) (litHolds_cons (litHolds_pos pp26 0 1 4 (by simpa [hpp26] using fc3)) (litHolds_cons (litHolds_neg pp26 0 2 4 (by simpa [hpp26] using rw7)) (litHolds_cons (litHolds_neg pp26 0 3 4 (by simpa [hpp26] using hAZW)) (litHolds_cons (litHolds_pos pp26 1 3 4 (by simpa [hpp26] using t1')) (litHolds_nil pp26))))))
                  simpa [hpp26] using h
                have p5c012 : 0 < orient D S3 Z := by
                  have e : orient D S3 Z = orient D S3 Z := by unfold orient; ring
                  linarith [p5DSX]
                have p5c013 : 0 < orient D S3 W := by
                  have e : orient D S3 W = orient D S3 W := by unfold orient; ring
                  linarith [p5DSY]
                have p5c014 : 0 < orient D S3 E := by
                  have e : orient D S3 E = -orient D E S3 := by unfold orient; ring
                  linarith [p5DES]
                have p5c023 : 0 < orient D Z W := by
                  have e : orient D Z W = orient D Z W := by unfold orient; ring
                  linarith [p5DXY]
                have p5c024 : 0 < orient D Z E := by
                  have e : orient D Z E = -orient D E Z := by unfold orient; ring
                  linarith [g4]
                have p5c034 : 0 < orient D W E := by
                  have e : orient D W E = -orient D E W := by unfold orient; ring
                  linarith [f4]
                have p5c123 : 0 < orient S3 Z W := by
                  have e : orient S3 Z W = orient S3 Z W := by unfold orient; ring
                  linarith [hSZW]
                have p5c124 : 0 < orient S3 Z E := by
                  have e : orient S3 Z E = orient E S3 Z := by unfold orient; ring
                  linarith [hESZ]
                have p5c134 : 0 < orient S3 W E := by
                  have e : orient S3 W E = orient E S3 W := by unfold orient; ring
                  linarith [p5ESY]
                have p5c234 : 0 < orient Z W E := by
                  have e : orient Z W E = orient E Z W := by unfold orient; ring
                  linarith [t1']
                have p5sA : orient S3 Z A < 0 := by
                  have e : orient S3 Z A = orient A S3 Z := by unfold orient; ring
                  linarith [rz7]
                have p5sB : orient S3 Z B < 0 := by
                  have e : orient S3 Z B = orient B S3 Z := by unfold orient; ring
                  linarith [p5BSX]
                have p5sC : orient S3 Z C < 0 := by
                  have e : orient S3 Z C = orient C S3 Z := by unfold orient; ring
                  linarith [p5CSX]
                have p5sM : orient S3 Z M < 0 := by
                  have e : orient S3 Z M = orient M S3 Z := by unfold orient; ring
                  linarith [rz9]
                have p5sQ : orient S3 Z Q < 0 := by
                  have e : orient S3 Z Q = orient Q S3 Z := by unfold orient; ring
                  linarith [hQSZ]
                refine pent5_of_signs S D S3 Z W E mD mS3 mZ mW mE p5c012 p5c013 p5c014 p5c023 p5c024 p5c034 p5c123 p5c124 p5c134 p5c234 ?_
                intro q hq hq0 hq1 hq2 hq3 hq4
                rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · exact Or.inr (Or.inl (le_of_lt p5sA))
                · exact Or.inr (Or.inl (le_of_lt p5sB))
                · exact Or.inr (Or.inl (le_of_lt p5sC))
                · exact absurd rfl hq0
                · exact absurd rfl hq4
                · exact Or.inr (Or.inl (le_of_lt p5sM))
                · exact Or.inr (Or.inl (le_of_lt p5sQ))
                · exact absurd rfl hq1
                · exact absurd rfl hq2
                · exact absurd rfl hq3
        · -- the pentagon `A, Z, W, S3, Q`
          set pp27 : Fin 5 → Point := ![A, Q, S3, Z, W] with hpp27
          have gg27 : IndexedGP pp27 := by
            have h := indexedGP_vec5 S hgp A Q S3 Z W mA mQ mS3 mZ mW neAQ neAS3 neAZ neAW neQS3 neQZ neQW neS3Z neS3W neZW
            simpa [hpp27] using h
          have p3QXY : 0 < orient Q Z W := by
            have h := sign_imp_pos [(1, 2, 4, false), (2, 3, 4, true), (0, 1, 4, false), (0, 2, 4, false), (0, 3, 4, true)] 1 3 4 (by decide +kernel) pp27 gg27
              (litHolds_cons (litHolds_neg pp27 1 2 4 (by simpa [hpp27] using hQSW)) (litHolds_cons (litHolds_pos pp27 2 3 4 (by simpa [hpp27] using hSZW)) (litHolds_cons (litHolds_neg pp27 0 1 4 (by simpa [hpp27] using rw6)) (litHolds_cons (litHolds_neg pp27 0 2 4 (by simpa [hpp27] using rw7)) (litHolds_cons (litHolds_pos pp27 0 3 4 (by simpa [hpp27] using hAZW)) (litHolds_nil pp27))))))
            simpa [hpp27] using h
          have p3c012 : 0 < orient A Z W := by
            have e : orient A Z W = orient A Z W := by unfold orient; ring
            linarith [hAZW]
          have p3c013 : 0 < orient A Z S3 := by
            have e : orient A Z S3 = -orient A S3 Z := by unfold orient; ring
            linarith [rz7]
          have p3c014 : 0 < orient A Z Q := by
            have e : orient A Z Q = -orient A Q Z := by unfold orient; ring
            linarith [rz6]
          have p3c023 : 0 < orient A W S3 := by
            have e : orient A W S3 = -orient A S3 W := by unfold orient; ring
            linarith [rw7]
          have p3c024 : 0 < orient A W Q := by
            have e : orient A W Q = -orient A Q W := by unfold orient; ring
            linarith [rw6]
          have p3c034 : 0 < orient A S3 Q := by
            have e : orient A S3 Q = -orient A Q S3 := by unfold orient; ring
            linarith [bAQS]
          have p3c123 : 0 < orient Z W S3 := by
            have e : orient Z W S3 = orient S3 Z W := by unfold orient; ring
            linarith [hSZW]
          have p3c124 : 0 < orient Z W Q := by
            have e : orient Z W Q = orient Q Z W := by unfold orient; ring
            linarith [p3QXY]
          have p3c134 : 0 < orient Z S3 Q := by
            have e : orient Z S3 Q = -orient Q S3 Z := by unfold orient; ring
            linarith [hQSZ]
          have p3c234 : 0 < orient W S3 Q := by
            have e : orient W S3 Q = -orient Q S3 W := by unfold orient; ring
            linarith [hQSW]
          have p3sB : orient S3 Q B < 0 := by
            have e : orient S3 Q B = -orient B Q S3 := by unfold orient; ring
            linarith [bBQS]
          have p3sC : orient S3 Q C < 0 := by
            have e : orient S3 Q C = -orient C Q S3 := by unfold orient; ring
            linarith [bCQS]
          have p3sD : orient A Z D < 0 := by
            have e : orient A Z D = -orient A D Z := by unfold orient; ring
            linarith [rz4]
          have p3sE : orient A Z E < 0 := by
            have e : orient A Z E = -orient A E Z := by unfold orient; ring
            linarith [rz3]
          have p3sM : orient A Z M < 0 := by
            have e : orient A Z M = -orient A M Z := by unfold orient; ring
            linarith [rz5]
          refine pent5_of_signs S A Z W S3 Q mA mZ mW mS3 mQ p3c012 p3c013 p3c014 p3c023 p3c024 p3c034 p3c123 p3c124 p3c134 p3c234 ?_
          intro q hq hq0 hq1 hq2 hq3 hq4
          rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd rfl hq0
          · exact Or.inr (Or.inr (Or.inr (Or.inl (le_of_lt p3sB))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (le_of_lt p3sC))))
          · exact Or.inl (le_of_lt p3sD)
          · exact Or.inl (le_of_lt p3sE)
          · exact Or.inl (le_of_lt p3sM)
          · exact absurd rfl hq4
          · exact absurd rfl hq3
          · exact absurd rfl hq1
          · exact absurd rfl hq2
      · obtain ⟨lw1, lw2, lw3, lw4, lw5, lw6, lw7, lw8, lw9⟩ := hdw
        set pp28 : Fin 5 → Point := ![A, D, E, S3, Z] with hpp28
        have gg28 : IndexedGP pp28 := by
          have h := indexedGP_vec5 S hgp A D E S3 Z mA mD mE mS3 mZ neAD neAE neAS3 neAZ neDE neDS3 neDZ neES3 neEZ neS3Z
          simpa [hpp28] using h
        have kRLADS : 0 < orient A D S3 := by
          have h := sign_imp_pos [(2, 3, 4, true), (1, 2, 4, false), (0, 2, 4, true), (0, 1, 4, true), (0, 3, 4, false)] 0 1 3 (by decide +kernel) pp28 gg28
            (litHolds_cons (litHolds_pos pp28 2 3 4 (by simpa [hpp28] using hESZ)) (litHolds_cons (litHolds_neg pp28 1 2 4 (by simpa [hpp28] using rz2)) (litHolds_cons (litHolds_pos pp28 0 2 4 (by simpa [hpp28] using rz3)) (litHolds_cons (litHolds_pos pp28 0 1 4 (by simpa [hpp28] using rz4)) (litHolds_cons (litHolds_neg pp28 0 3 4 (by simpa [hpp28] using rz7)) (litHolds_nil pp28))))))
          simpa [hpp28] using h
        set pp29 : Fin 5 → Point := ![A, B, C, D, S3] with hpp29
        have gg29 : IndexedGP pp29 := by
          have h := indexedGP_vec5 S hgp A B C D S3 mA mB mC mD mS3 neAB neAC neAD neAS3 neBC neBD neBS3 neCD neCS3 neDS3
          simpa [hpp29] using h
        have kRLBDS : 0 < orient B D S3 := by
          have h := sign_imp_pos [(0, 2, 3, true), (0, 1, 4, false), (1, 2, 4, false), (0, 2, 4, false), (0, 3, 4, true)] 1 3 4 (by decide +kernel) pp29 gg29
            (litHolds_cons (litHolds_pos pp29 0 2 3 (by simpa [hpp29] using bACD)) (litHolds_cons (litHolds_neg pp29 0 1 4 (by simpa [hpp29] using bABS)) (litHolds_cons (litHolds_neg pp29 1 2 4 (by simpa [hpp29] using bBCS)) (litHolds_cons (litHolds_neg pp29 0 2 4 (by simpa [hpp29] using bACS)) (litHolds_cons (litHolds_pos pp29 0 3 4 (by simpa [hpp29] using kRLADS)) (litHolds_nil pp29))))))
          simpa [hpp29] using h
        set pp30 : Fin 5 → Point := ![B, D, Q, S3, W] with hpp30
        have gg30 : IndexedGP pp30 := by
          have h := indexedGP_vec5 S hgp B D Q S3 W mB mD mQ mS3 mW neBD neBQ neBS3 neBW neDQ neDS3 neDW neQS3 neQW neS3W
          simpa [hpp30] using h
        have kRLDQS : 0 < orient D Q S3 := by
          have h := sign_imp_pos [(0, 2, 3, true), (2, 3, 4, false), (0, 1, 4, false), (0, 3, 4, true), (0, 1, 3, true)] 1 2 3 (by decide +kernel) pp30 gg30
            (litHolds_cons (litHolds_pos pp30 0 2 3 (by simpa [hpp30] using bBQS)) (litHolds_cons (litHolds_neg pp30 2 3 4 (by simpa [hpp30] using hQSW)) (litHolds_cons (litHolds_neg pp30 0 1 4 (by simpa [hpp30] using lw4)) (litHolds_cons (litHolds_pos pp30 0 3 4 (by simpa [hpp30] using lw6)) (litHolds_cons (litHolds_pos pp30 0 1 3 (by simpa [hpp30] using kRLBDS)) (litHolds_nil pp30))))))
          simpa [hpp30] using h
        set pp31 : Fin 5 → Point := ![A, B, D, Q, S3] with hpp31
        have gg31 : IndexedGP pp31 := by
          have h := indexedGP_vec5 S hgp A B D Q S3 mA mB mD mQ mS3 neAB neAD neAQ neAS3 neBD neBQ neBS3 neDQ neDS3 neQS3
          simpa [hpp31] using h
        have kRLX : 0 < orient A B S3 := by
          have h := sign_imp_pos [(0, 3, 4, false), (1, 3, 4, true), (0, 2, 4, true), (1, 2, 4, true), (2, 3, 4, true)] 0 1 4 (by decide +kernel) pp31 gg31
            (litHolds_cons (litHolds_neg pp31 0 3 4 (by simpa [hpp31] using bAQS)) (litHolds_cons (litHolds_pos pp31 1 3 4 (by simpa [hpp31] using bBQS)) (litHolds_cons (litHolds_pos pp31 0 2 4 (by simpa [hpp31] using kRLADS)) (litHolds_cons (litHolds_pos pp31 1 2 4 (by simpa [hpp31] using kRLBDS)) (litHolds_cons (litHolds_pos pp31 2 3 4 (by simpa [hpp31] using kRLDQS)) (litHolds_nil pp31))))))
          simpa [hpp31] using h
        exfalso
        linarith
    · obtain ⟨lz1, lz2, lz3, lz4, lz5, lz6, lz7, lz8, lz9⟩ := hdz
      rcases hDigW with hdw | hdw
      · obtain ⟨rw1, rw2, rw3, rw4, rw5, rw6, rw7, rw8, rw9⟩ := hdw
        set pp32 : Fin 5 → Point := ![B, E, Q, S3, Z] with hpp32
        have gg32 : IndexedGP pp32 := by
          have h := indexedGP_vec5 S hgp B E Q S3 Z mB mE mQ mS3 mZ neBE neBQ neBS3 neBZ neEQ neES3 neEZ neQS3 neQZ neS3Z
          simpa [hpp32] using h
        have kLRX : orient E S3 Z < 0 := by
          have h := sign_imp_neg [(0, 2, 3, true), (0, 1, 3, true), (1, 2, 3, false), (2, 3, 4, false), (0, 3, 4, true)] 1 3 4 (by decide +kernel) pp32 gg32
            (litHolds_cons (litHolds_pos pp32 0 2 3 (by simpa [hpp32] using bBQS)) (litHolds_cons (litHolds_pos pp32 0 1 3 (by simpa [hpp32] using bBES)) (litHolds_cons (litHolds_neg pp32 1 2 3 (by simpa [hpp32] using bEQS)) (litHolds_cons (litHolds_neg pp32 2 3 4 (by simpa [hpp32] using hQSZ)) (litHolds_cons (litHolds_pos pp32 0 3 4 (by simpa [hpp32] using lz6)) (litHolds_nil pp32))))))
          simpa [hpp32] using h
        exfalso
        linarith
      · obtain ⟨lw1, lw2, lw3, lw4, lw5, lw6, lw7, lw8, lw9⟩ := hdw
        set pp33 : Fin 5 → Point := ![B, E, Q, S3, Z] with hpp33
        have gg33 : IndexedGP pp33 := by
          have h := indexedGP_vec5 S hgp B E Q S3 Z mB mE mQ mS3 mZ neBE neBQ neBS3 neBZ neEQ neES3 neEZ neQS3 neQZ neS3Z
          simpa [hpp33] using h
        have kLLX : orient B E S3 < 0 := by
          have h := sign_imp_neg [(0, 2, 3, true), (1, 2, 3, false), (2, 3, 4, false), (1, 3, 4, true), (0, 3, 4, true)] 0 1 3 (by decide +kernel) pp33 gg33
            (litHolds_cons (litHolds_pos pp33 0 2 3 (by simpa [hpp33] using bBQS)) (litHolds_cons (litHolds_neg pp33 1 2 3 (by simpa [hpp33] using bEQS)) (litHolds_cons (litHolds_neg pp33 2 3 4 (by simpa [hpp33] using hQSZ)) (litHolds_cons (litHolds_pos pp33 1 3 4 (by simpa [hpp33] using hESZ)) (litHolds_cons (litHolds_pos pp33 0 3 4 (by simpa [hpp33] using lz6)) (litHolds_nil pp33))))))
          simpa [hpp33] using h
        exfalso
        linarith


set_option maxHeartbeats 2000000 in
/-- Harborth two-point case, both outer points on the left of `Q → S3` (with `Z`
the one seen last from `S3`). -/
theorem two_LL (S : Finset Point) (hgp : GeneralPosition S)
    (A B C D E M Q S3 Z W : Point)
    (mA : A ∈ S) (mB : B ∈ S) (mC : C ∈ S) (mD : D ∈ S) (mE : E ∈ S) (mM : M ∈ S) (mQ : Q ∈ S) (mS3 : S3 ∈ S) (mZ : Z ∈ S) (mW : W ∈ S)
    (neAB : A ≠ B) (neAC : A ≠ C) (neAD : A ≠ D) (neAE : A ≠ E)
    (neAM : A ≠ M) (neAQ : A ≠ Q) (neAS3 : A ≠ S3) (neAZ : A ≠ Z)
    (neAW : A ≠ W) (neBC : B ≠ C) (neBD : B ≠ D) (neBE : B ≠ E)
    (neBM : B ≠ M) (neBQ : B ≠ Q) (neBS3 : B ≠ S3) (neBZ : B ≠ Z)
    (neBW : B ≠ W) (neCD : C ≠ D) (neCE : C ≠ E) (neCM : C ≠ M)
    (neCQ : C ≠ Q) (neCS3 : C ≠ S3) (neCZ : C ≠ Z) (neCW : C ≠ W)
    (neDE : D ≠ E) (neDM : D ≠ M) (neDQ : D ≠ Q) (neDS3 : D ≠ S3)
    (neDZ : D ≠ Z) (neDW : D ≠ W) (neEM : E ≠ M) (neEQ : E ≠ Q)
    (neES3 : E ≠ S3) (neEZ : E ≠ Z) (neEW : E ≠ W) (neMQ : M ≠ Q)
    (neMS3 : M ≠ S3) (neMZ : M ≠ Z) (neMW : M ≠ W) (neQS3 : Q ≠ S3)
    (neQZ : Q ≠ Z) (neQW : Q ≠ W) (neS3Z : S3 ≠ Z) (neS3W : S3 ≠ W)
    (neZW : Z ≠ W)
    (hSall : ∀ q ∈ S, q = A ∨ q = B ∨ q = C ∨ q = D ∨ q = E ∨ q = M ∨ q = Q ∨ q = S3 ∨ q = Z ∨ q = W)
    (bABC : 0 < orient A B C) (bABD : 0 < orient A B D) (bABE : 0 < orient A B E)
    (bACD : 0 < orient A C D) (bACE : 0 < orient A C E) (bADE : 0 < orient A D E)
    (bBCD : 0 < orient B C D) (bBCE : 0 < orient B C E) (bBDE : 0 < orient B D E)
    (bCDE : 0 < orient C D E) (bABM : 0 < orient A B M) (bBCM : 0 < orient B C M)
    (bCDM : 0 < orient C D M) (bDEM : 0 < orient D E M) (bAEM : orient A E M < 0)
    (bACM : 0 < orient A C M) (bBDM : 0 < orient B D M) (bCEM : 0 < orient C E M)
    (bADM : orient A D M < 0) (bBEM : orient B E M < 0) (bAMQ : orient A M Q < 0)
    (bBMQ : 0 < orient B M Q) (bABQ : orient A B Q < 0) (bAEQ : 0 < orient A E Q)
    (bBCQ : orient B C Q < 0) (bAMS : orient A M S3 < 0) (bBMS : 0 < orient B M S3)
    (bABS : orient A B S3 < 0) (bAES : 0 < orient A E S3) (bBCS : orient B C S3 < 0)
    (bAQS : orient A Q S3 < 0) (bBQS : 0 < orient B Q S3) (bACQ : orient A C Q < 0)
    (bACS : orient A C S3 < 0) (bBEQ : 0 < orient B E Q) (bBES : 0 < orient B E S3)
    (bCEQ : 0 < orient C E Q) (bCES : 0 < orient C E S3) (bCMQ : 0 < orient C M Q)
    (bCMS : 0 < orient C M S3) (bCQS : 0 < orient C Q S3) (bEMQ : orient E M Q < 0)
    (bEMS : orient E M S3 < 0) (bEQS : orient E Q S3 < 0)
    (hRegZ : RegAll A B C D E M Q S3 Z) (hRegW : RegAll A B C D E M Q S3 W)
    (hsame1 : RegA M B C A D Z → RegA M B C A D W →
      (0 < orient Z B W ∧ 0 < orient C Z W) ∨ (0 < orient W B Z ∧ 0 < orient C W Z))
    (hQSZ : 0 < orient Q S3 Z) (hQSW : 0 < orient Q S3 W) (hSZW : orient S3 Z W < 0) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  have hDigZ : RDig A D E M Q S3 Z ∨ LDig B C D M Q S3 Z := by
    rcases hRegZ with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inl h
  have hDigW : RDig A D E M Q S3 W ∨ LDig B C D M Q S3 W := by
    rcases hRegW with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inl h
  rcases lt_or_gt_of_ne (hgp C mC S3 mS3 Z mZ neCS3 neCZ neS3Z) with hCSZ | hCSZ
  · -- `Z` is inside the quadrilateral `B, Q, S3, C`
    rcases hDigZ with hdz | hdz
    · obtain ⟨rz1, rz2, rz3, rz4, rz5, rz6, rz7, rz8, rz9⟩ := hdz
      rcases hDigW with hdw | hdw
      · obtain ⟨rw1, rw2, rw3, rw4, rw5, rw6, rw7, rw8, rw9⟩ := hdw
        set pp1 : Fin 5 → Point := ![A, C, Q, S3, Z] with hpp1
        have gg1 : IndexedGP pp1 := by
          have h := indexedGP_vec5 S hgp A C Q S3 Z mA mC mQ mS3 mZ neAC neAQ neAS3 neAZ neCQ neCS3 neCZ neQS3 neQZ neS3Z
          simpa [hpp1] using h
        have jRRACX : 0 < orient A C Z := by
          have h := sign_imp_pos [(0, 2, 3, false), (0, 1, 3, false), (1, 2, 3, true), (2, 3, 4, true), (1, 3, 4, false), (0, 3, 4, false)] 0 1 4 (by decide +kernel) pp1 gg1
            (litHolds_cons (litHolds_neg pp1 0 2 3 (by simpa [hpp1] using bAQS)) (litHolds_cons (litHolds_neg pp1 0 1 3 (by simpa [hpp1] using bACS)) (litHolds_cons (litHolds_pos pp1 1 2 3 (by simpa [hpp1] using bCQS)) (litHolds_cons (litHolds_pos pp1 2 3 4 (by simpa [hpp1] using hQSZ)) (litHolds_cons (litHolds_neg pp1 1 3 4 (by simpa [hpp1] using hCSZ)) (litHolds_cons (litHolds_neg pp1 0 3 4 (by simpa [hpp1] using rz7)) (litHolds_nil pp1)))))))
          simpa [hpp1] using h
        set pp2 : Fin 5 → Point := ![A, B, Q, S3, Z] with hpp2
        have gg2 : IndexedGP pp2 := by
          have h := indexedGP_vec5 S hgp A B Q S3 Z mA mB mQ mS3 mZ neAB neAQ neAS3 neAZ neBQ neBS3 neBZ neQS3 neQZ neS3Z
          simpa [hpp2] using h
        have jRRBQX : 0 < orient B Q Z := by
          have h := sign_imp_pos [(0, 1, 2, false), (0, 2, 3, false), (1, 2, 3, true), (2, 3, 4, true), (0, 3, 4, false)] 1 2 4 (by decide +kernel) pp2 gg2
            (litHolds_cons (litHolds_neg pp2 0 1 2 (by simpa [hpp2] using bABQ)) (litHolds_cons (litHolds_neg pp2 0 2 3 (by simpa [hpp2] using bAQS)) (litHolds_cons (litHolds_pos pp2 1 2 3 (by simpa [hpp2] using bBQS)) (litHolds_cons (litHolds_pos pp2 2 3 4 (by simpa [hpp2] using hQSZ)) (litHolds_cons (litHolds_neg pp2 0 3 4 (by simpa [hpp2] using rz7)) (litHolds_nil pp2))))))
          simpa [hpp2] using h
        set pp3 : Fin 5 → Point := ![A, B, C, Q, Z] with hpp3
        have gg3 : IndexedGP pp3 := by
          have h := indexedGP_vec5 S hgp A B C Q Z mA mB mC mQ mZ neAB neAC neAQ neAZ neBC neBQ neBZ neCQ neCZ neQZ
          simpa [hpp3] using h
        have jRRCQX : 0 < orient C Q Z := by
          have h := sign_imp_pos [(0, 1, 3, false), (1, 2, 3, false), (0, 2, 3, false), (0, 3, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp3 gg3
            (litHolds_cons (litHolds_neg pp3 0 1 3 (by simpa [hpp3] using bABQ)) (litHolds_cons (litHolds_neg pp3 1 2 3 (by simpa [hpp3] using bBCQ)) (litHolds_cons (litHolds_neg pp3 0 2 3 (by simpa [hpp3] using bACQ)) (litHolds_cons (litHolds_neg pp3 0 3 4 (by simpa [hpp3] using rz6)) (litHolds_cons (litHolds_pos pp3 1 3 4 (by simpa [hpp3] using jRRBQX)) (litHolds_nil pp3))))))
          simpa [hpp3] using h
        set pp4 : Fin 5 → Point := ![A, C, E, Q, Z] with hpp4
        have gg4 : IndexedGP pp4 := by
          have h := indexedGP_vec5 S hgp A C E Q Z mA mC mE mQ mZ neAC neAE neAQ neAZ neCE neCQ neCZ neEQ neEZ neQZ
          simpa [hpp4] using h
        have jRRX : orient A C E < 0 := by
          have h := sign_imp_neg [(0, 1, 3, false), (0, 3, 4, false), (0, 1, 4, true), (1, 3, 4, true)] 0 1 2 (by decide +kernel) pp4 gg4
            (litHolds_cons (litHolds_neg pp4 0 1 3 (by simpa [hpp4] using bACQ)) (litHolds_cons (litHolds_neg pp4 0 3 4 (by simpa [hpp4] using rz6)) (litHolds_cons (litHolds_pos pp4 0 1 4 (by simpa [hpp4] using jRRACX)) (litHolds_cons (litHolds_pos pp4 1 3 4 (by simpa [hpp4] using jRRCQX)) (litHolds_nil pp4)))))
          simpa [hpp4] using h
        exfalso
        linarith
      · obtain ⟨lw1, lw2, lw3, lw4, lw5, lw6, lw7, lw8, lw9⟩ := hdw
        set pp5 : Fin 5 → Point := ![A, C, Q, S3, Z] with hpp5
        have gg5 : IndexedGP pp5 := by
          have h := indexedGP_vec5 S hgp A C Q S3 Z mA mC mQ mS3 mZ neAC neAQ neAS3 neAZ neCQ neCS3 neCZ neQS3 neQZ neS3Z
          simpa [hpp5] using h
        have jRLACX : 0 < orient A C Z := by
          have h := sign_imp_pos [(0, 2, 3, false), (0, 1, 3, false), (1, 2, 3, true), (2, 3, 4, true), (1, 3, 4, false), (0, 3, 4, false)] 0 1 4 (by decide +kernel) pp5 gg5
            (litHolds_cons (litHolds_neg pp5 0 2 3 (by simpa [hpp5] using bAQS)) (litHolds_cons (litHolds_neg pp5 0 1 3 (by simpa [hpp5] using bACS)) (litHolds_cons (litHolds_pos pp5 1 2 3 (by simpa [hpp5] using bCQS)) (litHolds_cons (litHolds_pos pp5 2 3 4 (by simpa [hpp5] using hQSZ)) (litHolds_cons (litHolds_neg pp5 1 3 4 (by simpa [hpp5] using hCSZ)) (litHolds_cons (litHolds_neg pp5 0 3 4 (by simpa [hpp5] using rz7)) (litHolds_nil pp5)))))))
          simpa [hpp5] using h
        set pp6 : Fin 5 → Point := ![A, B, Q, S3, Z] with hpp6
        have gg6 : IndexedGP pp6 := by
          have h := indexedGP_vec5 S hgp A B Q S3 Z mA mB mQ mS3 mZ neAB neAQ neAS3 neAZ neBQ neBS3 neBZ neQS3 neQZ neS3Z
          simpa [hpp6] using h
        have jRLBQX : 0 < orient B Q Z := by
          have h := sign_imp_pos [(0, 1, 2, false), (0, 2, 3, false), (1, 2, 3, true), (2, 3, 4, true), (0, 3, 4, false)] 1 2 4 (by decide +kernel) pp6 gg6
            (litHolds_cons (litHolds_neg pp6 0 1 2 (by simpa [hpp6] using bABQ)) (litHolds_cons (litHolds_neg pp6 0 2 3 (by simpa [hpp6] using bAQS)) (litHolds_cons (litHolds_pos pp6 1 2 3 (by simpa [hpp6] using bBQS)) (litHolds_cons (litHolds_pos pp6 2 3 4 (by simpa [hpp6] using hQSZ)) (litHolds_cons (litHolds_neg pp6 0 3 4 (by simpa [hpp6] using rz7)) (litHolds_nil pp6))))))
          simpa [hpp6] using h
        set pp7 : Fin 5 → Point := ![A, B, C, Q, Z] with hpp7
        have gg7 : IndexedGP pp7 := by
          have h := indexedGP_vec5 S hgp A B C Q Z mA mB mC mQ mZ neAB neAC neAQ neAZ neBC neBQ neBZ neCQ neCZ neQZ
          simpa [hpp7] using h
        have jRLCQX : 0 < orient C Q Z := by
          have h := sign_imp_pos [(0, 1, 3, false), (1, 2, 3, false), (0, 2, 3, false), (0, 3, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp7 gg7
            (litHolds_cons (litHolds_neg pp7 0 1 3 (by simpa [hpp7] using bABQ)) (litHolds_cons (litHolds_neg pp7 1 2 3 (by simpa [hpp7] using bBCQ)) (litHolds_cons (litHolds_neg pp7 0 2 3 (by simpa [hpp7] using bACQ)) (litHolds_cons (litHolds_neg pp7 0 3 4 (by simpa [hpp7] using rz6)) (litHolds_cons (litHolds_pos pp7 1 3 4 (by simpa [hpp7] using jRLBQX)) (litHolds_nil pp7))))))
          simpa [hpp7] using h
        have jRLX : 0 < orient A C Q := by
          have h := sign_imp_pos [(0, 3, 4, false), (0, 2, 4, true), (2, 3, 4, true)] 0 2 3 (by decide +kernel) pp7 gg7
            (litHolds_cons (litHolds_neg pp7 0 3 4 (by simpa [hpp7] using rz6)) (litHolds_cons (litHolds_pos pp7 0 2 4 (by simpa [hpp7] using jRLACX)) (litHolds_cons (litHolds_pos pp7 2 3 4 (by simpa [hpp7] using jRLCQX)) (litHolds_nil pp7))))
          simpa [hpp7] using h
        exfalso
        linarith
    · obtain ⟨lz1, lz2, lz3, lz4, lz5, lz6, lz7, lz8, lz9⟩ := hdz
      rcases hDigW with hdw | hdw
      · obtain ⟨rw1, rw2, rw3, rw4, rw5, rw6, rw7, rw8, rw9⟩ := hdw
        set pp8 : Fin 5 → Point := ![A, B, C, S3, Z] with hpp8
        have gg8 : IndexedGP pp8 := by
          have h := indexedGP_vec5 S hgp A B C S3 Z mA mB mC mS3 mZ neAB neAC neAS3 neAZ neBC neBS3 neBZ neCS3 neCZ neS3Z
          simpa [hpp8] using h
        have jLRACX : orient A C Z < 0 := by
          have h := sign_imp_neg [(0, 1, 2, true), (0, 2, 3, false), (2, 3, 4, false), (1, 2, 4, false), (1, 3, 4, true)] 0 2 4 (by decide +kernel) pp8 gg8
            (litHolds_cons (litHolds_pos pp8 0 1 2 (by simpa [hpp8] using bABC)) (litHolds_cons (litHolds_neg pp8 0 2 3 (by simpa [hpp8] using bACS)) (litHolds_cons (litHolds_neg pp8 2 3 4 (by simpa [hpp8] using hCSZ)) (litHolds_cons (litHolds_neg pp8 1 2 4 (by simpa [hpp8] using lz2)) (litHolds_cons (litHolds_pos pp8 1 3 4 (by simpa [hpp8] using lz6)) (litHolds_nil pp8))))))
          simpa [hpp8] using h
        set pp9 : Fin 5 → Point := ![A, B, C, D, Z] with hpp9
        have gg9 : IndexedGP pp9 := by
          have h := indexedGP_vec5 S hgp A B C D Z mA mB mC mD mZ neAB neAC neAD neAZ neBC neBD neBZ neCD neCZ neDZ
          simpa [hpp9] using h
        have jLRADX : orient A D Z < 0 := by
          have h := sign_imp_neg [(0, 2, 3, true), (2, 3, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp9 gg9
            (litHolds_cons (litHolds_pos pp9 0 2 3 (by simpa [hpp9] using bACD)) (litHolds_cons (litHolds_neg pp9 2 3 4 (by simpa [hpp9] using lz3)) (litHolds_cons (litHolds_neg pp9 0 2 4 (by simpa [hpp9] using jLRACX)) (litHolds_nil pp9))))
          simpa [hpp9] using h
        have jLRASX : 0 < orient A S3 Z := by
          have h := sign_imp_pos [(0, 1, 3, false), (2, 3, 4, false), (1, 2, 4, false), (1, 3, 4, true), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp8 gg8
            (litHolds_cons (litHolds_neg pp8 0 1 3 (by simpa [hpp8] using bABS)) (litHolds_cons (litHolds_neg pp8 2 3 4 (by simpa [hpp8] using hCSZ)) (litHolds_cons (litHolds_neg pp8 1 2 4 (by simpa [hpp8] using lz2)) (litHolds_cons (litHolds_pos pp8 1 3 4 (by simpa [hpp8] using lz6)) (litHolds_cons (litHolds_neg pp8 0 2 4 (by simpa [hpp8] using jLRACX)) (litHolds_nil pp8))))))
          simpa [hpp8] using h
        set pp10 : Fin 5 → Point := ![A, B, S3, Z, W] with hpp10
        have gg10 : IndexedGP pp10 := by
          have h := indexedGP_vec5 S hgp A B S3 Z W mA mB mS3 mZ mW neAB neAS3 neAZ neAW neBS3 neBZ neBW neS3Z neS3W neZW
          simpa [hpp10] using h
        have jLRAXY : orient A Z W < 0 := by
          have h := sign_imp_neg [(2, 3, 4, false), (0, 2, 4, false), (0, 2, 3, true)] 0 3 4 (by decide +kernel) pp10 gg10
            (litHolds_cons (litHolds_neg pp10 2 3 4 (by simpa [hpp10] using hSZW)) (litHolds_cons (litHolds_neg pp10 0 2 4 (by simpa [hpp10] using rw7)) (litHolds_cons (litHolds_pos pp10 0 2 3 (by simpa [hpp10] using jLRASX)) (litHolds_nil pp10))))
          simpa [hpp10] using h
        set pp11 : Fin 5 → Point := ![A, D, S3, Z, W] with hpp11
        have gg11 : IndexedGP pp11 := by
          have h := indexedGP_vec5 S hgp A D S3 Z W mA mD mS3 mZ mW neAD neAS3 neAZ neAW neDS3 neDZ neDW neS3Z neS3W neZW
          simpa [hpp11] using h
        have jLRDSX : 0 < orient D S3 Z := by
          have h := sign_imp_pos [(2, 3, 4, false), (0, 1, 4, true), (0, 1, 3, false), (0, 2, 3, true), (0, 3, 4, false)] 1 2 3 (by decide +kernel) pp11 gg11
            (litHolds_cons (litHolds_neg pp11 2 3 4 (by simpa [hpp11] using hSZW)) (litHolds_cons (litHolds_pos pp11 0 1 4 (by simpa [hpp11] using rw4)) (litHolds_cons (litHolds_neg pp11 0 1 3 (by simpa [hpp11] using jLRADX)) (litHolds_cons (litHolds_pos pp11 0 2 3 (by simpa [hpp11] using jLRASX)) (litHolds_cons (litHolds_neg pp11 0 3 4 (by simpa [hpp11] using jLRAXY)) (litHolds_nil pp11))))))
          simpa [hpp11] using h
        set pp12 : Fin 5 → Point := ![A, C, D, S3, Z] with hpp12
        have gg12 : IndexedGP pp12 := by
          have h := indexedGP_vec5 S hgp A C D S3 Z mA mC mD mS3 mZ neAC neAD neAS3 neAZ neCD neCS3 neCZ neDS3 neDZ neS3Z
          simpa [hpp12] using h
        have jLRX : 0 < orient C D Z := by
          have h := sign_imp_pos [(1, 3, 4, false), (0, 1, 4, false), (0, 2, 4, false), (0, 3, 4, true), (2, 3, 4, true)] 1 2 4 (by decide +kernel) pp12 gg12
            (litHolds_cons (litHolds_neg pp12 1 3 4 (by simpa [hpp12] using hCSZ)) (litHolds_cons (litHolds_neg pp12 0 1 4 (by simpa [hpp12] using jLRACX)) (litHolds_cons (litHolds_neg pp12 0 2 4 (by simpa [hpp12] using jLRADX)) (litHolds_cons (litHolds_pos pp12 0 3 4 (by simpa [hpp12] using jLRASX)) (litHolds_cons (litHolds_pos pp12 2 3 4 (by simpa [hpp12] using jLRDSX)) (litHolds_nil pp12))))))
          simpa [hpp12] using h
        exfalso
        linarith
      · obtain ⟨lw1, lw2, lw3, lw4, lw5, lw6, lw7, lw8, lw9⟩ := hdw
        rcases lt_or_gt_of_ne (hgp B mB Z mZ W mW neBZ neBW neZW) with hBZW | hBZW
        · -- the pentagon `B, Q, S3, W, Z`
          set pp13 : Fin 5 → Point := ![B, C, S3, Z, W] with hpp13
          have gg13 : IndexedGP pp13 := by
            have h := indexedGP_vec5 S hgp B C S3 Z W mB mC mS3 mZ mW neBC neBS3 neBZ neBW neCS3 neCZ neCW neS3Z neS3W neZW
            simpa [hpp13] using h
          have q3CXY : 0 < orient C Z W := by
            have h := sign_imp_pos [(2, 3, 4, false), (1, 2, 3, false), (0, 1, 3, false), (0, 2, 3, true), (0, 3, 4, false)] 1 3 4 (by decide +kernel) pp13 gg13
              (litHolds_cons (litHolds_neg pp13 2 3 4 (by simpa [hpp13] using hSZW)) (litHolds_cons (litHolds_neg pp13 1 2 3 (by simpa [hpp13] using hCSZ)) (litHolds_cons (litHolds_neg pp13 0 1 3 (by simpa [hpp13] using lz2)) (litHolds_cons (litHolds_pos pp13 0 2 3 (by simpa [hpp13] using lz6)) (litHolds_cons (litHolds_neg pp13 0 3 4 (by simpa [hpp13] using hBZW)) (litHolds_nil pp13))))))
            simpa [hpp13] using h
          set pp14 : Fin 5 → Point := ![B, C, D, Z, W] with hpp14
          have gg14 : IndexedGP pp14 := by
            have h := indexedGP_vec5 S hgp B C D Z W mB mC mD mZ mW neBC neBD neBZ neBW neCD neCZ neCW neDZ neDW neZW
            simpa [hpp14] using h
          have q3DXY : 0 < orient D Z W := by
            have h := sign_imp_pos [(0, 1, 4, false), (1, 2, 4, false), (0, 2, 4, false), (0, 3, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp14 gg14
              (litHolds_cons (litHolds_neg pp14 0 1 4 (by simpa [hpp14] using lw2)) (litHolds_cons (litHolds_neg pp14 1 2 4 (by simpa [hpp14] using lw3)) (litHolds_cons (litHolds_neg pp14 0 2 4 (by simpa [hpp14] using lw4)) (litHolds_cons (litHolds_neg pp14 0 3 4 (by simpa [hpp14] using hBZW)) (litHolds_cons (litHolds_pos pp14 1 3 4 (by simpa [hpp14] using q3CXY)) (litHolds_nil pp14))))))
            simpa [hpp14] using h
          set pp15 : Fin 5 → Point := ![B, Q, S3, Z, W] with hpp15
          have gg15 : IndexedGP pp15 := by
            have h := indexedGP_vec5 S hgp B Q S3 Z W mB mQ mS3 mZ mW neBQ neBS3 neBZ neBW neQS3 neQZ neQW neS3Z neS3W neZW
            simpa [hpp15] using h
          have q3QXY : orient Q Z W < 0 := by
            have h := sign_imp_neg [(1, 2, 4, true), (2, 3, 4, false), (0, 1, 4, true), (0, 2, 4, true), (0, 3, 4, false)] 1 3 4 (by decide +kernel) pp15 gg15
              (litHolds_cons (litHolds_pos pp15 1 2 4 (by simpa [hpp15] using hQSW)) (litHolds_cons (litHolds_neg pp15 2 3 4 (by simpa [hpp15] using hSZW)) (litHolds_cons (litHolds_pos pp15 0 1 4 (by simpa [hpp15] using lw5)) (litHolds_cons (litHolds_pos pp15 0 2 4 (by simpa [hpp15] using lw6)) (litHolds_cons (litHolds_neg pp15 0 3 4 (by simpa [hpp15] using hBZW)) (litHolds_nil pp15))))))
            simpa [hpp15] using h
          have q3c012 : 0 < orient B Q S3 := by
            have e : orient B Q S3 = orient B Q S3 := by unfold orient; ring
            linarith [bBQS]
          have q3c013 : 0 < orient B Q W := by
            have e : orient B Q W = orient B Q W := by unfold orient; ring
            linarith [lw5]
          have q3c014 : 0 < orient B Q Z := by
            have e : orient B Q Z = orient B Q Z := by unfold orient; ring
            linarith [lz5]
          have q3c023 : 0 < orient B S3 W := by
            have e : orient B S3 W = orient B S3 W := by unfold orient; ring
            linarith [lw6]
          have q3c024 : 0 < orient B S3 Z := by
            have e : orient B S3 Z = orient B S3 Z := by unfold orient; ring
            linarith [lz6]
          have q3c034 : 0 < orient B W Z := by
            have e : orient B W Z = -orient B Z W := by unfold orient; ring
            linarith [hBZW]
          have q3c123 : 0 < orient Q S3 W := by
            have e : orient Q S3 W = orient Q S3 W := by unfold orient; ring
            linarith [hQSW]
          have q3c124 : 0 < orient Q S3 Z := by
            have e : orient Q S3 Z = orient Q S3 Z := by unfold orient; ring
            linarith [hQSZ]
          have q3c134 : 0 < orient Q W Z := by
            have e : orient Q W Z = -orient Q Z W := by unfold orient; ring
            linarith [q3QXY]
          have q3c234 : 0 < orient S3 W Z := by
            have e : orient S3 W Z = -orient S3 Z W := by unfold orient; ring
            linarith [hSZW]
          have q3sA : orient B Q A < 0 := by
            have e : orient B Q A = orient A B Q := by unfold orient; ring
            linarith [bABQ]
          have q3sC : orient W Z C < 0 := by
            have e : orient W Z C = -orient C Z W := by unfold orient; ring
            linarith [q3CXY]
          have q3sD : orient W Z D < 0 := by
            have e : orient W Z D = -orient D Z W := by unfold orient; ring
            linarith [q3DXY]
          have q3sE : orient B Q E < 0 := by
            have e : orient B Q E = -orient B E Q := by unfold orient; ring
            linarith [bBEQ]
          have q3sM : orient B Q M < 0 := by
            have e : orient B Q M = -orient B M Q := by unfold orient; ring
            linarith [bBMQ]
          refine pent5_of_signs S B Q S3 W Z mB mQ mS3 mW mZ q3c012 q3c013 q3c014 q3c023 q3c024 q3c034 q3c123 q3c124 q3c134 q3c234 ?_
          intro q hq hq0 hq1 hq2 hq3 hq4
          rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl (le_of_lt q3sA)
          · exact absurd rfl hq0
          · exact Or.inr (Or.inr (Or.inr (Or.inl (le_of_lt q3sC))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (le_of_lt q3sD))))
          · exact Or.inl (le_of_lt q3sE)
          · exact Or.inl (le_of_lt q3sM)
          · exact absurd rfl hq1
          · exact absurd rfl hq2
          · exact absurd rfl hq4
          · exact absurd rfl hq3
        · -- `W` is angularly after `Z` from `B`
          rcases hRegZ with ⟨hrz, hdd⟩ | ⟨hrz, hdd⟩ | ⟨hrz, hdd⟩ | ⟨hrz, hdd⟩
          · obtain ⟨g1, g2, g3, g4, g5⟩ := id hrz
            have gc1 : orient B M Z < 0 := by
              have e : orient B M Z = -orient M B Z := by unfold orient; ring
              linarith [g1]
            have gc2 : 0 < orient C M Z := by
              have e : orient C M Z = -orient M C Z := by unfold orient; ring
              linarith [g2]
            rcases hRegW with ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩
            · obtain ⟨f1, f2, f3, f4, f5⟩ := id hrw
              have fc1 : orient B M W < 0 := by
                have e : orient B M W = -orient M B W := by unfold orient; ring
                linarith [f1]
              have fc2 : 0 < orient C M W := by
                have e : orient C M W = -orient M C W := by unfold orient; ring
                linarith [f2]
              rcases hsame1 hrz hrw with ⟨t1, t2⟩ | ⟨t1, t2⟩
              · exfalso
                have e : orient Z B W = -orient B Z W := by unfold orient; ring
                linarith
              · have t2' : orient C Z W < 0 := by
                  have e : orient C Z W = -orient C W Z := by unfold orient; ring
                  linarith
                set pp16 : Fin 5 → Point := ![A, B, C, D, Z] with hpp16
                have gg16 : IndexedGP pp16 := by
                  have h := indexedGP_vec5 S hgp A B C D Z mA mB mC mD mZ neAB neAC neAD neAZ neBC neBD neBZ neCD neCZ neDZ
                  simpa [hpp16] using h
                have q5ACX : orient A C Z < 0 := by
                  have h := sign_imp_neg [(0, 2, 3, true), (1, 2, 3, true), (1, 2, 4, false), (2, 3, 4, false), (0, 1, 4, false)] 0 2 4 (by decide +kernel) pp16 gg16
                    (litHolds_cons (litHolds_pos pp16 0 2 3 (by simpa [hpp16] using bACD)) (litHolds_cons (litHolds_pos pp16 1 2 3 (by simpa [hpp16] using bBCD)) (litHolds_cons (litHolds_neg pp16 1 2 4 (by simpa [hpp16] using g3)) (litHolds_cons (litHolds_neg pp16 2 3 4 (by simpa [hpp16] using g5)) (litHolds_cons (litHolds_neg pp16 0 1 4 (by simpa [hpp16] using g4)) (litHolds_nil pp16))))))
                  simpa [hpp16] using h
                set pp17 : Fin 5 → Point := ![A, B, C, D, W] with hpp17
                have gg17 : IndexedGP pp17 := by
                  have h := indexedGP_vec5 S hgp A B C D W mA mB mC mD mW neAB neAC neAD neAW neBC neBD neBW neCD neCW neDW
                  simpa [hpp17] using h
                have q5ACY : orient A C W < 0 := by
                  have h := sign_imp_neg [(0, 2, 3, true), (1, 2, 3, true), (1, 2, 4, false), (2, 3, 4, false), (0, 1, 4, false)] 0 2 4 (by decide +kernel) pp17 gg17
                    (litHolds_cons (litHolds_pos pp17 0 2 3 (by simpa [hpp17] using bACD)) (litHolds_cons (litHolds_pos pp17 1 2 3 (by simpa [hpp17] using bBCD)) (litHolds_cons (litHolds_neg pp17 1 2 4 (by simpa [hpp17] using f3)) (litHolds_cons (litHolds_neg pp17 2 3 4 (by simpa [hpp17] using f5)) (litHolds_cons (litHolds_neg pp17 0 1 4 (by simpa [hpp17] using f4)) (litHolds_nil pp17))))))
                  simpa [hpp17] using h
                have q5ADX : orient A D Z < 0 := by
                  have h := sign_imp_neg [(0, 2, 3, true), (2, 3, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp16 gg16
                    (litHolds_cons (litHolds_pos pp16 0 2 3 (by simpa [hpp16] using bACD)) (litHolds_cons (litHolds_neg pp16 2 3 4 (by simpa [hpp16] using g5)) (litHolds_cons (litHolds_neg pp16 0 2 4 (by simpa [hpp16] using q5ACX)) (litHolds_nil pp16))))
                  simpa [hpp16] using h
                have q5ADY : orient A D W < 0 := by
                  have h := sign_imp_neg [(0, 2, 3, true), (2, 3, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp17 gg17
                    (litHolds_cons (litHolds_pos pp17 0 2 3 (by simpa [hpp17] using bACD)) (litHolds_cons (litHolds_neg pp17 2 3 4 (by simpa [hpp17] using f5)) (litHolds_cons (litHolds_neg pp17 0 2 4 (by simpa [hpp17] using q5ACY)) (litHolds_nil pp17))))
                  simpa [hpp17] using h
                set pp18 : Fin 5 → Point := ![A, B, C, S3, Z] with hpp18
                have gg18 : IndexedGP pp18 := by
                  have h := indexedGP_vec5 S hgp A B C S3 Z mA mB mC mS3 mZ neAB neAC neAS3 neAZ neBC neBS3 neBZ neCS3 neCZ neS3Z
                  simpa [hpp18] using h
                have q5ASX : 0 < orient A S3 Z := by
                  have h := sign_imp_pos [(2, 3, 4, false), (1, 2, 4, false), (1, 3, 4, true), (0, 1, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp18 gg18
                    (litHolds_cons (litHolds_neg pp18 2 3 4 (by simpa [hpp18] using hCSZ)) (litHolds_cons (litHolds_neg pp18 1 2 4 (by simpa [hpp18] using g3)) (litHolds_cons (litHolds_pos pp18 1 3 4 (by simpa [hpp18] using lz6)) (litHolds_cons (litHolds_neg pp18 0 1 4 (by simpa [hpp18] using g4)) (litHolds_cons (litHolds_neg pp18 0 2 4 (by simpa [hpp18] using q5ACX)) (litHolds_nil pp18))))))
                  simpa [hpp18] using h
                set pp19 : Fin 5 → Point := ![A, C, S3, Z, W] with hpp19
                have gg19 : IndexedGP pp19 := by
                  have h := indexedGP_vec5 S hgp A C S3 Z W mA mC mS3 mZ mW neAC neAS3 neAZ neAW neCS3 neCZ neCW neS3Z neS3W neZW
                  simpa [hpp19] using h
                have q5ASY : 0 < orient A S3 W := by
                  have h := sign_imp_pos [(2, 3, 4, false), (1, 2, 3, false), (1, 3, 4, false), (0, 1, 3, false), (0, 2, 3, true)] 0 2 4 (by decide +kernel) pp19 gg19
                    (litHolds_cons (litHolds_neg pp19 2 3 4 (by simpa [hpp19] using hSZW)) (litHolds_cons (litHolds_neg pp19 1 2 3 (by simpa [hpp19] using hCSZ)) (litHolds_cons (litHolds_neg pp19 1 3 4 (by simpa [hpp19] using t2')) (litHolds_cons (litHolds_neg pp19 0 1 3 (by simpa [hpp19] using q5ACX)) (litHolds_cons (litHolds_pos pp19 0 2 3 (by simpa [hpp19] using q5ASX)) (litHolds_nil pp19))))))
                  simpa [hpp19] using h
                set pp20 : Fin 5 → Point := ![A, B, C, Z, W] with hpp20
                have gg20 : IndexedGP pp20 := by
                  have h := indexedGP_vec5 S hgp A B C Z W mA mB mC mZ mW neAB neAC neAZ neAW neBC neBZ neBW neCZ neCW neZW
                  simpa [hpp20] using h
                have q5AXY : 0 < orient A Z W := by
                  have h := sign_imp_pos [(1, 2, 4, false), (1, 3, 4, true), (0, 1, 4, false), (2, 3, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp20 gg20
                    (litHolds_cons (litHolds_neg pp20 1 2 4 (by simpa [hpp20] using f3)) (litHolds_cons (litHolds_pos pp20 1 3 4 (by simpa [hpp20] using hBZW)) (litHolds_cons (litHolds_neg pp20 0 1 4 (by simpa [hpp20] using f4)) (litHolds_cons (litHolds_neg pp20 2 3 4 (by simpa [hpp20] using t2')) (litHolds_cons (litHolds_neg pp20 0 2 4 (by simpa [hpp20] using q5ACY)) (litHolds_nil pp20))))))
                  simpa [hpp20] using h
                set pp21 : Fin 5 → Point := ![A, C, D, S3, Z] with hpp21
                have gg21 : IndexedGP pp21 := by
                  have h := indexedGP_vec5 S hgp A C D S3 Z mA mC mD mS3 mZ neAC neAD neAS3 neAZ neCD neCS3 neCZ neDS3 neDZ neS3Z
                  simpa [hpp21] using h
                have q5CDS : orient C D S3 < 0 := by
                  have h := sign_imp_neg [(0, 1, 2, true), (1, 3, 4, false), (1, 2, 4, false), (0, 1, 4, false), (0, 3, 4, true)] 1 2 3 (by decide +kernel) pp21 gg21
                    (litHolds_cons (litHolds_pos pp21 0 1 2 (by simpa [hpp21] using bACD)) (litHolds_cons (litHolds_neg pp21 1 3 4 (by simpa [hpp21] using hCSZ)) (litHolds_cons (litHolds_neg pp21 1 2 4 (by simpa [hpp21] using g5)) (litHolds_cons (litHolds_neg pp21 0 1 4 (by simpa [hpp21] using q5ACX)) (litHolds_cons (litHolds_pos pp21 0 3 4 (by simpa [hpp21] using q5ASX)) (litHolds_nil pp21))))))
                  simpa [hpp21] using h
                set pp22 : Fin 5 → Point := ![A, C, E, S3, Z] with hpp22
                have gg22 : IndexedGP pp22 := by
                  have h := indexedGP_vec5 S hgp A C E S3 Z mA mC mE mS3 mZ neAC neAE neAS3 neAZ neCE neCS3 neCZ neES3 neEZ neS3Z
                  simpa [hpp22] using h
                have q5CEX : 0 < orient C E Z := by
                  have h := sign_imp_pos [(0, 1, 2, true), (1, 2, 3, true), (1, 3, 4, false), (0, 1, 4, false), (0, 3, 4, true)] 1 2 4 (by decide +kernel) pp22 gg22
                    (litHolds_cons (litHolds_pos pp22 0 1 2 (by simpa [hpp22] using bACE)) (litHolds_cons (litHolds_pos pp22 1 2 3 (by simpa [hpp22] using bCES)) (litHolds_cons (litHolds_neg pp22 1 3 4 (by simpa [hpp22] using hCSZ)) (litHolds_cons (litHolds_neg pp22 0 1 4 (by simpa [hpp22] using q5ACX)) (litHolds_cons (litHolds_pos pp22 0 3 4 (by simpa [hpp22] using q5ASX)) (litHolds_nil pp22))))))
                  simpa [hpp22] using h
                set pp23 : Fin 5 → Point := ![A, C, E, Z, W] with hpp23
                have gg23 : IndexedGP pp23 := by
                  have h := indexedGP_vec5 S hgp A C E Z W mA mC mE mZ mW neAC neAE neAZ neAW neCE neCZ neCW neEZ neEW neZW
                  simpa [hpp23] using h
                have q5CEY : 0 < orient C E W := by
                  have h := sign_imp_pos [(0, 1, 2, true), (1, 3, 4, false), (0, 1, 4, false), (0, 3, 4, true), (1, 2, 3, true)] 1 2 4 (by decide +kernel) pp23 gg23
                    (litHolds_cons (litHolds_pos pp23 0 1 2 (by simpa [hpp23] using bACE)) (litHolds_cons (litHolds_neg pp23 1 3 4 (by simpa [hpp23] using t2')) (litHolds_cons (litHolds_neg pp23 0 1 4 (by simpa [hpp23] using q5ACY)) (litHolds_cons (litHolds_pos pp23 0 3 4 (by simpa [hpp23] using q5AXY)) (litHolds_cons (litHolds_pos pp23 1 2 3 (by simpa [hpp23] using q5CEX)) (litHolds_nil pp23))))))
                  simpa [hpp23] using h
                have q5CSY : orient C S3 W < 0 := by
                  have h := sign_imp_neg [(1, 2, 3, false), (1, 3, 4, false), (0, 1, 4, false), (0, 2, 4, true), (0, 3, 4, true)] 1 2 4 (by decide +kernel) pp19 gg19
                    (litHolds_cons (litHolds_neg pp19 1 2 3 (by simpa [hpp19] using hCSZ)) (litHolds_cons (litHolds_neg pp19 1 3 4 (by simpa [hpp19] using t2')) (litHolds_cons (litHolds_neg pp19 0 1 4 (by simpa [hpp19] using q5ACY)) (litHolds_cons (litHolds_pos pp19 0 2 4 (by simpa [hpp19] using q5ASY)) (litHolds_cons (litHolds_pos pp19 0 3 4 (by simpa [hpp19] using q5AXY)) (litHolds_nil pp19))))))
                  simpa [hpp19] using h
                have q5DSX : orient D S3 Z < 0 := by
                  have h := sign_imp_neg [(1, 3, 4, false), (0, 1, 4, false), (0, 2, 4, false), (0, 3, 4, true), (1, 2, 3, false)] 2 3 4 (by decide +kernel) pp21 gg21
                    (litHolds_cons (litHolds_neg pp21 1 3 4 (by simpa [hpp21] using hCSZ)) (litHolds_cons (litHolds_neg pp21 0 1 4 (by simpa [hpp21] using q5ACX)) (litHolds_cons (litHolds_neg pp21 0 2 4 (by simpa [hpp21] using q5ADX)) (litHolds_cons (litHolds_pos pp21 0 3 4 (by simpa [hpp21] using q5ASX)) (litHolds_cons (litHolds_neg pp21 1 2 3 (by simpa [hpp21] using q5CDS)) (litHolds_nil pp21))))))
                  simpa [hpp21] using h
                set pp24 : Fin 5 → Point := ![A, C, D, S3, W] with hpp24
                have gg24 : IndexedGP pp24 := by
                  have h := indexedGP_vec5 S hgp A C D S3 W mA mC mD mS3 mW neAC neAD neAS3 neAW neCD neCS3 neCW neDS3 neDW neS3W
                  simpa [hpp24] using h
                have q5DSY : orient D S3 W < 0 := by
                  have h := sign_imp_neg [(0, 1, 4, false), (0, 2, 4, false), (0, 3, 4, true), (1, 2, 3, false), (1, 3, 4, false)] 2 3 4 (by decide +kernel) pp24 gg24
                    (litHolds_cons (litHolds_neg pp24 0 1 4 (by simpa [hpp24] using q5ACY)) (litHolds_cons (litHolds_neg pp24 0 2 4 (by simpa [hpp24] using q5ADY)) (litHolds_cons (litHolds_pos pp24 0 3 4 (by simpa [hpp24] using q5ASY)) (litHolds_cons (litHolds_neg pp24 1 2 3 (by simpa [hpp24] using q5CDS)) (litHolds_cons (litHolds_neg pp24 1 3 4 (by simpa [hpp24] using q5CSY)) (litHolds_nil pp24))))))
                  simpa [hpp24] using h
                set pp25 : Fin 5 → Point := ![A, C, D, Z, W] with hpp25
                have gg25 : IndexedGP pp25 := by
                  have h := indexedGP_vec5 S hgp A C D Z W mA mC mD mZ mW neAC neAD neAZ neAW neCD neCZ neCW neDZ neDW neZW
                  simpa [hpp25] using h
                have q5DXY : orient D Z W < 0 := by
                  have h := sign_imp_neg [(1, 2, 4, false), (1, 3, 4, false), (0, 1, 4, false), (0, 2, 4, false), (0, 3, 4, true)] 2 3 4 (by decide +kernel) pp25 gg25
                    (litHolds_cons (litHolds_neg pp25 1 2 4 (by simpa [hpp25] using f5)) (litHolds_cons (litHolds_neg pp25 1 3 4 (by simpa [hpp25] using t2')) (litHolds_cons (litHolds_neg pp25 0 1 4 (by simpa [hpp25] using q5ACY)) (litHolds_cons (litHolds_neg pp25 0 2 4 (by simpa [hpp25] using q5ADY)) (litHolds_cons (litHolds_pos pp25 0 3 4 (by simpa [hpp25] using q5AXY)) (litHolds_nil pp25))))))
                  simpa [hpp25] using h
                have q5c012 : 0 < orient C W Z := by
                  have e : orient C W Z = -orient C Z W := by unfold orient; ring
                  linarith [t2']
                have q5c013 : 0 < orient C W S3 := by
                  have e : orient C W S3 = -orient C S3 W := by unfold orient; ring
                  linarith [q5CSY]
                have q5c014 : 0 < orient C W D := by
                  have e : orient C W D = -orient C D W := by unfold orient; ring
                  linarith [f5]
                have q5c023 : 0 < orient C Z S3 := by
                  have e : orient C Z S3 = -orient C S3 Z := by unfold orient; ring
                  linarith [hCSZ]
                have q5c024 : 0 < orient C Z D := by
                  have e : orient C Z D = -orient C D Z := by unfold orient; ring
                  linarith [g5]
                have q5c034 : 0 < orient C S3 D := by
                  have e : orient C S3 D = -orient C D S3 := by unfold orient; ring
                  linarith [q5CDS]
                have q5c123 : 0 < orient W Z S3 := by
                  have e : orient W Z S3 = -orient S3 Z W := by unfold orient; ring
                  linarith [hSZW]
                have q5c124 : 0 < orient W Z D := by
                  have e : orient W Z D = -orient D Z W := by unfold orient; ring
                  linarith [q5DXY]
                have q5c134 : 0 < orient W S3 D := by
                  have e : orient W S3 D = -orient D S3 W := by unfold orient; ring
                  linarith [q5DSY]
                have q5c234 : 0 < orient Z S3 D := by
                  have e : orient Z S3 D = -orient D S3 Z := by unfold orient; ring
                  linarith [q5DSX]
                have q5sA : orient C W A < 0 := by
                  have e : orient C W A = orient A C W := by unfold orient; ring
                  linarith [q5ACY]
                have q5sB : orient C W B < 0 := by
                  have e : orient C W B = orient B C W := by unfold orient; ring
                  linarith [f3]
                have q5sE : orient C W E < 0 := by
                  have e : orient C W E = -orient C E W := by unfold orient; ring
                  linarith [q5CEY]
                have q5sM : orient C W M < 0 := by
                  have e : orient C W M = -orient C M W := by unfold orient; ring
                  linarith [fc2]
                have q5sQ : orient Z S3 Q < 0 := by
                  have e : orient Z S3 Q = -orient Q S3 Z := by unfold orient; ring
                  linarith [hQSZ]
                refine pent5_of_signs S C W Z S3 D mC mW mZ mS3 mD q5c012 q5c013 q5c014 q5c023 q5c024 q5c034 q5c123 q5c124 q5c134 q5c234 ?_
                intro q hq hq0 hq1 hq2 hq3 hq4
                rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
                · exact Or.inl (le_of_lt q5sA)
                · exact Or.inl (le_of_lt q5sB)
                · exact absurd rfl hq0
                · exact absurd rfl hq4
                · exact Or.inl (le_of_lt q5sE)
                · exact Or.inl (le_of_lt q5sM)
                · exact Or.inr (Or.inr (Or.inl (le_of_lt q5sQ)))
                · exact absurd rfl hq3
                · exact absurd rfl hq2
                · exact absurd rfl hq1
            · obtain ⟨f1, f2, f3, f4, f5⟩ := id hrw
              have fc1 : orient C M W < 0 := by
                have e : orient C M W = -orient M C W := by unfold orient; ring
                linarith [f1]
              have fc2 : 0 < orient D M W := by
                have e : orient D M W = -orient M D W := by unfold orient; ring
                linarith [f2]
              set pp26 : Fin 5 → Point := ![A, B, C, D, Z] with hpp26
              have gg26 : IndexedGP pp26 := by
                have h := indexedGP_vec5 S hgp A B C D Z mA mB mC mD mZ neAB neAC neAD neAZ neBC neBD neBZ neCD neCZ neDZ
                simpa [hpp26] using h
              have q4ACX : orient A C Z < 0 := by
                have h := sign_imp_neg [(0, 2, 3, true), (1, 2, 3, true), (1, 2, 4, false), (2, 3, 4, false), (0, 1, 4, false)] 0 2 4 (by decide +kernel) pp26 gg26
                  (litHolds_cons (litHolds_pos pp26 0 2 3 (by simpa [hpp26] using bACD)) (litHolds_cons (litHolds_pos pp26 1 2 3 (by simpa [hpp26] using bBCD)) (litHolds_cons (litHolds_neg pp26 1 2 4 (by simpa [hpp26] using g3)) (litHolds_cons (litHolds_neg pp26 2 3 4 (by simpa [hpp26] using g5)) (litHolds_cons (litHolds_neg pp26 0 1 4 (by simpa [hpp26] using g4)) (litHolds_nil pp26))))))
                simpa [hpp26] using h
              have q4ADX : orient A D Z < 0 := by
                have h := sign_imp_neg [(0, 2, 3, true), (2, 3, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp26 gg26
                  (litHolds_cons (litHolds_pos pp26 0 2 3 (by simpa [hpp26] using bACD)) (litHolds_cons (litHolds_neg pp26 2 3 4 (by simpa [hpp26] using g5)) (litHolds_cons (litHolds_neg pp26 0 2 4 (by simpa [hpp26] using q4ACX)) (litHolds_nil pp26))))
                simpa [hpp26] using h
              set pp27 : Fin 5 → Point := ![A, B, C, S3, Z] with hpp27
              have gg27 : IndexedGP pp27 := by
                have h := indexedGP_vec5 S hgp A B C S3 Z mA mB mC mS3 mZ neAB neAC neAS3 neAZ neBC neBS3 neBZ neCS3 neCZ neS3Z
                simpa [hpp27] using h
              have q4ASX : 0 < orient A S3 Z := by
                have h := sign_imp_pos [(2, 3, 4, false), (1, 2, 4, false), (1, 3, 4, true), (0, 1, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp27 gg27
                  (litHolds_cons (litHolds_neg pp27 2 3 4 (by simpa [hpp27] using hCSZ)) (litHolds_cons (litHolds_neg pp27 1 2 4 (by simpa [hpp27] using g3)) (litHolds_cons (litHolds_pos pp27 1 3 4 (by simpa [hpp27] using lz6)) (litHolds_cons (litHolds_neg pp27 0 1 4 (by simpa [hpp27] using g4)) (litHolds_cons (litHolds_neg pp27 0 2 4 (by simpa [hpp27] using q4ACX)) (litHolds_nil pp27))))))
                simpa [hpp27] using h
              set pp28 : Fin 5 → Point := ![A, B, D, E, W] with hpp28
              have gg28 : IndexedGP pp28 := by
                have h := indexedGP_vec5 S hgp A B D E W mA mB mD mE mW neAB neAD neAE neAW neBD neBE neBW neDE neDW neEW
                simpa [hpp28] using h
              have q4BEY : orient B E W < 0 := by
                have h := sign_imp_neg [(1, 2, 3, true), (1, 2, 4, false), (2, 3, 4, false)] 1 3 4 (by decide +kernel) pp28 gg28
                  (litHolds_cons (litHolds_pos pp28 1 2 3 (by simpa [hpp28] using bBDE)) (litHolds_cons (litHolds_neg pp28 1 2 4 (by simpa [hpp28] using lw4)) (litHolds_cons (litHolds_neg pp28 2 3 4 (by simpa [hpp28] using f5)) (litHolds_nil pp28))))
                simpa [hpp28] using h
              set pp29 : Fin 5 → Point := ![A, C, D, S3, Z] with hpp29
              have gg29 : IndexedGP pp29 := by
                have h := indexedGP_vec5 S hgp A C D S3 Z mA mC mD mS3 mZ neAC neAD neAS3 neAZ neCD neCS3 neCZ neDS3 neDZ neS3Z
                simpa [hpp29] using h
              have q4CDS : orient C D S3 < 0 := by
                have h := sign_imp_neg [(0, 1, 2, true), (1, 3, 4, false), (1, 2, 4, false), (0, 1, 4, false), (0, 3, 4, true)] 1 2 3 (by decide +kernel) pp29 gg29
                  (litHolds_cons (litHolds_pos pp29 0 1 2 (by simpa [hpp29] using bACD)) (litHolds_cons (litHolds_neg pp29 1 3 4 (by simpa [hpp29] using hCSZ)) (litHolds_cons (litHolds_neg pp29 1 2 4 (by simpa [hpp29] using g5)) (litHolds_cons (litHolds_neg pp29 0 1 4 (by simpa [hpp29] using q4ACX)) (litHolds_cons (litHolds_pos pp29 0 3 4 (by simpa [hpp29] using q4ASX)) (litHolds_nil pp29))))))
                simpa [hpp29] using h
              set pp30 : Fin 5 → Point := ![A, C, E, S3, Z] with hpp30
              have gg30 : IndexedGP pp30 := by
                have h := indexedGP_vec5 S hgp A C E S3 Z mA mC mE mS3 mZ neAC neAE neAS3 neAZ neCE neCS3 neCZ neES3 neEZ neS3Z
                simpa [hpp30] using h
              have q4CEX : 0 < orient C E Z := by
                have h := sign_imp_pos [(0, 1, 2, true), (1, 2, 3, true), (1, 3, 4, false), (0, 1, 4, false), (0, 3, 4, true)] 1 2 4 (by decide +kernel) pp30 gg30
                  (litHolds_cons (litHolds_pos pp30 0 1 2 (by simpa [hpp30] using bACE)) (litHolds_cons (litHolds_pos pp30 1 2 3 (by simpa [hpp30] using bCES)) (litHolds_cons (litHolds_neg pp30 1 3 4 (by simpa [hpp30] using hCSZ)) (litHolds_cons (litHolds_neg pp30 0 1 4 (by simpa [hpp30] using q4ACX)) (litHolds_cons (litHolds_pos pp30 0 3 4 (by simpa [hpp30] using q4ASX)) (litHolds_nil pp30))))))
                simpa [hpp30] using h
              set pp31 : Fin 5 → Point := ![A, C, D, E, W] with hpp31
              have gg31 : IndexedGP pp31 := by
                have h := indexedGP_vec5 S hgp A C D E W mA mC mD mE mW neAC neAD neAE neAW neCD neCE neCW neDE neDW neEW
                simpa [hpp31] using h
              have q4CEY : orient C E W < 0 := by
                have h := sign_imp_neg [(1, 2, 3, true), (1, 2, 4, false), (2, 3, 4, false)] 1 3 4 (by decide +kernel) pp31 gg31
                  (litHolds_cons (litHolds_pos pp31 1 2 3 (by simpa [hpp31] using bCDE)) (litHolds_cons (litHolds_neg pp31 1 2 4 (by simpa [hpp31] using f3)) (litHolds_cons (litHolds_neg pp31 2 3 4 (by simpa [hpp31] using f5)) (litHolds_nil pp31))))
                simpa [hpp31] using h
              set pp32 : Fin 5 → Point := ![B, C, E, S3, W] with hpp32
              have gg32 : IndexedGP pp32 := by
                have h := indexedGP_vec5 S hgp B C E S3 W mB mC mE mS3 mW neBC neBE neBS3 neBW neCE neCS3 neCW neES3 neEW neS3W
                simpa [hpp32] using h
              have q4CSY : 0 < orient C S3 W := by
                have h := sign_imp_pos [(0, 2, 3, true), (0, 1, 4, false), (0, 3, 4, true), (0, 2, 4, false), (1, 2, 4, false)] 1 3 4 (by decide +kernel) pp32 gg32
                  (litHolds_cons (litHolds_pos pp32 0 2 3 (by simpa [hpp32] using bBES)) (litHolds_cons (litHolds_neg pp32 0 1 4 (by simpa [hpp32] using f4)) (litHolds_cons (litHolds_pos pp32 0 3 4 (by simpa [hpp32] using lw6)) (litHolds_cons (litHolds_neg pp32 0 2 4 (by simpa [hpp32] using q4BEY)) (litHolds_cons (litHolds_neg pp32 1 2 4 (by simpa [hpp32] using q4CEY)) (litHolds_nil pp32))))))
                simpa [hpp32] using h
              set pp33 : Fin 5 → Point := ![B, C, E, Z, W] with hpp33
              have gg33 : IndexedGP pp33 := by
                have h := indexedGP_vec5 S hgp B C E Z W mB mC mE mZ mW neBC neBE neBZ neBW neCE neCZ neCW neEZ neEW neZW
                simpa [hpp33] using h
              have q4CXY : 0 < orient C Z W := by
                have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 4, false), (0, 3, 4, true), (1, 2, 3, true), (1, 2, 4, false)] 1 3 4 (by decide +kernel) pp33 gg33
                  (litHolds_cons (litHolds_pos pp33 0 1 2 (by simpa [hpp33] using bBCE)) (litHolds_cons (litHolds_neg pp33 0 1 4 (by simpa [hpp33] using f4)) (litHolds_cons (litHolds_pos pp33 0 3 4 (by simpa [hpp33] using hBZW)) (litHolds_cons (litHolds_pos pp33 1 2 3 (by simpa [hpp33] using q4CEX)) (litHolds_cons (litHolds_neg pp33 1 2 4 (by simpa [hpp33] using q4CEY)) (litHolds_nil pp33))))))
                simpa [hpp33] using h
              set pp34 : Fin 5 → Point := ![A, C, D, E, Z] with hpp34
              have gg34 : IndexedGP pp34 := by
                have h := indexedGP_vec5 S hgp A C D E Z mA mC mD mE mZ neAC neAD neAE neAZ neCD neCE neCZ neDE neDZ neEZ
                simpa [hpp34] using h
              have q4DEX : 0 < orient D E Z := by
                have h := sign_imp_pos [(1, 2, 3, true), (1, 2, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp34 gg34
                  (litHolds_cons (litHolds_pos pp34 1 2 3 (by simpa [hpp34] using bCDE)) (litHolds_cons (litHolds_neg pp34 1 2 4 (by simpa [hpp34] using g5)) (litHolds_cons (litHolds_pos pp34 1 3 4 (by simpa [hpp34] using q4CEX)) (litHolds_nil pp34))))
                simpa [hpp34] using h
              have q4DSX : orient D S3 Z < 0 := by
                have h := sign_imp_neg [(1, 3, 4, false), (0, 1, 4, false), (0, 2, 4, false), (0, 3, 4, true), (1, 2, 3, false)] 2 3 4 (by decide +kernel) pp29 gg29
                  (litHolds_cons (litHolds_neg pp29 1 3 4 (by simpa [hpp29] using hCSZ)) (litHolds_cons (litHolds_neg pp29 0 1 4 (by simpa [hpp29] using q4ACX)) (litHolds_cons (litHolds_neg pp29 0 2 4 (by simpa [hpp29] using q4ADX)) (litHolds_cons (litHolds_pos pp29 0 3 4 (by simpa [hpp29] using q4ASX)) (litHolds_cons (litHolds_neg pp29 1 2 3 (by simpa [hpp29] using q4CDS)) (litHolds_nil pp29))))))
                simpa [hpp29] using h
              set pp35 : Fin 5 → Point := ![B, D, E, S3, W] with hpp35
              have gg35 : IndexedGP pp35 := by
                have h := indexedGP_vec5 S hgp B D E S3 W mB mD mE mS3 mW neBD neBE neBS3 neBW neDE neDS3 neDW neES3 neEW neS3W
                simpa [hpp35] using h
              have q4DSY : 0 < orient D S3 W := by
                have h := sign_imp_pos [(0, 2, 3, true), (0, 1, 4, false), (0, 3, 4, true), (1, 2, 4, false), (0, 2, 4, false)] 1 3 4 (by decide +kernel) pp35 gg35
                  (litHolds_cons (litHolds_pos pp35 0 2 3 (by simpa [hpp35] using bBES)) (litHolds_cons (litHolds_neg pp35 0 1 4 (by simpa [hpp35] using lw4)) (litHolds_cons (litHolds_pos pp35 0 3 4 (by simpa [hpp35] using lw6)) (litHolds_cons (litHolds_neg pp35 1 2 4 (by simpa [hpp35] using f5)) (litHolds_cons (litHolds_neg pp35 0 2 4 (by simpa [hpp35] using q4BEY)) (litHolds_nil pp35))))))
                simpa [hpp35] using h
              set pp36 : Fin 5 → Point := ![B, D, E, Z, W] with hpp36
              have gg36 : IndexedGP pp36 := by
                have h := indexedGP_vec5 S hgp B D E Z W mB mD mE mZ mW neBD neBE neBZ neBW neDE neDZ neDW neEZ neEW neZW
                simpa [hpp36] using h
              have q4DXY : 0 < orient D Z W := by
                have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 4, false), (0, 3, 4, true), (1, 2, 4, false), (1, 2, 3, true)] 1 3 4 (by decide +kernel) pp36 gg36
                  (litHolds_cons (litHolds_pos pp36 0 1 2 (by simpa [hpp36] using bBDE)) (litHolds_cons (litHolds_neg pp36 0 1 4 (by simpa [hpp36] using lw4)) (litHolds_cons (litHolds_pos pp36 0 3 4 (by simpa [hpp36] using hBZW)) (litHolds_cons (litHolds_neg pp36 1 2 4 (by simpa [hpp36] using f5)) (litHolds_cons (litHolds_pos pp36 1 2 3 (by simpa [hpp36] using q4DEX)) (litHolds_nil pp36))))))
                simpa [hpp36] using h
              have q4c012 : 0 < orient C Z S3 := by
                have e : orient C Z S3 = -orient C S3 Z := by unfold orient; ring
                linarith [hCSZ]
              have q4c013 : 0 < orient C Z W := by
                have e : orient C Z W = orient C Z W := by unfold orient; ring
                linarith [q4CXY]
              have q4c014 : 0 < orient C Z D := by
                have e : orient C Z D = -orient C D Z := by unfold orient; ring
                linarith [g5]
              have q4c023 : 0 < orient C S3 W := by
                have e : orient C S3 W = orient C S3 W := by unfold orient; ring
                linarith [q4CSY]
              have q4c024 : 0 < orient C S3 D := by
                have e : orient C S3 D = -orient C D S3 := by unfold orient; ring
                linarith [q4CDS]
              have q4c034 : 0 < orient C W D := by
                have e : orient C W D = -orient C D W := by unfold orient; ring
                linarith [f3]
              have q4c123 : 0 < orient Z S3 W := by
                have e : orient Z S3 W = -orient S3 Z W := by unfold orient; ring
                linarith [hSZW]
              have q4c124 : 0 < orient Z S3 D := by
                have e : orient Z S3 D = -orient D S3 Z := by unfold orient; ring
                linarith [q4DSX]
              have q4c134 : 0 < orient Z W D := by
                have e : orient Z W D = orient D Z W := by unfold orient; ring
                linarith [q4DXY]
              have q4c234 : 0 < orient S3 W D := by
                have e : orient S3 W D = orient D S3 W := by unfold orient; ring
                linarith [q4DSY]
              have q4sA : orient C Z A < 0 := by
                have e : orient C Z A = orient A C Z := by unfold orient; ring
                linarith [q4ACX]
              have q4sB : orient C Z B < 0 := by
                have e : orient C Z B = orient B C Z := by unfold orient; ring
                linarith [g3]
              have q4sE : orient C Z E < 0 := by
                have e : orient C Z E = -orient C E Z := by unfold orient; ring
                linarith [q4CEX]
              have q4sM : orient C Z M < 0 := by
                have e : orient C Z M = -orient C M Z := by unfold orient; ring
                linarith [gc2]
              have q4sQ : orient Z S3 Q < 0 := by
                have e : orient Z S3 Q = -orient Q S3 Z := by unfold orient; ring
                linarith [hQSZ]
              refine pent5_of_signs S C Z S3 W D mC mZ mS3 mW mD q4c012 q4c013 q4c014 q4c023 q4c024 q4c034 q4c123 q4c124 q4c134 q4c234 ?_
              intro q hq hq0 hq1 hq2 hq3 hq4
              rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              · exact Or.inl (le_of_lt q4sA)
              · exact Or.inl (le_of_lt q4sB)
              · exact absurd rfl hq0
              · exact absurd rfl hq4
              · exact Or.inl (le_of_lt q4sE)
              · exact Or.inl (le_of_lt q4sM)
              · exact Or.inr (Or.inl (le_of_lt q4sQ))
              · exact absurd rfl hq2
              · exact absurd rfl hq1
              · exact absurd rfl hq3
            · exfalso
              obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
              linarith
            · exfalso
              obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
              linarith
          · obtain ⟨g1, g2, g3, g4, g5⟩ := id hrz
            have gc1 : orient C M Z < 0 := by
              have e : orient C M Z = -orient M C Z := by unfold orient; ring
              linarith [g1]
            have gc2 : 0 < orient D M Z := by
              have e : orient D M Z = -orient M D Z := by unfold orient; ring
              linarith [g2]
            rcases hRegW with ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩ | ⟨hrw, hdd⟩
            · obtain ⟨f1, f2, f3, f4, f5⟩ := id hrw
              have fc1 : orient B M W < 0 := by
                have e : orient B M W = -orient M B W := by unfold orient; ring
                linarith [f1]
              have fc2 : 0 < orient C M W := by
                have e : orient C M W = -orient M C W := by unfold orient; ring
                linarith [f2]
              set pp37 : Fin 5 → Point := ![A, B, C, Z, W] with hpp37
              have gg37 : IndexedGP pp37 := by
                have h := indexedGP_vec5 S hgp A B C Z W mA mB mC mZ mW neAB neAC neAZ neAW neBC neBZ neBW neCZ neCW neZW
                simpa [hpp37] using h
              have r21ABX : orient A B Z < 0 := by
                have h := sign_imp_neg [(0, 1, 2, true), (1, 2, 3, false), (1, 2, 4, false), (1, 3, 4, true), (0, 1, 4, false)] 0 1 3 (by decide +kernel) pp37 gg37
                  (litHolds_cons (litHolds_pos pp37 0 1 2 (by simpa [hpp37] using bABC)) (litHolds_cons (litHolds_neg pp37 1 2 3 (by simpa [hpp37] using g4)) (litHolds_cons (litHolds_neg pp37 1 2 4 (by simpa [hpp37] using f3)) (litHolds_cons (litHolds_pos pp37 1 3 4 (by simpa [hpp37] using hBZW)) (litHolds_cons (litHolds_neg pp37 0 1 4 (by simpa [hpp37] using f4)) (litHolds_nil pp37))))))
                simpa [hpp37] using h
              set pp38 : Fin 5 → Point := ![A, C, M, S3, Z] with hpp38
              have gg38 : IndexedGP pp38 := by
                have h := indexedGP_vec5 S hgp A C M S3 Z mA mC mM mS3 mZ neAC neAM neAS3 neAZ neCM neCS3 neCZ neMS3 neMZ neS3Z
                simpa [hpp38] using h
              have r21ACX : 0 < orient A C Z := by
                have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (1, 2, 3, true), (1, 3, 4, false), (1, 2, 4, false)] 0 1 4 (by decide +kernel) pp38 gg38
                  (litHolds_cons (litHolds_pos pp38 0 1 2 (by simpa [hpp38] using bACM)) (litHolds_cons (litHolds_neg pp38 0 1 3 (by simpa [hpp38] using bACS)) (litHolds_cons (litHolds_pos pp38 1 2 3 (by simpa [hpp38] using bCMS)) (litHolds_cons (litHolds_neg pp38 1 3 4 (by simpa [hpp38] using hCSZ)) (litHolds_cons (litHolds_neg pp38 1 2 4 (by simpa [hpp38] using gc1)) (litHolds_nil pp38))))))
                simpa [hpp38] using h
              set pp39 : Fin 5 → Point := ![A, B, C, S3, Z] with hpp39
              have gg39 : IndexedGP pp39 := by
                have h := indexedGP_vec5 S hgp A B C S3 Z mA mB mC mS3 mZ neAB neAC neAS3 neAZ neBC neBS3 neBZ neCS3 neCZ neS3Z
                simpa [hpp39] using h
              have r21X : 0 < orient A B S3 := by
                have h := sign_imp_pos [(0, 1, 2, true), (1, 2, 4, false), (0, 1, 4, false), (0, 2, 4, true)] 0 1 3 (by decide +kernel) pp39 gg39
                  (litHolds_cons (litHolds_pos pp39 0 1 2 (by simpa [hpp39] using bABC)) (litHolds_cons (litHolds_neg pp39 1 2 4 (by simpa [hpp39] using g4)) (litHolds_cons (litHolds_neg pp39 0 1 4 (by simpa [hpp39] using r21ABX)) (litHolds_cons (litHolds_pos pp39 0 2 4 (by simpa [hpp39] using r21ACX)) (litHolds_nil pp39)))))
                simpa [hpp39] using h
              exfalso
              linarith
            · obtain ⟨f1, f2, f3, f4, f5⟩ := id hrw
              have fc1 : orient C M W < 0 := by
                have e : orient C M W = -orient M C W := by unfold orient; ring
                linarith [f1]
              have fc2 : 0 < orient D M W := by
                have e : orient D M W = -orient M D W := by unfold orient; ring
                linarith [f2]
              set pp40 : Fin 5 → Point := ![B, C, M, S3, Z] with hpp40
              have gg40 : IndexedGP pp40 := by
                have h := indexedGP_vec5 S hgp B C M S3 Z mB mC mM mS3 mZ neBC neBM neBS3 neBZ neCM neCS3 neCZ neMS3 neMZ neS3Z
                simpa [hpp40] using h
              have r22X : orient B M S3 < 0 := by
                have h := sign_imp_neg [(1, 3, 4, false), (0, 2, 4, false), (0, 1, 4, false), (0, 3, 4, true), (1, 2, 4, false)] 0 2 3 (by decide +kernel) pp40 gg40
                  (litHolds_cons (litHolds_neg pp40 1 3 4 (by simpa [hpp40] using hCSZ)) (litHolds_cons (litHolds_neg pp40 0 2 4 (by simpa [hpp40] using lz1)) (litHolds_cons (litHolds_neg pp40 0 1 4 (by simpa [hpp40] using g4)) (litHolds_cons (litHolds_pos pp40 0 3 4 (by simpa [hpp40] using lz6)) (litHolds_cons (litHolds_neg pp40 1 2 4 (by simpa [hpp40] using gc1)) (litHolds_nil pp40))))))
                simpa [hpp40] using h
              exfalso
              linarith
            · exfalso
              obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
              linarith
            · exfalso
              obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
              linarith
          · exfalso
            obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
            linarith
          · exfalso
            obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hdd
            linarith
  · -- `Z` is outside the quadrilateral `B, Q, S3, C`: pentagon `B, Q, S3, Z, C`
    have hBCZ : orient B C Z < 0 := by
      rcases hDigZ with hd | hd
      · obtain ⟨rz1, rz2, rz3, rz4, rz5, rz6, rz7, rz8, rz9⟩ := hd
        set pp41 : Fin 5 → Point := ![A, B, C, S3, Z] with hpp41
        have gg41 : IndexedGP pp41 := by
          have h := indexedGP_vec5 S hgp A B C S3 Z mA mB mC mS3 mZ neAB neAC neAS3 neAZ neBC neBS3 neBZ neCS3 neCZ neS3Z
          simpa [hpp41] using h
        have vACX : orient A C Z < 0 := by
          have h := sign_imp_neg [(0, 2, 3, false), (0, 3, 4, false), (2, 3, 4, true)] 0 2 4 (by decide +kernel) pp41 gg41
            (litHolds_cons (litHolds_neg pp41 0 2 3 (by simpa [hpp41] using bACS)) (litHolds_cons (litHolds_neg pp41 0 3 4 (by simpa [hpp41] using rz7)) (litHolds_cons (litHolds_pos pp41 2 3 4 (by simpa [hpp41] using hCSZ)) (litHolds_nil pp41))))
          simpa [hpp41] using h
        have vBCX : orient B C Z < 0 := by
          have h := sign_imp_neg [(0, 1, 2, true), (1, 2, 3, false), (0, 2, 3, false), (2, 3, 4, true), (0, 2, 4, false)] 1 2 4 (by decide +kernel) pp41 gg41
            (litHolds_cons (litHolds_pos pp41 0 1 2 (by simpa [hpp41] using bABC)) (litHolds_cons (litHolds_neg pp41 1 2 3 (by simpa [hpp41] using bBCS)) (litHolds_cons (litHolds_neg pp41 0 2 3 (by simpa [hpp41] using bACS)) (litHolds_cons (litHolds_pos pp41 2 3 4 (by simpa [hpp41] using hCSZ)) (litHolds_cons (litHolds_neg pp41 0 2 4 (by simpa [hpp41] using vACX)) (litHolds_nil pp41))))))
          simpa [hpp41] using h
        exact vBCX
      · exact hd.2.1
    set pp42 : Fin 5 → Point := ![B, C, Q, S3, Z] with hpp42
    have gg42 : IndexedGP pp42 := by
      have h := indexedGP_vec5 S hgp B C Q S3 Z mB mC mQ mS3 mZ neBC neBQ neBS3 neBZ neCQ neCS3 neCZ neQS3 neQZ neS3Z
      simpa [hpp42] using h
    have q2BQX : 0 < orient B Q Z := by
      have h := sign_imp_pos [(0, 1, 2, false), (0, 1, 3, false), (0, 2, 3, true), (1, 2, 3, true), (2, 3, 4, true), (1, 3, 4, true), (0, 1, 4, false)] 0 2 4 (by decide +kernel) pp42 gg42
        (litHolds_cons (litHolds_neg pp42 0 1 2 (by simpa [hpp42] using bBCQ)) (litHolds_cons (litHolds_neg pp42 0 1 3 (by simpa [hpp42] using bBCS)) (litHolds_cons (litHolds_pos pp42 0 2 3 (by simpa [hpp42] using bBQS)) (litHolds_cons (litHolds_pos pp42 1 2 3 (by simpa [hpp42] using bCQS)) (litHolds_cons (litHolds_pos pp42 2 3 4 (by simpa [hpp42] using hQSZ)) (litHolds_cons (litHolds_pos pp42 1 3 4 (by simpa [hpp42] using hCSZ)) (litHolds_cons (litHolds_neg pp42 0 1 4 (by simpa [hpp42] using hBCZ)) (litHolds_nil pp42))))))))
      simpa [hpp42] using h
    have q2BSX : 0 < orient B S3 Z := by
      have h := sign_imp_pos [(0, 1, 3, false), (1, 2, 3, true), (2, 3, 4, true), (1, 3, 4, true), (0, 2, 4, true)] 0 3 4 (by decide +kernel) pp42 gg42
        (litHolds_cons (litHolds_neg pp42 0 1 3 (by simpa [hpp42] using bBCS)) (litHolds_cons (litHolds_pos pp42 1 2 3 (by simpa [hpp42] using bCQS)) (litHolds_cons (litHolds_pos pp42 2 3 4 (by simpa [hpp42] using hQSZ)) (litHolds_cons (litHolds_pos pp42 1 3 4 (by simpa [hpp42] using hCSZ)) (litHolds_cons (litHolds_pos pp42 0 2 4 (by simpa [hpp42] using q2BQX)) (litHolds_nil pp42))))))
      simpa [hpp42] using h
    have q2CQX : 0 < orient C Q Z := by
      have h := sign_imp_pos [(2, 3, 4, true), (1, 3, 4, true), (0, 1, 4, false), (0, 2, 4, true), (0, 3, 4, true)] 1 2 4 (by decide +kernel) pp42 gg42
        (litHolds_cons (litHolds_pos pp42 2 3 4 (by simpa [hpp42] using hQSZ)) (litHolds_cons (litHolds_pos pp42 1 3 4 (by simpa [hpp42] using hCSZ)) (litHolds_cons (litHolds_neg pp42 0 1 4 (by simpa [hpp42] using hBCZ)) (litHolds_cons (litHolds_pos pp42 0 2 4 (by simpa [hpp42] using q2BQX)) (litHolds_cons (litHolds_pos pp42 0 3 4 (by simpa [hpp42] using q2BSX)) (litHolds_nil pp42))))))
      simpa [hpp42] using h
    have q2c012 : 0 < orient B Q S3 := by
      have e : orient B Q S3 = orient B Q S3 := by unfold orient; ring
      linarith [bBQS]
    have q2c013 : 0 < orient B Q Z := by
      have e : orient B Q Z = orient B Q Z := by unfold orient; ring
      linarith [q2BQX]
    have q2c014 : 0 < orient B Q C := by
      have e : orient B Q C = -orient B C Q := by unfold orient; ring
      linarith [bBCQ]
    have q2c023 : 0 < orient B S3 Z := by
      have e : orient B S3 Z = orient B S3 Z := by unfold orient; ring
      linarith [q2BSX]
    have q2c024 : 0 < orient B S3 C := by
      have e : orient B S3 C = -orient B C S3 := by unfold orient; ring
      linarith [bBCS]
    have q2c034 : 0 < orient B Z C := by
      have e : orient B Z C = -orient B C Z := by unfold orient; ring
      linarith [hBCZ]
    have q2c123 : 0 < orient Q S3 Z := by
      have e : orient Q S3 Z = orient Q S3 Z := by unfold orient; ring
      linarith [hQSZ]
    have q2c124 : 0 < orient Q S3 C := by
      have e : orient Q S3 C = orient C Q S3 := by unfold orient; ring
      linarith [bCQS]
    have q2c134 : 0 < orient Q Z C := by
      have e : orient Q Z C = orient C Q Z := by unfold orient; ring
      linarith [q2CQX]
    have q2c234 : 0 < orient S3 Z C := by
      have e : orient S3 Z C = orient C S3 Z := by unfold orient; ring
      linarith [hCSZ]
    have q2sA : orient B Q A < 0 := by
      have e : orient B Q A = orient A B Q := by unfold orient; ring
      linarith [bABQ]
    have q2sD : orient C B D < 0 := by
      have e : orient C B D = -orient B C D := by unfold orient; ring
      linarith [bBCD]
    have q2sE : orient B Q E < 0 := by
      have e : orient B Q E = -orient B E Q := by unfold orient; ring
      linarith [bBEQ]
    have q2sM : orient B Q M < 0 := by
      have e : orient B Q M = -orient B M Q := by unfold orient; ring
      linarith [bBMQ]
    have q2sY : orient S3 Z W < 0 := by
      have e : orient S3 Z W = orient S3 Z W := by unfold orient; ring
      linarith [hSZW]
    refine pent5_of_signs S B Q S3 Z C mB mQ mS3 mZ mC q2c012 q2c013 q2c014 q2c023 q2c024 q2c034 q2c123 q2c124 q2c134 q2c234 ?_
    intro q hq hq0 hq1 hq2 hq3 hq4
    rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (le_of_lt q2sA)
    · exact absurd rfl hq0
    · exact absurd rfl hq4
    · exact Or.inr (Or.inr (Or.inr (Or.inr (le_of_lt q2sD))))
    · exact Or.inl (le_of_lt q2sE)
    · exact Or.inl (le_of_lt q2sM)
    · exact absurd rfl hq1
    · exact absurd rfl hq2
    · exact absurd rfl hq3
    · exact Or.inr (Or.inr (Or.inl (le_of_lt q2sY)))


set_option maxHeartbeats 2000000 in
/-- Harborth two-point case, the outer point `Z` right of `Q → S3` and `W` left. -/
theorem two_MX (S : Finset Point) (hgp : GeneralPosition S)
    (A B C D E M Q S3 Z W : Point)
    (mA : A ∈ S) (mB : B ∈ S) (mC : C ∈ S) (mD : D ∈ S) (mE : E ∈ S) (mM : M ∈ S) (mQ : Q ∈ S) (mS3 : S3 ∈ S) (mZ : Z ∈ S) (mW : W ∈ S)
    (neAB : A ≠ B) (neAC : A ≠ C) (neAD : A ≠ D) (neAE : A ≠ E)
    (neAM : A ≠ M) (neAQ : A ≠ Q) (neAS3 : A ≠ S3) (neAZ : A ≠ Z)
    (neAW : A ≠ W) (neBC : B ≠ C) (neBD : B ≠ D) (neBE : B ≠ E)
    (neBM : B ≠ M) (neBQ : B ≠ Q) (neBS3 : B ≠ S3) (neBZ : B ≠ Z)
    (neBW : B ≠ W) (neCD : C ≠ D) (neCE : C ≠ E) (neCM : C ≠ M)
    (neCQ : C ≠ Q) (neCS3 : C ≠ S3) (neCZ : C ≠ Z) (neCW : C ≠ W)
    (neDE : D ≠ E) (neDM : D ≠ M) (neDQ : D ≠ Q) (neDS3 : D ≠ S3)
    (neDZ : D ≠ Z) (neDW : D ≠ W) (neEM : E ≠ M) (neEQ : E ≠ Q)
    (neES3 : E ≠ S3) (neEZ : E ≠ Z) (neEW : E ≠ W) (neMQ : M ≠ Q)
    (neMS3 : M ≠ S3) (neMZ : M ≠ Z) (neMW : M ≠ W) (neQS3 : Q ≠ S3)
    (neQZ : Q ≠ Z) (neQW : Q ≠ W) (neS3Z : S3 ≠ Z) (neS3W : S3 ≠ W)
    (neZW : Z ≠ W)
    (hSall : ∀ q ∈ S, q = A ∨ q = B ∨ q = C ∨ q = D ∨ q = E ∨ q = M ∨ q = Q ∨ q = S3 ∨ q = Z ∨ q = W)
    (bABC : 0 < orient A B C) (bABD : 0 < orient A B D) (bABE : 0 < orient A B E)
    (bACD : 0 < orient A C D) (bACE : 0 < orient A C E) (bADE : 0 < orient A D E)
    (bBCD : 0 < orient B C D) (bBCE : 0 < orient B C E) (bBDE : 0 < orient B D E)
    (bCDE : 0 < orient C D E) (bABM : 0 < orient A B M) (bBCM : 0 < orient B C M)
    (bCDM : 0 < orient C D M) (bDEM : 0 < orient D E M) (bAEM : orient A E M < 0)
    (bACM : 0 < orient A C M) (bBDM : 0 < orient B D M) (bCEM : 0 < orient C E M)
    (bADM : orient A D M < 0) (bBEM : orient B E M < 0) (bAMQ : orient A M Q < 0)
    (bBMQ : 0 < orient B M Q) (bABQ : orient A B Q < 0) (bAEQ : 0 < orient A E Q)
    (bBCQ : orient B C Q < 0) (bAMS : orient A M S3 < 0) (bBMS : 0 < orient B M S3)
    (bABS : orient A B S3 < 0) (bAES : 0 < orient A E S3) (bBCS : orient B C S3 < 0)
    (bAQS : orient A Q S3 < 0) (bBQS : 0 < orient B Q S3) (bACQ : orient A C Q < 0)
    (bACS : orient A C S3 < 0) (bBEQ : 0 < orient B E Q) (bBES : 0 < orient B E S3)
    (bCEQ : 0 < orient C E Q) (bCES : 0 < orient C E S3) (bCMQ : 0 < orient C M Q)
    (bCMS : 0 < orient C M S3) (bCQS : 0 < orient C Q S3) (bEMQ : orient E M Q < 0)
    (bEMS : orient E M S3 < 0) (bEQS : orient E Q S3 < 0)
    (hRegZ : RegAll A B C D E M Q S3 Z) (hRegW : RegAll A B C D E M Q S3 W)
    (hQSZ : orient Q S3 Z < 0) (hQSW : 0 < orient Q S3 W) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  have hDigZ : RDig A D E M Q S3 Z ∨ LDig B C D M Q S3 Z := by
    rcases hRegZ with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inl h
  have hDigW : RDig A D E M Q S3 W ∨ LDig B C D M Q S3 W := by
    rcases hRegW with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
    · exact Or.inl h
  rcases lt_or_gt_of_ne (hgp E mE S3 mS3 Z mZ neES3 neEZ neS3Z) with hESZ | hESZ
  · -- the pentagon `A, E, Z, S3, Q`
    have hAEZ : 0 < orient A E Z := by
      rcases hDigZ with hd | hd
      · exact hd.2.2.1
      · obtain ⟨lz1, lz2, lz3, lz4, lz5, lz6, lz7, lz8, lz9⟩ := hd
        set pp1 : Fin 5 → Point := ![A, B, E, S3, Z] with hpp1
        have gg1 : IndexedGP pp1 := by
          have h := indexedGP_vec5 S hgp A B E S3 Z mA mB mE mS3 mZ neAB neAE neAS3 neAZ neBE neBS3 neBZ neES3 neEZ neS3Z
          simpa [hpp1] using h
        have wAEX : 0 < orient A E Z := by
          have h := sign_imp_pos [(0, 1, 2, true), (0, 2, 3, true), (1, 2, 3, true), (1, 3, 4, true), (2, 3, 4, false)] 0 2 4 (by decide +kernel) pp1 gg1
            (litHolds_cons (litHolds_pos pp1 0 1 2 (by simpa [hpp1] using bABE)) (litHolds_cons (litHolds_pos pp1 0 2 3 (by simpa [hpp1] using bAES)) (litHolds_cons (litHolds_pos pp1 1 2 3 (by simpa [hpp1] using bBES)) (litHolds_cons (litHolds_pos pp1 1 3 4 (by simpa [hpp1] using lz6)) (litHolds_cons (litHolds_neg pp1 2 3 4 (by simpa [hpp1] using hESZ)) (litHolds_nil pp1))))))
          simpa [hpp1] using h
        exact wAEX
    set pp2 : Fin 5 → Point := ![A, E, Q, S3, Z] with hpp2
    have gg2 : IndexedGP pp2 := by
      have h := indexedGP_vec5 S hgp A E Q S3 Z mA mE mQ mS3 mZ neAE neAQ neAS3 neAZ neEQ neES3 neEZ neQS3 neQZ neS3Z
      simpa [hpp2] using h
    have x1AQX : orient A Q Z < 0 := by
      have h := sign_imp_neg [(0, 1, 2, true), (0, 1, 3, true), (0, 2, 3, false), (1, 2, 3, false), (2, 3, 4, false), (1, 3, 4, false), (0, 1, 4, true)] 0 2 4 (by decide +kernel) pp2 gg2
        (litHolds_cons (litHolds_pos pp2 0 1 2 (by simpa [hpp2] using bAEQ)) (litHolds_cons (litHolds_pos pp2 0 1 3 (by simpa [hpp2] using bAES)) (litHolds_cons (litHolds_neg pp2 0 2 3 (by simpa [hpp2] using bAQS)) (litHolds_cons (litHolds_neg pp2 1 2 3 (by simpa [hpp2] using bEQS)) (litHolds_cons (litHolds_neg pp2 2 3 4 (by simpa [hpp2] using hQSZ)) (litHolds_cons (litHolds_neg pp2 1 3 4 (by simpa [hpp2] using hESZ)) (litHolds_cons (litHolds_pos pp2 0 1 4 (by simpa [hpp2] using hAEZ)) (litHolds_nil pp2))))))))
      simpa [hpp2] using h
    have x1ASX : orient A S3 Z < 0 := by
      have h := sign_imp_neg [(0, 1, 3, true), (1, 2, 3, false), (2, 3, 4, false), (1, 3, 4, false), (0, 2, 4, false)] 0 3 4 (by decide +kernel) pp2 gg2
        (litHolds_cons (litHolds_pos pp2 0 1 3 (by simpa [hpp2] using bAES)) (litHolds_cons (litHolds_neg pp2 1 2 3 (by simpa [hpp2] using bEQS)) (litHolds_cons (litHolds_neg pp2 2 3 4 (by simpa [hpp2] using hQSZ)) (litHolds_cons (litHolds_neg pp2 1 3 4 (by simpa [hpp2] using hESZ)) (litHolds_cons (litHolds_neg pp2 0 2 4 (by simpa [hpp2] using x1AQX)) (litHolds_nil pp2))))))
      simpa [hpp2] using h
    have x1EQX : orient E Q Z < 0 := by
      have h := sign_imp_neg [(2, 3, 4, false), (1, 3, 4, false), (0, 1, 4, true), (0, 2, 4, false), (0, 3, 4, false)] 1 2 4 (by decide +kernel) pp2 gg2
        (litHolds_cons (litHolds_neg pp2 2 3 4 (by simpa [hpp2] using hQSZ)) (litHolds_cons (litHolds_neg pp2 1 3 4 (by simpa [hpp2] using hESZ)) (litHolds_cons (litHolds_pos pp2 0 1 4 (by simpa [hpp2] using hAEZ)) (litHolds_cons (litHolds_neg pp2 0 2 4 (by simpa [hpp2] using x1AQX)) (litHolds_cons (litHolds_neg pp2 0 3 4 (by simpa [hpp2] using x1ASX)) (litHolds_nil pp2))))))
      simpa [hpp2] using h
    have x1c012 : 0 < orient A E Z := by
      have e : orient A E Z = orient A E Z := by unfold orient; ring
      linarith [hAEZ]
    have x1c013 : 0 < orient A E S3 := by
      have e : orient A E S3 = orient A E S3 := by unfold orient; ring
      linarith [bAES]
    have x1c014 : 0 < orient A E Q := by
      have e : orient A E Q = orient A E Q := by unfold orient; ring
      linarith [bAEQ]
    have x1c023 : 0 < orient A Z S3 := by
      have e : orient A Z S3 = -orient A S3 Z := by unfold orient; ring
      linarith [x1ASX]
    have x1c024 : 0 < orient A Z Q := by
      have e : orient A Z Q = -orient A Q Z := by unfold orient; ring
      linarith [x1AQX]
    have x1c034 : 0 < orient A S3 Q := by
      have e : orient A S3 Q = -orient A Q S3 := by unfold orient; ring
      linarith [bAQS]
    have x1c123 : 0 < orient E Z S3 := by
      have e : orient E Z S3 = -orient E S3 Z := by unfold orient; ring
      linarith [hESZ]
    have x1c124 : 0 < orient E Z Q := by
      have e : orient E Z Q = -orient E Q Z := by unfold orient; ring
      linarith [x1EQX]
    have x1c134 : 0 < orient E S3 Q := by
      have e : orient E S3 Q = -orient E Q S3 := by unfold orient; ring
      linarith [bEQS]
    have x1c234 : 0 < orient Z S3 Q := by
      have e : orient Z S3 Q = -orient Q S3 Z := by unfold orient; ring
      linarith [hQSZ]
    have x1sB : orient A E B < 0 := by
      have e : orient A E B = -orient A B E := by unfold orient; ring
      linarith [bABE]
    have x1sC : orient A E C < 0 := by
      have e : orient A E C = -orient A C E := by unfold orient; ring
      linarith [bACE]
    have x1sD : orient A E D < 0 := by
      have e : orient A E D = -orient A D E := by unfold orient; ring
      linarith [bADE]
    have x1sM : orient A E M < 0 := by
      have e : orient A E M = orient A E M := by unfold orient; ring
      linarith [bAEM]
    have x1sY : orient S3 Q W < 0 := by
      have e : orient S3 Q W = -orient Q S3 W := by unfold orient; ring
      linarith [hQSW]
    refine pent5_of_signs S A E Z S3 Q mA mE mZ mS3 mQ x1c012 x1c013 x1c014 x1c023 x1c024 x1c034 x1c123 x1c124 x1c134 x1c234 ?_
    intro q hq hq0 hq1 hq2 hq3 hq4
    rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq0
    · exact Or.inl (le_of_lt x1sB)
    · exact Or.inl (le_of_lt x1sC)
    · exact Or.inl (le_of_lt x1sD)
    · exact absurd rfl hq1
    · exact Or.inl (le_of_lt x1sM)
    · exact absurd rfl hq4
    · exact absurd rfl hq3
    · exact absurd rfl hq2
    · exact Or.inr (Or.inr (Or.inr (Or.inl (le_of_lt x1sY))))
  · -- `Z` is inside the quadrilateral `E, S3, Q, A`
    rcases lt_or_gt_of_ne (hgp C mC S3 mS3 W mW neCS3 neCW neS3W) with hCSW | hCSW
    · -- impossible: `W` would be inside the quadrilateral `B, Q, S3, C`
      exfalso
      rcases hDigZ with hdz | hdz
      · obtain ⟨rz1, rz2, rz3, rz4, rz5, rz6, rz7, rz8, rz9⟩ := hdz
        rcases hDigW with hdw | hdw
        · obtain ⟨rw1, rw2, rw3, rw4, rw5, rw6, rw7, rw8, rw9⟩ := hdw
          set pp3 : Fin 5 → Point := ![A, B, Q, S3, W] with hpp3
          have gg3 : IndexedGP pp3 := by
            have h := indexedGP_vec5 S hgp A B Q S3 W mA mB mQ mS3 mW neAB neAQ neAS3 neAW neBQ neBS3 neBW neQS3 neQW neS3W
            simpa [hpp3] using h
          have yRRABY : orient A B W < 0 := by
            have h := sign_imp_neg [(0, 1, 3, false), (0, 2, 3, false), (1, 2, 3, true), (2, 3, 4, true), (0, 3, 4, false)] 0 1 4 (by decide +kernel) pp3 gg3
              (litHolds_cons (litHolds_neg pp3 0 1 3 (by simpa [hpp3] using bABS)) (litHolds_cons (litHolds_neg pp3 0 2 3 (by simpa [hpp3] using bAQS)) (litHolds_cons (litHolds_pos pp3 1 2 3 (by simpa [hpp3] using bBQS)) (litHolds_cons (litHolds_pos pp3 2 3 4 (by simpa [hpp3] using hQSW)) (litHolds_cons (litHolds_neg pp3 0 3 4 (by simpa [hpp3] using rw7)) (litHolds_nil pp3))))))
            simpa [hpp3] using h
          have yRRBQY : 0 < orient B Q W := by
            have h := sign_imp_pos [(0, 1, 2, false), (0, 2, 3, false), (1, 2, 3, true), (2, 3, 4, true), (0, 3, 4, false)] 1 2 4 (by decide +kernel) pp3 gg3
              (litHolds_cons (litHolds_neg pp3 0 1 2 (by simpa [hpp3] using bABQ)) (litHolds_cons (litHolds_neg pp3 0 2 3 (by simpa [hpp3] using bAQS)) (litHolds_cons (litHolds_pos pp3 1 2 3 (by simpa [hpp3] using bBQS)) (litHolds_cons (litHolds_pos pp3 2 3 4 (by simpa [hpp3] using hQSW)) (litHolds_cons (litHolds_neg pp3 0 3 4 (by simpa [hpp3] using rw7)) (litHolds_nil pp3))))))
            simpa [hpp3] using h
          have yRRBSY : 0 < orient B S3 W := by
            have h := sign_imp_pos [(2, 3, 4, true), (0, 2, 4, false), (0, 3, 4, false), (0, 1, 4, false), (1, 2, 4, true)] 1 3 4 (by decide +kernel) pp3 gg3
              (litHolds_cons (litHolds_pos pp3 2 3 4 (by simpa [hpp3] using hQSW)) (litHolds_cons (litHolds_neg pp3 0 2 4 (by simpa [hpp3] using rw6)) (litHolds_cons (litHolds_neg pp3 0 3 4 (by simpa [hpp3] using rw7)) (litHolds_cons (litHolds_neg pp3 0 1 4 (by simpa [hpp3] using yRRABY)) (litHolds_cons (litHolds_pos pp3 1 2 4 (by simpa [hpp3] using yRRBQY)) (litHolds_nil pp3))))))
            simpa [hpp3] using h
          set pp4 : Fin 5 → Point := ![A, B, C, S3, W] with hpp4
          have gg4 : IndexedGP pp4 := by
            have h := indexedGP_vec5 S hgp A B C S3 W mA mB mC mS3 mW neAB neAC neAS3 neAW neBC neBS3 neBW neCS3 neCW neS3W
            simpa [hpp4] using h
          have yRRX : 0 < orient C S3 W := by
            have h := sign_imp_pos [(0, 1, 3, false), (1, 2, 3, false), (0, 2, 3, false), (0, 3, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp4 gg4
              (litHolds_cons (litHolds_neg pp4 0 1 3 (by simpa [hpp4] using bABS)) (litHolds_cons (litHolds_neg pp4 1 2 3 (by simpa [hpp4] using bBCS)) (litHolds_cons (litHolds_neg pp4 0 2 3 (by simpa [hpp4] using bACS)) (litHolds_cons (litHolds_neg pp4 0 3 4 (by simpa [hpp4] using rw7)) (litHolds_cons (litHolds_pos pp4 1 3 4 (by simpa [hpp4] using yRRBSY)) (litHolds_nil pp4))))))
            simpa [hpp4] using h
          exfalso
          linarith
        · obtain ⟨lw1, lw2, lw3, lw4, lw5, lw6, lw7, lw8, lw9⟩ := hdw
          set pp5 : Fin 5 → Point := ![A, B, C, S3, W] with hpp5
          have gg5 : IndexedGP pp5 := by
            have h := indexedGP_vec5 S hgp A B C S3 W mA mB mC mS3 mW neAB neAC neAS3 neAW neBC neBS3 neBW neCS3 neCW neS3W
            simpa [hpp5] using h
          have yRLACY : orient A C W < 0 := by
            have h := sign_imp_neg [(0, 1, 2, true), (0, 2, 3, false), (2, 3, 4, false), (1, 2, 4, false), (1, 3, 4, true)] 0 2 4 (by decide +kernel) pp5 gg5
              (litHolds_cons (litHolds_pos pp5 0 1 2 (by simpa [hpp5] using bABC)) (litHolds_cons (litHolds_neg pp5 0 2 3 (by simpa [hpp5] using bACS)) (litHolds_cons (litHolds_neg pp5 2 3 4 (by simpa [hpp5] using hCSW)) (litHolds_cons (litHolds_neg pp5 1 2 4 (by simpa [hpp5] using lw2)) (litHolds_cons (litHolds_pos pp5 1 3 4 (by simpa [hpp5] using lw6)) (litHolds_nil pp5))))))
            simpa [hpp5] using h
          set pp6 : Fin 5 → Point := ![A, D, E, S3, Z] with hpp6
          have gg6 : IndexedGP pp6 := by
            have h := indexedGP_vec5 S hgp A D E S3 Z mA mD mE mS3 mZ neAD neAE neAS3 neAZ neDE neDS3 neDZ neES3 neEZ neS3Z
            simpa [hpp6] using h
          have yRLADS : 0 < orient A D S3 := by
            have h := sign_imp_pos [(2, 3, 4, true), (1, 2, 4, false), (0, 2, 4, true), (0, 1, 4, true), (0, 3, 4, false)] 0 1 3 (by decide +kernel) pp6 gg6
              (litHolds_cons (litHolds_pos pp6 2 3 4 (by simpa [hpp6] using hESZ)) (litHolds_cons (litHolds_neg pp6 1 2 4 (by simpa [hpp6] using rz2)) (litHolds_cons (litHolds_pos pp6 0 2 4 (by simpa [hpp6] using rz3)) (litHolds_cons (litHolds_pos pp6 0 1 4 (by simpa [hpp6] using rz4)) (litHolds_cons (litHolds_neg pp6 0 3 4 (by simpa [hpp6] using rz7)) (litHolds_nil pp6))))))
            simpa [hpp6] using h
          set pp7 : Fin 5 → Point := ![A, C, D, S3, W] with hpp7
          have gg7 : IndexedGP pp7 := by
            have h := indexedGP_vec5 S hgp A C D S3 W mA mC mD mS3 mW neAC neAD neAS3 neAW neCD neCS3 neCW neDS3 neDW neS3W
            simpa [hpp7] using h
          have yRLADY : 0 < orient A D W := by
            have h := sign_imp_pos [(0, 1, 2, true), (0, 1, 3, false), (1, 3, 4, false), (1, 2, 4, false), (0, 1, 4, false), (0, 2, 3, true)] 0 2 4 (by decide +kernel) pp7 gg7
              (litHolds_cons (litHolds_pos pp7 0 1 2 (by simpa [hpp7] using bACD)) (litHolds_cons (litHolds_neg pp7 0 1 3 (by simpa [hpp7] using bACS)) (litHolds_cons (litHolds_neg pp7 1 3 4 (by simpa [hpp7] using hCSW)) (litHolds_cons (litHolds_neg pp7 1 2 4 (by simpa [hpp7] using lw3)) (litHolds_cons (litHolds_neg pp7 0 1 4 (by simpa [hpp7] using yRLACY)) (litHolds_cons (litHolds_pos pp7 0 2 3 (by simpa [hpp7] using yRLADS)) (litHolds_nil pp7)))))))
            simpa [hpp7] using h
          set pp8 : Fin 5 → Point := ![A, B, C, D, W] with hpp8
          have gg8 : IndexedGP pp8 := by
            have h := indexedGP_vec5 S hgp A B C D W mA mB mC mD mW neAB neAC neAD neAW neBC neBD neBW neCD neCW neDW
            simpa [hpp8] using h
          have yRLX : orient A B D < 0 := by
            have h := sign_imp_neg [(1, 2, 4, false), (2, 3, 4, false), (1, 3, 4, false), (0, 2, 4, false), (0, 3, 4, true)] 0 1 3 (by decide +kernel) pp8 gg8
              (litHolds_cons (litHolds_neg pp8 1 2 4 (by simpa [hpp8] using lw2)) (litHolds_cons (litHolds_neg pp8 2 3 4 (by simpa [hpp8] using lw3)) (litHolds_cons (litHolds_neg pp8 1 3 4 (by simpa [hpp8] using lw4)) (litHolds_cons (litHolds_neg pp8 0 2 4 (by simpa [hpp8] using yRLACY)) (litHolds_cons (litHolds_pos pp8 0 3 4 (by simpa [hpp8] using yRLADY)) (litHolds_nil pp8))))))
            simpa [hpp8] using h
          exfalso
          linarith
      · obtain ⟨lz1, lz2, lz3, lz4, lz5, lz6, lz7, lz8, lz9⟩ := hdz
        rcases hDigW with hdw | hdw
        · obtain ⟨rw1, rw2, rw3, rw4, rw5, rw6, rw7, rw8, rw9⟩ := hdw
          set pp9 : Fin 5 → Point := ![A, C, Q, S3, W] with hpp9
          have gg9 : IndexedGP pp9 := by
            have h := indexedGP_vec5 S hgp A C Q S3 W mA mC mQ mS3 mW neAC neAQ neAS3 neAW neCQ neCS3 neCW neQS3 neQW neS3W
            simpa [hpp9] using h
          have yLRACY : 0 < orient A C W := by
            have h := sign_imp_pos [(0, 2, 3, false), (0, 1, 3, false), (1, 2, 3, true), (2, 3, 4, true), (1, 3, 4, false), (0, 3, 4, false)] 0 1 4 (by decide +kernel) pp9 gg9
              (litHolds_cons (litHolds_neg pp9 0 2 3 (by simpa [hpp9] using bAQS)) (litHolds_cons (litHolds_neg pp9 0 1 3 (by simpa [hpp9] using bACS)) (litHolds_cons (litHolds_pos pp9 1 2 3 (by simpa [hpp9] using bCQS)) (litHolds_cons (litHolds_pos pp9 2 3 4 (by simpa [hpp9] using hQSW)) (litHolds_cons (litHolds_neg pp9 1 3 4 (by simpa [hpp9] using hCSW)) (litHolds_cons (litHolds_neg pp9 0 3 4 (by simpa [hpp9] using rw7)) (litHolds_nil pp9)))))))
            simpa [hpp9] using h
          set pp10 : Fin 5 → Point := ![A, B, Q, S3, W] with hpp10
          have gg10 : IndexedGP pp10 := by
            have h := indexedGP_vec5 S hgp A B Q S3 W mA mB mQ mS3 mW neAB neAQ neAS3 neAW neBQ neBS3 neBW neQS3 neQW neS3W
            simpa [hpp10] using h
          have yLRBQY : 0 < orient B Q W := by
            have h := sign_imp_pos [(0, 1, 2, false), (0, 2, 3, false), (1, 2, 3, true), (2, 3, 4, true), (0, 3, 4, false)] 1 2 4 (by decide +kernel) pp10 gg10
              (litHolds_cons (litHolds_neg pp10 0 1 2 (by simpa [hpp10] using bABQ)) (litHolds_cons (litHolds_neg pp10 0 2 3 (by simpa [hpp10] using bAQS)) (litHolds_cons (litHolds_pos pp10 1 2 3 (by simpa [hpp10] using bBQS)) (litHolds_cons (litHolds_pos pp10 2 3 4 (by simpa [hpp10] using hQSW)) (litHolds_cons (litHolds_neg pp10 0 3 4 (by simpa [hpp10] using rw7)) (litHolds_nil pp10))))))
            simpa [hpp10] using h
          set pp11 : Fin 5 → Point := ![A, B, C, Q, W] with hpp11
          have gg11 : IndexedGP pp11 := by
            have h := indexedGP_vec5 S hgp A B C Q W mA mB mC mQ mW neAB neAC neAQ neAW neBC neBQ neBW neCQ neCW neQW
            simpa [hpp11] using h
          have yLRCQY : 0 < orient C Q W := by
            have h := sign_imp_pos [(0, 1, 3, false), (1, 2, 3, false), (0, 2, 3, false), (0, 3, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp11 gg11
              (litHolds_cons (litHolds_neg pp11 0 1 3 (by simpa [hpp11] using bABQ)) (litHolds_cons (litHolds_neg pp11 1 2 3 (by simpa [hpp11] using bBCQ)) (litHolds_cons (litHolds_neg pp11 0 2 3 (by simpa [hpp11] using bACQ)) (litHolds_cons (litHolds_neg pp11 0 3 4 (by simpa [hpp11] using rw6)) (litHolds_cons (litHolds_pos pp11 1 3 4 (by simpa [hpp11] using yLRBQY)) (litHolds_nil pp11))))))
            simpa [hpp11] using h
          have yLRX : 0 < orient A C Q := by
            have h := sign_imp_pos [(0, 3, 4, false), (0, 2, 4, true), (2, 3, 4, true)] 0 2 3 (by decide +kernel) pp11 gg11
              (litHolds_cons (litHolds_neg pp11 0 3 4 (by simpa [hpp11] using rw6)) (litHolds_cons (litHolds_pos pp11 0 2 4 (by simpa [hpp11] using yLRACY)) (litHolds_cons (litHolds_pos pp11 2 3 4 (by simpa [hpp11] using yLRCQY)) (litHolds_nil pp11))))
            simpa [hpp11] using h
          exfalso
          linarith
        · obtain ⟨lw1, lw2, lw3, lw4, lw5, lw6, lw7, lw8, lw9⟩ := hdw
          set pp12 : Fin 5 → Point := ![B, E, Q, S3, Z] with hpp12
          have gg12 : IndexedGP pp12 := by
            have h := indexedGP_vec5 S hgp B E Q S3 Z mB mE mQ mS3 mZ neBE neBQ neBS3 neBZ neEQ neES3 neEZ neQS3 neQZ neS3Z
            simpa [hpp12] using h
          have yLLX : orient B E S3 < 0 := by
            have h := sign_imp_neg [(0, 2, 3, true), (1, 2, 3, false), (2, 3, 4, false), (1, 3, 4, true), (0, 3, 4, true)] 0 1 3 (by decide +kernel) pp12 gg12
              (litHolds_cons (litHolds_pos pp12 0 2 3 (by simpa [hpp12] using bBQS)) (litHolds_cons (litHolds_neg pp12 1 2 3 (by simpa [hpp12] using bEQS)) (litHolds_cons (litHolds_neg pp12 2 3 4 (by simpa [hpp12] using hQSZ)) (litHolds_cons (litHolds_pos pp12 1 3 4 (by simpa [hpp12] using hESZ)) (litHolds_cons (litHolds_pos pp12 0 3 4 (by simpa [hpp12] using lz6)) (litHolds_nil pp12))))))
            simpa [hpp12] using h
          exfalso
          linarith
    · -- the pentagon `B, Q, S3, W, C`
      have hBCW : orient B C W < 0 := by
        rcases hDigW with hd | hd
        · obtain ⟨rw1, rw2, rw3, rw4, rw5, rw6, rw7, rw8, rw9⟩ := hd
          set pp13 : Fin 5 → Point := ![A, B, C, S3, W] with hpp13
          have gg13 : IndexedGP pp13 := by
            have h := indexedGP_vec5 S hgp A B C S3 W mA mB mC mS3 mW neAB neAC neAS3 neAW neBC neBS3 neBW neCS3 neCW neS3W
            simpa [hpp13] using h
          have zACY : orient A C W < 0 := by
            have h := sign_imp_neg [(0, 2, 3, false), (0, 3, 4, false), (2, 3, 4, true)] 0 2 4 (by decide +kernel) pp13 gg13
              (litHolds_cons (litHolds_neg pp13 0 2 3 (by simpa [hpp13] using bACS)) (litHolds_cons (litHolds_neg pp13 0 3 4 (by simpa [hpp13] using rw7)) (litHolds_cons (litHolds_pos pp13 2 3 4 (by simpa [hpp13] using hCSW)) (litHolds_nil pp13))))
            simpa [hpp13] using h
          have zBCY : orient B C W < 0 := by
            have h := sign_imp_neg [(0, 1, 2, true), (1, 2, 3, false), (0, 2, 3, false), (2, 3, 4, true), (0, 2, 4, false)] 1 2 4 (by decide +kernel) pp13 gg13
              (litHolds_cons (litHolds_pos pp13 0 1 2 (by simpa [hpp13] using bABC)) (litHolds_cons (litHolds_neg pp13 1 2 3 (by simpa [hpp13] using bBCS)) (litHolds_cons (litHolds_neg pp13 0 2 3 (by simpa [hpp13] using bACS)) (litHolds_cons (litHolds_pos pp13 2 3 4 (by simpa [hpp13] using hCSW)) (litHolds_cons (litHolds_neg pp13 0 2 4 (by simpa [hpp13] using zACY)) (litHolds_nil pp13))))))
            simpa [hpp13] using h
          exact zBCY
        · exact hd.2.1
      set pp14 : Fin 5 → Point := ![B, C, Q, S3, W] with hpp14
      have gg14 : IndexedGP pp14 := by
        have h := indexedGP_vec5 S hgp B C Q S3 W mB mC mQ mS3 mW neBC neBQ neBS3 neBW neCQ neCS3 neCW neQS3 neQW neS3W
        simpa [hpp14] using h
      have x2BQY : 0 < orient B Q W := by
        have h := sign_imp_pos [(0, 1, 2, false), (0, 1, 3, false), (0, 2, 3, true), (1, 2, 3, true), (2, 3, 4, true), (1, 3, 4, true), (0, 1, 4, false)] 0 2 4 (by decide +kernel) pp14 gg14
          (litHolds_cons (litHolds_neg pp14 0 1 2 (by simpa [hpp14] using bBCQ)) (litHolds_cons (litHolds_neg pp14 0 1 3 (by simpa [hpp14] using bBCS)) (litHolds_cons (litHolds_pos pp14 0 2 3 (by simpa [hpp14] using bBQS)) (litHolds_cons (litHolds_pos pp14 1 2 3 (by simpa [hpp14] using bCQS)) (litHolds_cons (litHolds_pos pp14 2 3 4 (by simpa [hpp14] using hQSW)) (litHolds_cons (litHolds_pos pp14 1 3 4 (by simpa [hpp14] using hCSW)) (litHolds_cons (litHolds_neg pp14 0 1 4 (by simpa [hpp14] using hBCW)) (litHolds_nil pp14))))))))
        simpa [hpp14] using h
      have x2BSY : 0 < orient B S3 W := by
        have h := sign_imp_pos [(0, 1, 3, false), (1, 2, 3, true), (2, 3, 4, true), (1, 3, 4, true), (0, 2, 4, true)] 0 3 4 (by decide +kernel) pp14 gg14
          (litHolds_cons (litHolds_neg pp14 0 1 3 (by simpa [hpp14] using bBCS)) (litHolds_cons (litHolds_pos pp14 1 2 3 (by simpa [hpp14] using bCQS)) (litHolds_cons (litHolds_pos pp14 2 3 4 (by simpa [hpp14] using hQSW)) (litHolds_cons (litHolds_pos pp14 1 3 4 (by simpa [hpp14] using hCSW)) (litHolds_cons (litHolds_pos pp14 0 2 4 (by simpa [hpp14] using x2BQY)) (litHolds_nil pp14))))))
        simpa [hpp14] using h
      have x2CQY : 0 < orient C Q W := by
        have h := sign_imp_pos [(2, 3, 4, true), (1, 3, 4, true), (0, 1, 4, false), (0, 2, 4, true), (0, 3, 4, true)] 1 2 4 (by decide +kernel) pp14 gg14
          (litHolds_cons (litHolds_pos pp14 2 3 4 (by simpa [hpp14] using hQSW)) (litHolds_cons (litHolds_pos pp14 1 3 4 (by simpa [hpp14] using hCSW)) (litHolds_cons (litHolds_neg pp14 0 1 4 (by simpa [hpp14] using hBCW)) (litHolds_cons (litHolds_pos pp14 0 2 4 (by simpa [hpp14] using x2BQY)) (litHolds_cons (litHolds_pos pp14 0 3 4 (by simpa [hpp14] using x2BSY)) (litHolds_nil pp14))))))
        simpa [hpp14] using h
      have x2c012 : 0 < orient B Q S3 := by
        have e : orient B Q S3 = orient B Q S3 := by unfold orient; ring
        linarith [bBQS]
      have x2c013 : 0 < orient B Q W := by
        have e : orient B Q W = orient B Q W := by unfold orient; ring
        linarith [x2BQY]
      have x2c014 : 0 < orient B Q C := by
        have e : orient B Q C = -orient B C Q := by unfold orient; ring
        linarith [bBCQ]
      have x2c023 : 0 < orient B S3 W := by
        have e : orient B S3 W = orient B S3 W := by unfold orient; ring
        linarith [x2BSY]
      have x2c024 : 0 < orient B S3 C := by
        have e : orient B S3 C = -orient B C S3 := by unfold orient; ring
        linarith [bBCS]
      have x2c034 : 0 < orient B W C := by
        have e : orient B W C = -orient B C W := by unfold orient; ring
        linarith [hBCW]
      have x2c123 : 0 < orient Q S3 W := by
        have e : orient Q S3 W = orient Q S3 W := by unfold orient; ring
        linarith [hQSW]
      have x2c124 : 0 < orient Q S3 C := by
        have e : orient Q S3 C = orient C Q S3 := by unfold orient; ring
        linarith [bCQS]
      have x2c134 : 0 < orient Q W C := by
        have e : orient Q W C = orient C Q W := by unfold orient; ring
        linarith [x2CQY]
      have x2c234 : 0 < orient S3 W C := by
        have e : orient S3 W C = orient C S3 W := by unfold orient; ring
        linarith [hCSW]
      have x2sA : orient B Q A < 0 := by
        have e : orient B Q A = orient A B Q := by unfold orient; ring
        linarith [bABQ]
      have x2sD : orient C B D < 0 := by
        have e : orient C B D = -orient B C D := by unfold orient; ring
        linarith [bBCD]
      have x2sE : orient B Q E < 0 := by
        have e : orient B Q E = -orient B E Q := by unfold orient; ring
        linarith [bBEQ]
      have x2sM : orient B Q M < 0 := by
        have e : orient B Q M = -orient B M Q := by unfold orient; ring
        linarith [bBMQ]
      have x2sX : orient Q S3 Z < 0 := by
        have e : orient Q S3 Z = orient Q S3 Z := by unfold orient; ring
        linarith [hQSZ]
      refine pent5_of_signs S B Q S3 W C mB mQ mS3 mW mC x2c012 x2c013 x2c014 x2c023 x2c024 x2c034 x2c123 x2c124 x2c134 x2c234 ?_
      intro q hq hq0 hq1 hq2 hq3 hq4
      rcases hSall q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (le_of_lt x2sA)
      · exact absurd rfl hq0
      · exact absurd rfl hq4
      · exact Or.inr (Or.inr (Or.inr (Or.inr (le_of_lt x2sD))))
      · exact Or.inl (le_of_lt x2sE)
      · exact Or.inl (le_of_lt x2sM)
      · exact absurd rfl hq1
      · exact absurd rfl hq2
      · exact Or.inr (Or.inl (le_of_lt x2sX))
      · exact absurd rfl hq3


set_option maxHeartbeats 4000000 in
/-- Harborth's two-point case: `S` consists of the pentagon, the interior point `M`, two points
`Q, S3` in the region `B i` (with `Q` at least as close to the edge line as `S3`, and `S3` beyond
the tent `P i, Q, P (i+1)`), and two further points `X, Y` lying in regions other than `B i`;
if `X` and `Y` share a region, the farther one lies beyond the tent of the closer one. Then `S`
has an empty convex pentagon. -/
theorem two_case (S : Finset Point) (hgp : GeneralPosition S) (P : Fin 5 → Point)
    (hinj : Function.Injective P) (hPS : ∀ i, P i ∈ S)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (M : Point) (hMS : M ∈ S)
    (hM : M ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)))
    (hcore : ∀ i, 0 < orient (P i) (P (i + 2)) M) (i : Fin 5) (Q S3 X Y : Point)
    (hS : ∀ q, q ∈ S ↔ (∃ j, q = P j) ∨ q = M ∨ q = Q ∨ q = S3 ∨ q = X ∨ q = Y)
    (hQ : InB P M i Q) (hS3 : InB P M i S3) (hQS3 : Q ≠ S3)
    (hQmin : -orient (P i) (P (i + 1)) Q ≤ -orient (P i) (P (i + 1)) S3)
    (hC : 0 < orient Q (P i) S3 ∧ 0 < orient (P (i + 1)) Q S3)
    (hX : ∃ j, j ≠ i ∧ InB P M j X) (hY : ∃ j, j ≠ i ∧ InB P M j Y) (hXY : X ≠ Y)
    (hsame : ∀ j, InB P M j X → InB P M j Y →
      (-orient (P j) (P (j + 1)) X ≤ -orient (P j) (P (j + 1)) Y →
        0 < orient X (P j) Y ∧ 0 < orient (P (j + 1)) X Y) ∧
      (-orient (P j) (P (j + 1)) Y ≤ -orient (P j) (P (j + 1)) X →
        0 < orient Y (P j) X ∧ 0 < orient (P (j + 1)) Y X)) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  -- (A) index arithmetic in `Fin 5`
  have a1 : ∀ a : Fin 5, a + 1 + 1 = a + 2 := by decide
  have a2 : ∀ a : Fin 5, a + 2 + 1 = a + 3 := by decide
  have a3 : ∀ a : Fin 5, a + 3 + 1 = a + 4 := by decide
  have a4 : ∀ a : Fin 5, a + 4 + 1 = a := by decide
  have a5 : ∀ a : Fin 5, a - 1 = a + 4 := by decide
  have a6 : ∀ a : Fin 5, a + 1 + 2 = a + 3 := by decide
  have a7 : ∀ a : Fin 5, a + 2 + 2 = a + 4 := by decide
  have a8 : ∀ a : Fin 5, a + 3 + 2 = a := by decide
  have a9 : ∀ a : Fin 5, a + 4 + 2 = a + 1 := by decide
  have a10 : ∀ a : Fin 5, a + 1 - 1 = a := by decide
  have a11 : ∀ a : Fin 5, a + 2 - 1 = a + 1 := by decide
  have a12 : ∀ a : Fin 5, a + 3 - 1 = a + 2 := by decide
  have a13 : ∀ a : Fin 5, a + 4 - 1 = a + 3 := by decide
  have icases : ∀ a b : Fin 5, b = a ∨ b = a + 1 ∨ b = a + 2 ∨ b = a + 3 ∨ b = a + 4 := by decide
  have jcases : ∀ a b : Fin 5, b ≠ a → b = a + 1 ∨ b = a + 2 ∨ b = a + 3 ∨ b = a + 4 := by decide
  have q01 : ∀ a : Fin 5, a ≠ a + 1 := by decide
  have q02 : ∀ a : Fin 5, a ≠ a + 2 := by decide
  have q03 : ∀ a : Fin 5, a ≠ a + 3 := by decide
  have q04 : ∀ a : Fin 5, a ≠ a + 4 := by decide
  have q10 : ∀ a : Fin 5, a + 1 ≠ a := by decide
  have q12 : ∀ a : Fin 5, a + 1 ≠ a + 2 := by decide
  have q13 : ∀ a : Fin 5, a + 1 ≠ a + 3 := by decide
  have q14 : ∀ a : Fin 5, a + 1 ≠ a + 4 := by decide
  have q20 : ∀ a : Fin 5, a + 2 ≠ a := by decide
  have q21 : ∀ a : Fin 5, a + 2 ≠ a + 1 := by decide
  have q23 : ∀ a : Fin 5, a + 2 ≠ a + 3 := by decide
  have q24 : ∀ a : Fin 5, a + 2 ≠ a + 4 := by decide
  have q30 : ∀ a : Fin 5, a + 3 ≠ a := by decide
  have q31 : ∀ a : Fin 5, a + 3 ≠ a + 1 := by decide
  have q32 : ∀ a : Fin 5, a + 3 ≠ a + 2 := by decide
  have q34 : ∀ a : Fin 5, a + 3 ≠ a + 4 := by decide
  have q40 : ∀ a : Fin 5, a + 4 ≠ a := by decide
  have q41 : ∀ a : Fin 5, a + 4 ≠ a + 1 := by decide
  have q42 : ∀ a : Fin 5, a + 4 ≠ a + 2 := by decide
  have q43 : ∀ a : Fin 5, a + 4 ≠ a + 3 := by decide
  obtain ⟨jx, hjx, hIX⟩ := hX
  obtain ⟨jy, hjy, hIY⟩ := hY
  have mA : (P i) ∈ S := hPS i
  have mB : (P (i + 1)) ∈ S := hPS (i + 1)
  have mC : (P (i + 2)) ∈ S := hPS (i + 2)
  have mD : (P (i + 3)) ∈ S := hPS (i + 3)
  have mE : (P (i + 4)) ∈ S := hPS (i + 4)
  have mM : M ∈ S := hMS
  have mQ : Q ∈ S := (hS Q).2 (Or.inr (Or.inr (Or.inl rfl)))
  have mS3 : S3 ∈ S := (hS S3).2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have mX : X ∈ S := (hS X).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have mY : Y ∈ S := (hS Y).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have neAB : (P i) ≠ (P (i + 1)) := hinj.ne (q01 i)
  have neAC : (P i) ≠ (P (i + 2)) := hinj.ne (q02 i)
  have neAD : (P i) ≠ (P (i + 3)) := hinj.ne (q03 i)
  have neAE : (P i) ≠ (P (i + 4)) := hinj.ne (q04 i)
  have neBC : (P (i + 1)) ≠ (P (i + 2)) := hinj.ne (q12 i)
  have neBD : (P (i + 1)) ≠ (P (i + 3)) := hinj.ne (q13 i)
  have neBE : (P (i + 1)) ≠ (P (i + 4)) := hinj.ne (q14 i)
  have neCD : (P (i + 2)) ≠ (P (i + 3)) := hinj.ne (q23 i)
  have neCE : (P (i + 2)) ≠ (P (i + 4)) := hinj.ne (q24 i)
  have neDE : (P (i + 3)) ≠ (P (i + 4)) := hinj.ne (q34 i)
  have bABC : 0 < orient (P i) (P (i + 1)) (P (i + 2)) := hccw i (i + 2) (q20 i) (q21 i)
  have bABD : 0 < orient (P i) (P (i + 1)) (P (i + 3)) := hccw i (i + 3) (q30 i) (q31 i)
  have bABE : 0 < orient (P i) (P (i + 1)) (P (i + 4)) := hccw i (i + 4) (q40 i) (q41 i)
  have bACD : 0 < orient (P i) (P (i + 2)) (P (i + 3)) := by
    have h := hccw (i + 2) i (q02 i) (by rw [a2 i]; exact q03 i)
    rw [a2 i] at h
    linarith [orient_cyc (P i) (P (i + 2)) (P (i + 3))]
  have bACE : 0 < orient (P i) (P (i + 2)) (P (i + 4)) := by
    have h := hccw (i + 4) (i + 2) (q24 i) (by rw [a4 i]; exact q20 i)
    rw [a4 i] at h
    linarith [orient_cyc (P i) (P (i + 2)) (P (i + 4)), orient_cyc (P (i + 2)) (P (i + 4)) (P i)]
  have bADE : 0 < orient (P i) (P (i + 3)) (P (i + 4)) := by
    have h := hccw (i + 3) i (q03 i) (by rw [a3 i]; exact q04 i)
    rw [a3 i] at h
    linarith [orient_cyc (P i) (P (i + 3)) (P (i + 4))]
  have bBCD : 0 < orient (P (i + 1)) (P (i + 2)) (P (i + 3)) := by
    have h := hccw (i + 1) (i + 3) (q31 i) (by rw [a1 i]; exact q32 i)
    rwa [a1 i] at h
  have bBCE : 0 < orient (P (i + 1)) (P (i + 2)) (P (i + 4)) := by
    have h := hccw (i + 1) (i + 4) (q41 i) (by rw [a1 i]; exact q42 i)
    rwa [a1 i] at h
  have bBDE : 0 < orient (P (i + 1)) (P (i + 3)) (P (i + 4)) := by
    have h := hccw (i + 3) (i + 1) (q13 i) (by rw [a3 i]; exact q14 i)
    rw [a3 i] at h
    linarith [orient_cyc (P (i + 1)) (P (i + 3)) (P (i + 4))]
  have bCDE : 0 < orient (P (i + 2)) (P (i + 3)) (P (i + 4)) := by
    have h := hccw (i + 2) (i + 4) (q42 i) (by rw [a2 i]; exact q43 i)
    rwa [a2 i] at h
  have hE := orient_edge_pos_of_mem_interior P M hM hccw
  have bABM : 0 < orient (P i) (P (i + 1)) M := hE i
  have bBCM : 0 < orient (P (i + 1)) (P (i + 2)) M := by have h := hE (i + 1); rwa [a1 i] at h
  have bCDM : 0 < orient (P (i + 2)) (P (i + 3)) M := by have h := hE (i + 2); rwa [a2 i] at h
  have bDEM : 0 < orient (P (i + 3)) (P (i + 4)) M := by have h := hE (i + 3); rwa [a3 i] at h
  have bAEM : orient (P i) (P (i + 4)) M < 0 := by
    have h := hE (i + 4); rw [a4 i] at h
    have e : orient (P i) (P (i + 4)) M = -orient (P (i + 4)) (P i) M := by unfold orient; ring
    linarith
  have bACM : 0 < orient (P i) (P (i + 2)) M := hcore i
  have bBDM : 0 < orient (P (i + 1)) (P (i + 3)) M := by have h := hcore (i + 1); rwa [a6 i] at h
  have bCEM : 0 < orient (P (i + 2)) (P (i + 4)) M := by have h := hcore (i + 2); rwa [a7 i] at h
  have bADM : orient (P i) (P (i + 3)) M < 0 := by
    have h := hcore (i + 3); rw [a8 i] at h
    have e : orient (P i) (P (i + 3)) M = -orient (P (i + 3)) (P i) M := by unfold orient; ring
    linarith
  have bBEM : orient (P (i + 1)) (P (i + 4)) M < 0 := by
    have h := hcore (i + 4); rw [a9 i] at h
    have e : orient (P (i + 1)) (P (i + 4)) M = -orient (P (i + 4)) (P (i + 1)) M := by unfold orient; ring
    linarith
  obtain ⟨Q1, Q2, Q3, Q4, Q5⟩ := id hQ
  rw [a5 i] at Q4
  have bAMQ : orient (P i) M Q < 0 := by
    have e : orient (P i) M Q = -orient M (P i) Q := by unfold orient; ring
    linarith [Q1]
  have bBMQ : 0 < orient (P (i + 1)) M Q := by
    have e : orient (P (i + 1)) M Q = -orient M (P (i + 1)) Q := by unfold orient; ring
    linarith [Q2]
  have bABQ : orient (P i) (P (i + 1)) Q < 0 := Q3
  have bAEQ : 0 < orient (P i) (P (i + 4)) Q := by
    have e : orient (P i) (P (i + 4)) Q = -orient (P (i + 4)) (P i) Q := by unfold orient; ring
    linarith [Q4]
  have bBCQ : orient (P (i + 1)) (P (i + 2)) Q < 0 := Q5
  obtain ⟨SS1, SS2, SS3, SS4, SS5⟩ := id hS3
  rw [a5 i] at SS4
  have bAMS : orient (P i) M S3 < 0 := by
    have e : orient (P i) M S3 = -orient M (P i) S3 := by unfold orient; ring
    linarith [SS1]
  have bBMS : 0 < orient (P (i + 1)) M S3 := by
    have e : orient (P (i + 1)) M S3 = -orient M (P (i + 1)) S3 := by unfold orient; ring
    linarith [SS2]
  have bABS : orient (P i) (P (i + 1)) S3 < 0 := SS3
  have bAES : 0 < orient (P i) (P (i + 4)) S3 := by
    have e : orient (P i) (P (i + 4)) S3 = -orient (P (i + 4)) (P i) S3 := by unfold orient; ring
    linarith [SS4]
  have bBCS : orient (P (i + 1)) (P (i + 2)) S3 < 0 := SS5
  obtain ⟨hC1, hC2⟩ := hC
  have bAQS : orient (P i) Q S3 < 0 := by
    have e : orient (P i) Q S3 = -orient Q (P i) S3 := by unfold orient; ring
    linarith
  have bBQS : 0 < orient (P (i + 1)) Q S3 := hC2
  have hMP : ∀ k : Fin 5, M ≠ P k := by
    intro k h
    have h' := hE k
    rw [h, orient_self_left] at h'
    exact lt_irrefl _ h'
  have neAM : (P i) ≠ M := (hMP i).symm
  have neBM : (P (i + 1)) ≠ M := (hMP (i + 1)).symm
  have neCM : (P (i + 2)) ≠ M := (hMP (i + 2)).symm
  have neDM : (P (i + 3)) ≠ M := (hMP (i + 3)).symm
  have neEM : (P (i + 4)) ≠ M := (hMP (i + 4)).symm
  have nQP : ∀ k : Fin 5, Q ≠ P k := ne_vertex_of_inB P hccw M i Q hQ
  have nSP : ∀ k : Fin 5, S3 ≠ P k := ne_vertex_of_inB P hccw M i S3 hS3
  have neAQ : (P i) ≠ Q := (nQP i).symm
  have neAS3 : (P i) ≠ S3 := (nSP i).symm
  have neBQ : (P (i + 1)) ≠ Q := (nQP (i + 1)).symm
  have neBS3 : (P (i + 1)) ≠ S3 := (nSP (i + 1)).symm
  have neCQ : (P (i + 2)) ≠ Q := (nQP (i + 2)).symm
  have neCS3 : (P (i + 2)) ≠ S3 := (nSP (i + 2)).symm
  have neDQ : (P (i + 3)) ≠ Q := (nQP (i + 3)).symm
  have neDS3 : (P (i + 3)) ≠ S3 := (nSP (i + 3)).symm
  have neEQ : (P (i + 4)) ≠ Q := (nQP (i + 4)).symm
  have neES3 : (P (i + 4)) ≠ S3 := (nSP (i + 4)).symm
  have neMQ : M ≠ Q := by
    intro h; rw [← h, orient_self_left] at Q1; exact lt_irrefl _ Q1
  have neMS3 : M ≠ S3 := by
    intro h; rw [← h, orient_self_left] at SS1; exact lt_irrefl _ SS1
  have neQS3 : Q ≠ S3 := hQS3
  set pp1 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 2)), (P (i + 3)), Q] with hpp1
  have gg1 : IndexedGP pp1 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) Q mA mB mC mD mQ neAB neAC neAD neAQ neBC neBD neBQ neCD neCQ neDQ
    simpa [hpp1] using h
  have bACQ : orient (P i) (P (i + 2)) Q < 0 := by
    have h := sign_imp_neg [(0, 1, 2, true), (0, 1, 4, false), (1, 2, 4, false)] 0 2 4 (by decide +kernel) pp1 gg1
      (litHolds_cons (litHolds_pos pp1 0 1 2 (by simpa [hpp1] using bABC)) (litHolds_cons (litHolds_neg pp1 0 1 4 (by simpa [hpp1] using bABQ)) (litHolds_cons (litHolds_neg pp1 1 2 4 (by simpa [hpp1] using bBCQ)) (litHolds_nil pp1))))
    simpa [hpp1] using h
  set pp2 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 2)), (P (i + 3)), S3] with hpp2
  have gg2 : IndexedGP pp2 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) S3 mA mB mC mD mS3 neAB neAC neAD neAS3 neBC neBD neBS3 neCD neCS3 neDS3
    simpa [hpp2] using h
  have bACS : orient (P i) (P (i + 2)) S3 < 0 := by
    have h := sign_imp_neg [(0, 1, 2, true), (0, 1, 4, false), (1, 2, 4, false)] 0 2 4 (by decide +kernel) pp2 gg2
      (litHolds_cons (litHolds_pos pp2 0 1 2 (by simpa [hpp2] using bABC)) (litHolds_cons (litHolds_neg pp2 0 1 4 (by simpa [hpp2] using bABS)) (litHolds_cons (litHolds_neg pp2 1 2 4 (by simpa [hpp2] using bBCS)) (litHolds_nil pp2))))
    simpa [hpp2] using h
  set pp3 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 2)), (P (i + 4)), Q] with hpp3
  have gg3 : IndexedGP pp3 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 4)) Q mA mB mC mE mQ neAB neAC neAE neAQ neBC neBE neBQ neCE neCQ neEQ
    simpa [hpp3] using h
  have bBEQ : 0 < orient (P (i + 1)) (P (i + 4)) Q := by
    have h := sign_imp_pos [(0, 2, 3, true), (0, 1, 4, false), (0, 3, 4, true), (1, 2, 4, false), (0, 2, 4, false)] 1 3 4 (by decide +kernel) pp3 gg3
      (litHolds_cons (litHolds_pos pp3 0 2 3 (by simpa [hpp3] using bACE)) (litHolds_cons (litHolds_neg pp3 0 1 4 (by simpa [hpp3] using bABQ)) (litHolds_cons (litHolds_pos pp3 0 3 4 (by simpa [hpp3] using bAEQ)) (litHolds_cons (litHolds_neg pp3 1 2 4 (by simpa [hpp3] using bBCQ)) (litHolds_cons (litHolds_neg pp3 0 2 4 (by simpa [hpp3] using bACQ)) (litHolds_nil pp3))))))
    simpa [hpp3] using h
  set pp4 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 2)), (P (i + 4)), S3] with hpp4
  have gg4 : IndexedGP pp4 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 4)) S3 mA mB mC mE mS3 neAB neAC neAE neAS3 neBC neBE neBS3 neCE neCS3 neES3
    simpa [hpp4] using h
  have bBES : 0 < orient (P (i + 1)) (P (i + 4)) S3 := by
    have h := sign_imp_pos [(0, 2, 3, true), (0, 1, 4, false), (0, 3, 4, true), (1, 2, 4, false), (0, 2, 4, false)] 1 3 4 (by decide +kernel) pp4 gg4
      (litHolds_cons (litHolds_pos pp4 0 2 3 (by simpa [hpp4] using bACE)) (litHolds_cons (litHolds_neg pp4 0 1 4 (by simpa [hpp4] using bABS)) (litHolds_cons (litHolds_pos pp4 0 3 4 (by simpa [hpp4] using bAES)) (litHolds_cons (litHolds_neg pp4 1 2 4 (by simpa [hpp4] using bBCS)) (litHolds_cons (litHolds_neg pp4 0 2 4 (by simpa [hpp4] using bACS)) (litHolds_nil pp4))))))
    simpa [hpp4] using h
  have bCEQ : 0 < orient (P (i + 2)) (P (i + 4)) Q := by
    have h := sign_imp_pos [(1, 2, 3, true), (1, 2, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp3 gg3
      (litHolds_cons (litHolds_pos pp3 1 2 3 (by simpa [hpp3] using bBCE)) (litHolds_cons (litHolds_neg pp3 1 2 4 (by simpa [hpp3] using bBCQ)) (litHolds_cons (litHolds_pos pp3 1 3 4 (by simpa [hpp3] using bBEQ)) (litHolds_nil pp3))))
    simpa [hpp3] using h
  have bCES : 0 < orient (P (i + 2)) (P (i + 4)) S3 := by
    have h := sign_imp_pos [(1, 2, 3, true), (1, 2, 4, false), (1, 3, 4, true)] 2 3 4 (by decide +kernel) pp4 gg4
      (litHolds_cons (litHolds_pos pp4 1 2 3 (by simpa [hpp4] using bBCE)) (litHolds_cons (litHolds_neg pp4 1 2 4 (by simpa [hpp4] using bBCS)) (litHolds_cons (litHolds_pos pp4 1 3 4 (by simpa [hpp4] using bBES)) (litHolds_nil pp4))))
    simpa [hpp4] using h
  set pp5 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 2)), M, Q] with hpp5
  have gg5 : IndexedGP pp5 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 2)) M Q mA mB mC mM mQ neAB neAC neAM neAQ neBC neBM neBQ neCM neCQ neMQ
    simpa [hpp5] using h
  have bCMQ : 0 < orient (P (i + 2)) M Q := by
    have h := sign_imp_pos [(0, 3, 4, false), (1, 3, 4, true), (0, 1, 4, false), (1, 2, 4, false), (0, 2, 4, false)] 2 3 4 (by decide +kernel) pp5 gg5
      (litHolds_cons (litHolds_neg pp5 0 3 4 (by simpa [hpp5] using bAMQ)) (litHolds_cons (litHolds_pos pp5 1 3 4 (by simpa [hpp5] using bBMQ)) (litHolds_cons (litHolds_neg pp5 0 1 4 (by simpa [hpp5] using bABQ)) (litHolds_cons (litHolds_neg pp5 1 2 4 (by simpa [hpp5] using bBCQ)) (litHolds_cons (litHolds_neg pp5 0 2 4 (by simpa [hpp5] using bACQ)) (litHolds_nil pp5))))))
    simpa [hpp5] using h
  set pp6 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 2)), M, S3] with hpp6
  have gg6 : IndexedGP pp6 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 2)) M S3 mA mB mC mM mS3 neAB neAC neAM neAS3 neBC neBM neBS3 neCM neCS3 neMS3
    simpa [hpp6] using h
  have bCMS : 0 < orient (P (i + 2)) M S3 := by
    have h := sign_imp_pos [(0, 3, 4, false), (1, 3, 4, true), (0, 1, 4, false), (1, 2, 4, false), (0, 2, 4, false)] 2 3 4 (by decide +kernel) pp6 gg6
      (litHolds_cons (litHolds_neg pp6 0 3 4 (by simpa [hpp6] using bAMS)) (litHolds_cons (litHolds_pos pp6 1 3 4 (by simpa [hpp6] using bBMS)) (litHolds_cons (litHolds_neg pp6 0 1 4 (by simpa [hpp6] using bABS)) (litHolds_cons (litHolds_neg pp6 1 2 4 (by simpa [hpp6] using bBCS)) (litHolds_cons (litHolds_neg pp6 0 2 4 (by simpa [hpp6] using bACS)) (litHolds_nil pp6))))))
    simpa [hpp6] using h
  set pp7 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 2)), Q, S3] with hpp7
  have gg7 : IndexedGP pp7 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 2)) Q S3 mA mB mC mQ mS3 neAB neAC neAQ neAS3 neBC neBQ neBS3 neCQ neCS3 neQS3
    simpa [hpp7] using h
  have bCQS : 0 < orient (P (i + 2)) Q S3 := by
    have h := sign_imp_pos [(0, 1, 4, false), (1, 2, 4, false), (0, 3, 4, false), (1, 3, 4, true), (0, 2, 4, false)] 2 3 4 (by decide +kernel) pp7 gg7
      (litHolds_cons (litHolds_neg pp7 0 1 4 (by simpa [hpp7] using bABS)) (litHolds_cons (litHolds_neg pp7 1 2 4 (by simpa [hpp7] using bBCS)) (litHolds_cons (litHolds_neg pp7 0 3 4 (by simpa [hpp7] using bAQS)) (litHolds_cons (litHolds_pos pp7 1 3 4 (by simpa [hpp7] using bBQS)) (litHolds_cons (litHolds_neg pp7 0 2 4 (by simpa [hpp7] using bACS)) (litHolds_nil pp7))))))
    simpa [hpp7] using h
  set pp8 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 4)), M, Q] with hpp8
  have gg8 : IndexedGP pp8 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 4)) M Q mA mB mE mM mQ neAB neAE neAM neAQ neBE neBM neBQ neEM neEQ neMQ
    simpa [hpp8] using h
  have bEMQ : orient (P (i + 4)) M Q < 0 := by
    have h := sign_imp_neg [(0, 3, 4, false), (1, 3, 4, true), (0, 1, 4, false), (0, 2, 4, true), (1, 2, 4, true)] 2 3 4 (by decide +kernel) pp8 gg8
      (litHolds_cons (litHolds_neg pp8 0 3 4 (by simpa [hpp8] using bAMQ)) (litHolds_cons (litHolds_pos pp8 1 3 4 (by simpa [hpp8] using bBMQ)) (litHolds_cons (litHolds_neg pp8 0 1 4 (by simpa [hpp8] using bABQ)) (litHolds_cons (litHolds_pos pp8 0 2 4 (by simpa [hpp8] using bAEQ)) (litHolds_cons (litHolds_pos pp8 1 2 4 (by simpa [hpp8] using bBEQ)) (litHolds_nil pp8))))))
    simpa [hpp8] using h
  set pp9 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 4)), M, S3] with hpp9
  have gg9 : IndexedGP pp9 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 4)) M S3 mA mB mE mM mS3 neAB neAE neAM neAS3 neBE neBM neBS3 neEM neES3 neMS3
    simpa [hpp9] using h
  have bEMS : orient (P (i + 4)) M S3 < 0 := by
    have h := sign_imp_neg [(0, 3, 4, false), (1, 3, 4, true), (0, 1, 4, false), (0, 2, 4, true), (1, 2, 4, true)] 2 3 4 (by decide +kernel) pp9 gg9
      (litHolds_cons (litHolds_neg pp9 0 3 4 (by simpa [hpp9] using bAMS)) (litHolds_cons (litHolds_pos pp9 1 3 4 (by simpa [hpp9] using bBMS)) (litHolds_cons (litHolds_neg pp9 0 1 4 (by simpa [hpp9] using bABS)) (litHolds_cons (litHolds_pos pp9 0 2 4 (by simpa [hpp9] using bAES)) (litHolds_cons (litHolds_pos pp9 1 2 4 (by simpa [hpp9] using bBES)) (litHolds_nil pp9))))))
    simpa [hpp9] using h
  set pp10 : Fin 5 → Point := ![(P i), (P (i + 1)), (P (i + 4)), Q, S3] with hpp10
  have gg10 : IndexedGP pp10 := by
    have h := indexedGP_vec5 S hgp (P i) (P (i + 1)) (P (i + 4)) Q S3 mA mB mE mQ mS3 neAB neAE neAQ neAS3 neBE neBQ neBS3 neEQ neES3 neQS3
    simpa [hpp10] using h
  have bEQS : orient (P (i + 4)) Q S3 < 0 := by
    have h := sign_imp_neg [(0, 1, 4, false), (0, 2, 4, true), (0, 3, 4, false), (1, 3, 4, true), (1, 2, 4, true)] 2 3 4 (by decide +kernel) pp10 gg10
      (litHolds_cons (litHolds_neg pp10 0 1 4 (by simpa [hpp10] using bABS)) (litHolds_cons (litHolds_pos pp10 0 2 4 (by simpa [hpp10] using bAES)) (litHolds_cons (litHolds_neg pp10 0 3 4 (by simpa [hpp10] using bAQS)) (litHolds_cons (litHolds_pos pp10 1 3 4 (by simpa [hpp10] using bBQS)) (litHolds_cons (litHolds_pos pp10 1 2 4 (by simpa [hpp10] using bBES)) (litHolds_nil pp10))))))
    simpa [hpp10] using h
  have mCQ : orient M (P (i + 2)) Q < 0 := by
    have e : orient M (P (i + 2)) Q = -orient (P (i + 2)) M Q := by unfold orient; ring
    linarith [bCMQ]
  have mEQ : 0 < orient M (P (i + 4)) Q := by
    have e : orient M (P (i + 4)) Q = -orient (P (i + 4)) M Q := by unfold orient; ring
    linarith [bEMQ]
  have mCS : orient M (P (i + 2)) S3 < 0 := by
    have e : orient M (P (i + 2)) S3 = -orient (P (i + 2)) M S3 := by unfold orient; ring
    linarith [bCMS]
  have mES : 0 < orient M (P (i + 4)) S3 := by
    have e : orient M (P (i + 4)) S3 = -orient (P (i + 4)) M S3 := by unfold orient; ring
    linarith [bEMS]
  have nXP : ∀ k : Fin 5, X ≠ P k := ne_vertex_of_inB P hccw M jx X hIX
  have neAX : (P i) ≠ X := (nXP i).symm
  have neBX : (P (i + 1)) ≠ X := (nXP (i + 1)).symm
  have neCX : (P (i + 2)) ≠ X := (nXP (i + 2)).symm
  have neDX : (P (i + 3)) ≠ X := (nXP (i + 3)).symm
  have neEX : (P (i + 4)) ≠ X := (nXP (i + 4)).symm
  have neMX : M ≠ X := by
    intro h; have u := hIX.1; rw [← h, orient_self_left] at u; exact lt_irrefl _ u
  have neQX : Q ≠ X := by
    intro h
    rcases jcases i jx hjx with rfl | rfl | rfl | rfl
    · have u := hIX.1; rw [← h] at u; linarith [Q2]
    · have u := hIX.1; rw [← h] at u; linarith [mCQ]
    · have u := hIX.2.1; rw [a3 i] at u; rw [← h] at u; linarith [mEQ]
    · have u := hIX.2.1; rw [a4 i] at u; rw [← h] at u; linarith [Q1]
  have neS3X : S3 ≠ X := by
    intro h
    rcases jcases i jx hjx with rfl | rfl | rfl | rfl
    · have u := hIX.1; rw [← h] at u; linarith [SS2]
    · have u := hIX.1; rw [← h] at u; linarith [mCS]
    · have u := hIX.2.1; rw [a3 i] at u; rw [← h] at u; linarith [mES]
    · have u := hIX.2.1; rw [a4 i] at u; rw [← h] at u; linarith [SS1]
  have nYP : ∀ k : Fin 5, Y ≠ P k := ne_vertex_of_inB P hccw M jy Y hIY
  have neAY : (P i) ≠ Y := (nYP i).symm
  have neBY : (P (i + 1)) ≠ Y := (nYP (i + 1)).symm
  have neCY : (P (i + 2)) ≠ Y := (nYP (i + 2)).symm
  have neDY : (P (i + 3)) ≠ Y := (nYP (i + 3)).symm
  have neEY : (P (i + 4)) ≠ Y := (nYP (i + 4)).symm
  have neMY : M ≠ Y := by
    intro h; have u := hIY.1; rw [← h, orient_self_left] at u; exact lt_irrefl _ u
  have neQY : Q ≠ Y := by
    intro h
    rcases jcases i jy hjy with rfl | rfl | rfl | rfl
    · have u := hIY.1; rw [← h] at u; linarith [Q2]
    · have u := hIY.1; rw [← h] at u; linarith [mCQ]
    · have u := hIY.2.1; rw [a3 i] at u; rw [← h] at u; linarith [mEQ]
    · have u := hIY.2.1; rw [a4 i] at u; rw [← h] at u; linarith [Q1]
  have neS3Y : S3 ≠ Y := by
    intro h
    rcases jcases i jy hjy with rfl | rfl | rfl | rfl
    · have u := hIY.1; rw [← h] at u; linarith [SS2]
    · have u := hIY.1; rw [← h] at u; linarith [mCS]
    · have u := hIY.2.1; rw [a3 i] at u; rw [← h] at u; linarith [mES]
    · have u := hIY.2.1; rw [a4 i] at u; rw [← h] at u; linarith [SS1]
  have neXY : X ≠ Y := hXY
  have hregX : RegA M (P (i + 1)) (P (i + 2)) (P i) (P (i + 3)) X ∨
      RegA M (P (i + 2)) (P (i + 3)) (P (i + 1)) (P (i + 4)) X ∨
      RegA M (P (i + 3)) (P (i + 4)) (P (i + 2)) (P i) X ∨
      RegA M (P (i + 4)) (P i) (P (i + 3)) (P (i + 1)) X := by
    rcases jcases i jx hjx with rfl | rfl | rfl | rfl
    · obtain ⟨u1, u2, u3, u4, u5⟩ := hIX
      rw [a1 i] at u2 u3
      rw [a10 i] at u4
      rw [a1 i, a6 i] at u5
      exact Or.inl ⟨u1, u2, u3, u4, u5⟩
    · obtain ⟨u1, u2, u3, u4, u5⟩ := hIX
      rw [a2 i] at u2 u3
      rw [a11 i] at u4
      rw [a2 i, a7 i] at u5
      exact Or.inr (Or.inl ⟨u1, u2, u3, u4, u5⟩)
    · obtain ⟨u1, u2, u3, u4, u5⟩ := hIX
      rw [a3 i] at u2 u3
      rw [a12 i] at u4
      rw [a3 i, a8 i] at u5
      exact Or.inr (Or.inr (Or.inl ⟨u1, u2, u3, u4, u5⟩))
    · obtain ⟨u1, u2, u3, u4, u5⟩ := hIX
      rw [a4 i] at u2 u3
      rw [a13 i] at u4
      rw [a4 i, a9 i] at u5
      exact Or.inr (Or.inr (Or.inr ⟨u1, u2, u3, u4, u5⟩))
  have hregY : RegA M (P (i + 1)) (P (i + 2)) (P i) (P (i + 3)) Y ∨
      RegA M (P (i + 2)) (P (i + 3)) (P (i + 1)) (P (i + 4)) Y ∨
      RegA M (P (i + 3)) (P (i + 4)) (P (i + 2)) (P i) Y ∨
      RegA M (P (i + 4)) (P i) (P (i + 3)) (P (i + 1)) Y := by
    rcases jcases i jy hjy with rfl | rfl | rfl | rfl
    · obtain ⟨u1, u2, u3, u4, u5⟩ := hIY
      rw [a1 i] at u2 u3
      rw [a10 i] at u4
      rw [a1 i, a6 i] at u5
      exact Or.inl ⟨u1, u2, u3, u4, u5⟩
    · obtain ⟨u1, u2, u3, u4, u5⟩ := hIY
      rw [a2 i] at u2 u3
      rw [a11 i] at u4
      rw [a2 i, a7 i] at u5
      exact Or.inr (Or.inl ⟨u1, u2, u3, u4, u5⟩)
    · obtain ⟨u1, u2, u3, u4, u5⟩ := hIY
      rw [a3 i] at u2 u3
      rw [a12 i] at u4
      rw [a3 i, a8 i] at u5
      exact Or.inr (Or.inr (Or.inl ⟨u1, u2, u3, u4, u5⟩))
    · obtain ⟨u1, u2, u3, u4, u5⟩ := hIY
      rw [a4 i] at u2 u3
      rw [a13 i] at u4
      rw [a4 i, a9 i] at u5
      exact Or.inr (Or.inr (Or.inr ⟨u1, u2, u3, u4, u5⟩))
  have hRegAllX : RegAll (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 X :=
    regAll_of_reg S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 X mA mB mC mD mE mM mQ mS3 mX neAB neAC neAD neAE neAM neAQ neAS3 neAX neBC neBD neBE neBM neBQ neBS3 neBX neCD neCE neCM neCQ neCS3 neCX neDE neDM neDQ neDS3 neDX neEM neEQ neES3 neEX neMQ neMS3 neMX neQS3 neQX neS3X bABC bABD bABE bACD bACE bADE bBCD bBCE bBDE bCDE bABM bBCM bCDM bDEM bAEM bACM bBDM bCEM bADM bBEM bAMQ bBMQ bABQ bAEQ bBCQ bAMS bBMS bABS bAES bBCS bAQS bBQS bACQ bACS bBEQ bBES bCEQ bCES bCMQ bCMS bCQS bEMQ bEMS bEQS hregX
  have hRegAllY : RegAll (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 Y :=
    regAll_of_reg S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 Y mA mB mC mD mE mM mQ mS3 mY neAB neAC neAD neAE neAM neAQ neAS3 neAY neBC neBD neBE neBM neBQ neBS3 neBY neCD neCE neCM neCQ neCS3 neCY neDE neDM neDQ neDS3 neDY neEM neEQ neES3 neEY neMQ neMS3 neMY neQS3 neQY neS3Y bABC bABD bABE bACD bACE bADE bBCD bBCE bBDE bCDE bABM bBCM bCDM bDEM bAEM bACM bBDM bCEM bADM bBEM bAMQ bBMQ bABQ bAEQ bBCQ bAMS bBMS bABS bAES bBCS bAQS bBQS bACQ bACS bBEQ bBES bCEQ bCES bCMQ bCMS bCQS bEMQ bEMS bEQS hregY
  have hSall : ∀ q ∈ S, q = (P i) ∨ q = (P (i + 1)) ∨ q = (P (i + 2)) ∨ q = (P (i + 3)) ∨ q = (P (i + 4)) ∨ q = M ∨ q = Q ∨ q = S3 ∨ q = X ∨ q = Y := by
    intro q hq
    rcases (hS q).1 hq with ⟨j, rfl⟩ | h | h | h | h | h
    · rcases icases i j with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))
  have hSallYX : ∀ q ∈ S, q = (P i) ∨ q = (P (i + 1)) ∨ q = (P (i + 2)) ∨ q = (P (i + 3)) ∨ q = (P (i + 4)) ∨ q = M ∨ q = Q ∨ q = S3 ∨ q = Y ∨ q = X := by
    intro q hq
    rcases hSall q hq with h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  have hsame4 : RegA M (P (i + 4)) (P i) (P (i + 3)) (P (i + 1)) X → RegA M (P (i + 4)) (P i) (P (i + 3)) (P (i + 1)) Y →
      (0 < orient X (P (i + 4)) Y ∧ 0 < orient (P i) X Y) ∨ (0 < orient Y (P (i + 4)) X ∧ 0 < orient (P i) Y X) := by
    intro hx hy
    obtain ⟨x1, x2, x3, x4, x5⟩ := hx
    obtain ⟨y1, y2, y3, y4, y5⟩ := hy
    have iX : InB P M (i + 4) X :=
      ⟨x1, by rw [a4 i]; exact x2, by rw [a4 i]; exact x3, by rw [a13 i]; exact x4,
        by rw [a4 i, a9 i]; exact x5⟩
    have iY : InB P M (i + 4) Y :=
      ⟨y1, by rw [a4 i]; exact y2, by rw [a4 i]; exact y3, by rw [a13 i]; exact y4,
        by rw [a4 i, a9 i]; exact y5⟩
    have h := hsame (i + 4) iX iY
    rw [a4 i] at h
    rcases le_total (-orient (P (i + 4)) (P i) X) (-orient (P (i + 4)) (P i) Y) with hle | hle
    · exact Or.inl (h.1 hle)
    · exact Or.inr (h.2 hle)
  have hsame4' : RegA M (P (i + 4)) (P i) (P (i + 3)) (P (i + 1)) Y → RegA M (P (i + 4)) (P i) (P (i + 3)) (P (i + 1)) X →
      (0 < orient Y (P (i + 4)) X ∧ 0 < orient (P i) Y X) ∨ (0 < orient X (P (i + 4)) Y ∧ 0 < orient (P i) X Y) :=
    fun h1 h2 => (hsame4 h2 h1).symm
  have hsame1 : RegA M (P (i + 1)) (P (i + 2)) (P i) (P (i + 3)) X → RegA M (P (i + 1)) (P (i + 2)) (P i) (P (i + 3)) Y →
      (0 < orient X (P (i + 1)) Y ∧ 0 < orient (P (i + 2)) X Y) ∨ (0 < orient Y (P (i + 1)) X ∧ 0 < orient (P (i + 2)) Y X) := by
    intro hx hy
    obtain ⟨x1, x2, x3, x4, x5⟩ := hx
    obtain ⟨y1, y2, y3, y4, y5⟩ := hy
    have iX : InB P M (i + 1) X :=
      ⟨x1, by rw [a1 i]; exact x2, by rw [a1 i]; exact x3, by rw [a10 i]; exact x4,
        by rw [a1 i, a6 i]; exact x5⟩
    have iY : InB P M (i + 1) Y :=
      ⟨y1, by rw [a1 i]; exact y2, by rw [a1 i]; exact y3, by rw [a10 i]; exact y4,
        by rw [a1 i, a6 i]; exact y5⟩
    have h := hsame (i + 1) iX iY
    rw [a1 i] at h
    rcases le_total (-orient (P (i + 1)) (P (i + 2)) X) (-orient (P (i + 1)) (P (i + 2)) Y) with hle | hle
    · exact Or.inl (h.1 hle)
    · exact Or.inr (h.2 hle)
  have hsame1' : RegA M (P (i + 1)) (P (i + 2)) (P i) (P (i + 3)) Y → RegA M (P (i + 1)) (P (i + 2)) (P i) (P (i + 3)) X →
      (0 < orient Y (P (i + 1)) X ∧ 0 < orient (P (i + 2)) Y X) ∨ (0 < orient X (P (i + 1)) Y ∧ 0 < orient (P (i + 2)) X Y) :=
    fun h1 h2 => (hsame1 h2 h1).symm
  have hQSXne : orient Q S3 X ≠ 0 := hgp Q mQ S3 mS3 X mX neQS3 neQX neS3X
  have hQSYne : orient Q S3 Y ≠ 0 := hgp Q mQ S3 mS3 Y mY neQS3 neQY neS3Y
  have hSXYne : orient S3 X Y ≠ 0 := hgp S3 mS3 X mX Y mY neS3X neS3Y neXY
  rcases lt_or_gt_of_ne hQSXne with hx | hx
  · rcases lt_or_gt_of_ne hQSYne with hy | hy
    · rcases lt_or_gt_of_ne hSXYne with hs | hs
      · have hs' : 0 < orient S3 Y X := by
          have e : orient S3 Y X = -orient S3 X Y := by unfold orient; ring
          linarith
        exact two_RR S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 Y X mA mB mC mD mE mM mQ mS3 mY mX neAB neAC neAD neAE neAM neAQ neAS3 neAY neAX neBC neBD neBE neBM neBQ neBS3 neBY neBX neCD neCE neCM neCQ neCS3 neCY neCX neDE neDM neDQ neDS3 neDY neDX neEM neEQ neES3 neEY neEX neMQ neMS3 neMY neMX neQS3 neQY neQX neS3Y neS3X neXY.symm hSallYX bABC bABD bABE bACD bACE bADE bBCD bBCE bBDE bCDE bABM bBCM bCDM bDEM bAEM bACM bBDM bCEM bADM bBEM bAMQ bBMQ bABQ bAEQ bBCQ bAMS bBMS bABS bAES bBCS bAQS bBQS bACQ bACS bBEQ bBES bCEQ bCES bCMQ bCMS bCQS bEMQ bEMS bEQS hRegAllY hRegAllX hsame4' hy hx hs'
      · exact two_RR S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 X Y mA mB mC mD mE mM mQ mS3 mX mY neAB neAC neAD neAE neAM neAQ neAS3 neAX neAY neBC neBD neBE neBM neBQ neBS3 neBX neBY neCD neCE neCM neCQ neCS3 neCX neCY neDE neDM neDQ neDS3 neDX neDY neEM neEQ neES3 neEX neEY neMQ neMS3 neMX neMY neQS3 neQX neQY neS3X neS3Y neXY hSall bABC bABD bABE bACD bACE bADE bBCD bBCE bBDE bCDE bABM bBCM bCDM bDEM bAEM bACM bBDM bCEM bADM bBEM bAMQ bBMQ bABQ bAEQ bBCQ bAMS bBMS bABS bAES bBCS bAQS bBQS bACQ bACS bBEQ bBES bCEQ bCES bCMQ bCMS bCQS bEMQ bEMS bEQS hRegAllX hRegAllY hsame4 hx hy hs
    · exact two_MX S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 X Y mA mB mC mD mE mM mQ mS3 mX mY neAB neAC neAD neAE neAM neAQ neAS3 neAX neAY neBC neBD neBE neBM neBQ neBS3 neBX neBY neCD neCE neCM neCQ neCS3 neCX neCY neDE neDM neDQ neDS3 neDX neDY neEM neEQ neES3 neEX neEY neMQ neMS3 neMX neMY neQS3 neQX neQY neS3X neS3Y neXY hSall bABC bABD bABE bACD bACE bADE bBCD bBCE bBDE bCDE bABM bBCM bCDM bDEM bAEM bACM bBDM bCEM bADM bBEM bAMQ bBMQ bABQ bAEQ bBCQ bAMS bBMS bABS bAES bBCS bAQS bBQS bACQ bACS bBEQ bBES bCEQ bCES bCMQ bCMS bCQS bEMQ bEMS bEQS hRegAllX hRegAllY hx hy
  · rcases lt_or_gt_of_ne hQSYne with hy | hy
    · exact two_MX S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 Y X mA mB mC mD mE mM mQ mS3 mY mX neAB neAC neAD neAE neAM neAQ neAS3 neAY neAX neBC neBD neBE neBM neBQ neBS3 neBY neBX neCD neCE neCM neCQ neCS3 neCY neCX neDE neDM neDQ neDS3 neDY neDX neEM neEQ neES3 neEY neEX neMQ neMS3 neMY neMX neQS3 neQY neQX neS3Y neS3X neXY.symm hSallYX bABC bABD bABE bACD bACE bADE bBCD bBCE bBDE bCDE bABM bBCM bCDM bDEM bAEM bACM bBDM bCEM bADM bBEM bAMQ bBMQ bABQ bAEQ bBCQ bAMS bBMS bABS bAES bBCS bAQS bBQS bACQ bACS bBEQ bBES bCEQ bCES bCMQ bCMS bCQS bEMQ bEMS bEQS hRegAllY hRegAllX hy hx
    · rcases lt_or_gt_of_ne hSXYne with hs | hs
      · exact two_LL S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 X Y mA mB mC mD mE mM mQ mS3 mX mY neAB neAC neAD neAE neAM neAQ neAS3 neAX neAY neBC neBD neBE neBM neBQ neBS3 neBX neBY neCD neCE neCM neCQ neCS3 neCX neCY neDE neDM neDQ neDS3 neDX neDY neEM neEQ neES3 neEX neEY neMQ neMS3 neMX neMY neQS3 neQX neQY neS3X neS3Y neXY hSall bABC bABD bABE bACD bACE bADE bBCD bBCE bBDE bCDE bABM bBCM bCDM bDEM bAEM bACM bBDM bCEM bADM bBEM bAMQ bBMQ bABQ bAEQ bBCQ bAMS bBMS bABS bAES bBCS bAQS bBQS bACQ bACS bBEQ bBES bCEQ bCES bCMQ bCMS bCQS bEMQ bEMS bEQS hRegAllX hRegAllY hsame1 hx hy hs
      · have hs' : orient S3 Y X < 0 := by
          have e : orient S3 Y X = -orient S3 X Y := by unfold orient; ring
          linarith
        exact two_LL S hgp (P i) (P (i + 1)) (P (i + 2)) (P (i + 3)) (P (i + 4)) M Q S3 Y X mA mB mC mD mE mM mQ mS3 mY mX neAB neAC neAD neAE neAM neAQ neAS3 neAY neAX neBC neBD neBE neBM neBQ neBS3 neBY neBX neCD neCE neCM neCQ neCS3 neCY neCX neDE neDM neDQ neDS3 neDY neDX neEM neEQ neES3 neEY neEX neMQ neMS3 neMY neMX neQS3 neQY neQX neS3Y neS3X neXY.symm hSallYX bABC bABD bABE bACD bACE bADE bBCD bBCE bBDE bCDE bABM bBCM bCDM bDEM bAEM bACM bBDM bCEM bADM bBEM bAMQ bBMQ bABQ bAEQ bBCQ bAMS bBMS bABS bAES bBCS bAQS bBQS bACQ bACS bBEQ bBES bCEQ bCES bCMQ bCMS bCQS bEMQ bEMS bEQS hRegAllY hRegAllX hsame1' hy hx hs'


end Horton
