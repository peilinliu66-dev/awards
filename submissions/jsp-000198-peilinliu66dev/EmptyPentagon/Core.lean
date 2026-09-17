/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/Core.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import EmptyPentagon.Forces
import EmptyPentagon.Descent
import EmptyPentagon.CyclicLabel
import EmptyPentagon.Pentagon
import EmptyPentagon.Ear
import EmptyPentagon.Wedge
import EmptyPentagon.Front
import EmptyPentagon.Front2
import EmptyPentagon.Second
import EmptyPentagon.Third
import EmptyPentagon.Two
import EmptyPentagon.Final

noncomputable section
open Classical
namespace Horton

set_option maxHeartbeats 1000000 in
/-- Harborth's core case analysis: a ten-point set in general position containing a
counterclockwise convex pentagon `P` with at most one point of `S` strictly inside it has an
empty convex pentagon. -/
theorem exists_empty_pentagon_of_few_interior (S : Finset Point) (hcard : S.card = 10)
    (hgp : GeneralPosition S) (P : Fin 5 → Point) (hinj : Function.Injective P)
    (hPS : ∀ i, P i ∈ S)
    (hccw : ∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < orient (P i) (P (i + 1)) (P j))
    (hfew : (interiorPoints S (Finset.univ.image P)).card ≤ 1) :
    ∃ V : Finset Point, V.card = 5 ∧ EmptyConvexPolygon S V := by
  classical
  by_contra hcon
  -- (A) index arithmetic in `Fin 5`
  have a01 : ∀ a : Fin 5, a ≠ a + 1 := by decide
  have a02 : ∀ a : Fin 5, a ≠ a + 2 := by decide
  have a12 : ∀ a : Fin 5, a + 1 ≠ a + 2 := by decide
  have amne : ∀ a : Fin 5, a - 1 ≠ a := by decide
  -- (B) the pentagon vertex set
  have hFcard : (Finset.univ.image P : Finset Point).card = 5 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hmemF : ∀ q : Point, q ∈ (Finset.univ.image P : Finset Point) ↔ ∃ j, q = P j := by
    intro q
    constructor
    · intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      exact Finset.mem_image_of_mem P (Finset.mem_univ j)
  have hmemI : ∀ q : Point, q ∈ interiorPoints S (Finset.univ.image P) ↔
      (q ∈ S ∧
        q ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point))) := by
    intro q
    simp only [interiorPoints, Finset.mem_filter]
  rcases Nat.eq_zero_or_pos (interiorPoints S (Finset.univ.image P)).card with hz | hpos
  · -- (C) no interior point: the pentagon itself is empty
    refine hcon ⟨Finset.univ.image P, hFcard, emptyConvexPolygon_of_ccw S P hinj hPS hccw ?_⟩
    intro q hqS _ hqint
    have hq := (hmemI q).mpr ⟨hqS, hqint⟩
    rw [Finset.card_eq_zero] at hz
    rw [hz] at hq
    exact absurd hq (Finset.notMem_empty q)
  -- (D) exactly one interior point `M`
  have h1 : (interiorPoints S (Finset.univ.image P)).card = 1 := le_antisymm hfew hpos
  obtain ⟨M, hMeq⟩ := Finset.card_eq_one.mp h1
  have hMmem : M ∈ interiorPoints S (Finset.univ.image P) := by
    rw [hMeq]; exact Finset.mem_singleton_self M
  obtain ⟨hMS, hMint⟩ := (hmemI M).mp hMmem
  have huniq : ∀ q ∈ S,
      q ∈ interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)) → q = M := by
    intro q hqS hqint
    have hq := (hmemI q).mpr ⟨hqS, hqint⟩
    rw [hMeq] at hq
    exact Finset.mem_singleton.mp hq
  have hE := orient_edge_pos_of_mem_interior P M hMint hccw
  have hMP : ∀ j, M ≠ P j := by
    intro j hj
    have h := hE j
    rw [hj, orient_self_left] at h
    exact absurd h (lt_irrefl 0)
  -- (E) the ear case
  by_cases hear : ∃ i : Fin 5, 0 < orient (P (i + 2)) (P i) M
  · obtain ⟨i, hi⟩ := hear
    exact hcon (ear_case S P hinj hPS hccw M hMS hMint huniq i hi)
  push Not at hear
  have hcore : ∀ i : Fin 5, 0 < orient (P i) (P (i + 2)) M := by
    intro i
    have hh := hear i
    rw [orient_swap_line] at hh
    have hz2 : orient (P i) (P (i + 2)) M ≠ 0 :=
      hgp _ (hPS i) _ (hPS (i + 2)) _ hMS (hinj.ne (a02 i)) (Ne.symm (hMP i))
        (Ne.symm (hMP (i + 2)))
    rcases lt_or_gt_of_ne hz2 with h | h
    · linarith
    · exact h
  -- (F) a point beyond an edge is neither a vertex nor `M`
  have hqneP : ∀ (j : Fin 5) (q : Point), orient (P j) (P (j + 1)) q < 0 → ∀ k, q ≠ P k := by
    intro j q hq k hk
    rw [hk] at hq
    by_cases hk1 : k = j
    · rw [hk1, orient_self_left] at hq; exact absurd hq (lt_irrefl 0)
    by_cases hk2 : k = j + 1
    · rw [hk2, orient_self_right] at hq; exact absurd hq (lt_irrefl 0)
    · linarith [hccw j k hk1 hk2]
  have hqneM : ∀ (j : Fin 5) (q : Point), orient (P j) (P (j + 1)) q < 0 → q ≠ M := by
    intro j q hq h
    rw [h] at hq
    linarith [hE j]
  -- (G) the two front cases
  by_cases hf1 : ∃ (j : Fin 5) (R : Point), R ∈ S ∧ 0 < orient M (P j) R ∧
      orient M (P (j + 1)) R < 0 ∧ orient (P j) (P (j + 1)) R < 0 ∧
      0 < orient (P (j - 1)) (P j) R
  · obtain ⟨j, R, hRS, hw1, hw2, hw3, hw4⟩ := hf1
    exact hcon (front_case S hgp P hinj hPS hccw M hMS hMint huniq hcore j R hRS
      ⟨hw1, hw2, hw3⟩ hw4)
  by_cases hf2 : ∃ (j : Fin 5) (R : Point), R ∈ S ∧ 0 < orient M (P j) R ∧
      orient M (P (j + 1)) R < 0 ∧ orient (P j) (P (j + 1)) R < 0 ∧
      0 < orient (P (j + 1)) (P (j + 2)) R
  · obtain ⟨j, R, hRS, hw1, hw2, hw3, hw4⟩ := hf2
    exact hcon (front_case2 S hgp P hinj hPS hccw M hMS hMint huniq hcore j R hRS
      ⟨hw1, hw2, hw3⟩ hw4)
  push Not at hf1 hf2
  have hnofront : ∀ (j : Fin 5), ∀ q ∈ S, 0 < orient M (P j) q → orient M (P (j + 1)) q < 0 →
      orient (P j) (P (j + 1)) q < 0 →
      orient (P (j - 1)) (P j) q < 0 ∧ orient (P (j + 1)) (P (j + 2)) q < 0 := by
    intro j q hqS hw1 hw2 hw3
    have hne := hqneP j q hw3
    have hz1 : orient (P (j - 1)) (P j) q ≠ 0 :=
      hgp _ (hPS (j - 1)) _ (hPS j) _ hqS (hinj.ne (amne j)) (Ne.symm (hne (j - 1)))
        (Ne.symm (hne j))
    have hz2 : orient (P (j + 1)) (P (j + 2)) q ≠ 0 :=
      hgp _ (hPS (j + 1)) _ (hPS (j + 2)) _ hqS (hinj.ne (a12 j)) (Ne.symm (hne (j + 1)))
        (Ne.symm (hne (j + 2)))
    exact ⟨lt_of_le_of_ne (hf1 j q hqS hw1 hw2 hw3) hz1,
      lt_of_le_of_ne (hf2 j q hqS hw1 hw2 hw3) hz2⟩
  -- (H) the four points of `S` outside the pentagon
  have hMF : M ∉ (Finset.univ.image P : Finset Point) := by
    intro h
    obtain ⟨j, hj⟩ := (hmemF M).mp h
    exact hMP j hj
  have hsubIns : insert M (Finset.univ.image P) ⊆ S := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact hMS
    · obtain ⟨j, rfl⟩ := (hmemF q).mp hq'
      exact hPS j
  obtain ⟨O, hOdef⟩ : ∃ O : Finset Point, O = S \ insert M (Finset.univ.image P) := ⟨_, rfl⟩
  have hOcard : O.card = 4 := by
    rw [hOdef, Finset.card_sdiff_of_subset hsubIns, hcard, Finset.card_insert_of_notMem hMF, hFcard]
  have hmemO : ∀ q : Point, q ∈ O ↔ (q ∈ S ∧ q ≠ M ∧ ∀ j, q ≠ P j) := by
    intro q
    rw [hOdef, Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hq1, hq2⟩
      exact ⟨hq1, fun h => hq2 (Or.inl h), fun j hj => hq2 (Or.inr ((hmemF q).mpr ⟨j, hj⟩))⟩
    · rintro ⟨hq1, hq2, hq3⟩
      refine ⟨hq1, ?_⟩
      rintro (h | h)
      · exact hq2 h
      · obtain ⟨j, hj⟩ := (hmemF q).mp h
        exact hq3 j hj
  have hOS : ∀ q ∈ O, q ∈ S := fun q hq => ((hmemO q).mp hq).1
  -- (I) the regions
  obtain ⟨B, hBdef⟩ : ∃ B : Fin 5 → Finset Point,
      B = fun j => O.filter (fun q => InB P M j q) := ⟨_, rfl⟩
  have hmemB : ∀ (j : Fin 5) (q : Point), q ∈ B j ↔ (q ∈ O ∧ InB P M j q) := by
    intro j q
    simp only [hBdef, Finset.mem_filter]
  have hBO : ∀ j : Fin 5, B j ⊆ O := fun j q hq => ((hmemB j q).mp hq).1
  have hwedgeEx : ∀ q ∈ O, ∃ j : Fin 5, InB P M j q := by
    intro q hq
    obtain ⟨hqS, hqM, hqP⟩ := (hmemO q).mp hq
    have hqint : q ∉
        interior (convexHull ℝ ((Finset.univ.image P : Finset Point) : Set Point)) := by
      intro h; exact hqM (huniq q hqS h)
    have hRM : ∀ j : Fin 5, orient M (P j) q ≠ 0 := fun j =>
      hgp _ hMS _ (hPS j) _ hqS (hMP j) (Ne.symm hqM) (Ne.symm (hqP j))
    have hRE : ∀ j : Fin 5, orient (P j) (P (j + 1)) q ≠ 0 := fun j =>
      hgp _ (hPS j) _ (hPS (j + 1)) _ hqS (hinj.ne (a01 j)) (Ne.symm (hqP j))
        (Ne.symm (hqP (j + 1)))
    obtain ⟨j, hw1, hw2, hw3⟩ := exists_wedge P M q hccw hMint hqint hRM hRE
    obtain ⟨hw4, hw5⟩ := hnofront j q hqS hw1 hw2 hw3
    exact ⟨j, hw1, hw2, hw3, hw4, hw5⟩
  have hwedgeB : ∀ (j : Fin 5) (q : Point), q ∈ S → 0 < orient M (P j) q →
      orient M (P (j + 1)) q < 0 → orient (P j) (P (j + 1)) q < 0 → q ∈ B j := by
    intro j q hqS hw1 hw2 hw3
    obtain ⟨hw4, hw5⟩ := hnofront j q hqS hw1 hw2 hw3
    exact (hmemB j q).mpr
      ⟨(hmemO q).mpr ⟨hqS, hqneM j q hw3, hqneP j q hw3⟩, hw1, hw2, hw3, hw4, hw5⟩
  -- (J) the tent property, via the second-point case
  have hpair : ∀ (j : Fin 5) (A C : Point), A ∈ B j → C ∈ B j → A ≠ C →
      (∀ q ∈ S, 0 < orient M (P j) q → orient M (P (j + 1)) q < 0 →
        orient (P j) (P (j + 1)) q < 0 →
        -orient (P j) (P (j + 1)) A ≤ -orient (P j) (P (j + 1)) q) →
      0 < orient A (P j) C ∧ 0 < orient (P (j + 1)) A C := by
    intro j A C hA hC hAC hAmin
    obtain ⟨hAO, hAI⟩ := (hmemB j A).mp hA
    obtain ⟨hCO, hCI⟩ := (hmemB j C).mp hC
    have hAS := hOS A hAO
    have hCS := hOS C hCO
    have hAneP : ∀ k, A ≠ P k := ((hmemO A).mp hAO).2.2
    have hCneP : ∀ k, C ≠ P k := ((hmemO C).mp hCO).2.2
    have hz1 : orient A (P j) C ≠ 0 :=
      hgp _ hAS _ (hPS j) _ hCS (hAneP j) hAC (Ne.symm (hCneP j))
    have hz2 : orient (P (j + 1)) A C ≠ 0 :=
      hgp _ (hPS (j + 1)) _ hAS _ hCS (Ne.symm (hAneP (j + 1))) (Ne.symm (hCneP (j + 1))) hAC
    have hno : ¬ (orient A (P j) C < 0 ∨ orient (P (j + 1)) A C < 0) := by
      intro hviol
      exact hcon (second_case S hgp P hinj hPS hccw M hMS hMint huniq hcore j (hnofront j)
        A hAS ⟨hAI.1, hAI.2.1, hAI.2.2.1⟩ hAmin C hCS ⟨hCI.1, hCI.2.1, hCI.2.2.1⟩ hviol)
    push Not at hno
    exact ⟨lt_of_le_of_ne hno.1 (Ne.symm hz1), lt_of_le_of_ne hno.2 (Ne.symm hz2)⟩
  -- (K) case split on the region sizes
  by_cases hbig : ∃ j : Fin 5, 3 ≤ (B j).card
  · -- three or more points in one region: the third-point case
    obtain ⟨j, hj⟩ := hbig
    have hne0 : (B j).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨Q, hQB, hQm0⟩ :=
      Finset.exists_min_image (B j) (fun q => -orient (P j) (P (j + 1)) q) hne0
    have hc1 : ((B j).erase Q).card = (B j).card - 1 := Finset.card_erase_of_mem hQB
    have hne1 : ((B j).erase Q).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨S3, hS3e, hS3m0⟩ :=
      Finset.exists_min_image ((B j).erase Q) (fun q => -orient (P j) (P (j + 1)) q) hne1
    have hc2 : (((B j).erase Q).erase S3).card = ((B j).erase Q).card - 1 :=
      Finset.card_erase_of_mem hS3e
    have hne2 : (((B j).erase Q).erase S3).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨T, hTe, hTm0⟩ :=
      Finset.exists_min_image (((B j).erase Q).erase S3)
        (fun q => -orient (P j) (P (j + 1)) q) hne2
    have hS3B := Finset.mem_of_mem_erase hS3e
    have hTe' := Finset.mem_of_mem_erase hTe
    have hTB := Finset.mem_of_mem_erase hTe'
    have hQS3 : Q ≠ S3 := Ne.symm (Finset.ne_of_mem_erase hS3e)
    have hQT : Q ≠ T := Ne.symm (Finset.ne_of_mem_erase hTe')
    have hS3T : S3 ≠ T := Ne.symm (Finset.ne_of_mem_erase hTe)
    obtain ⟨hQO, hQI⟩ := (hmemB j Q).mp hQB
    obtain ⟨hS3O, hS3I⟩ := (hmemB j S3).mp hS3B
    obtain ⟨hTO, hTI⟩ := (hmemB j T).mp hTB
    have hQminS : ∀ q ∈ S, 0 < orient M (P j) q → orient M (P (j + 1)) q < 0 →
        orient (P j) (P (j + 1)) q < 0 →
        -orient (P j) (P (j + 1)) Q ≤ -orient (P j) (P (j + 1)) q :=
      fun q hqS hw1 hw2 hw3 => hQm0 q (hwedgeB j q hqS hw1 hw2 hw3)
    refine hcon (third_case S hgp P hinj hPS hccw M hMS hMint huniq hcore j (hnofront j)
      Q S3 T (hOS Q hQO) (hOS S3 hS3O) (hOS T hTO)
      ⟨hQI.1, hQI.2.1, hQI.2.2.1⟩ ⟨hS3I.1, hS3I.2.1, hS3I.2.2.1⟩
      ⟨hTI.1, hTI.2.1, hTI.2.2.1⟩ hQS3 hQT hS3T hQminS ?_ ?_ ?_)
    · intro q hqS hw1 hw2 hw3 hqQ
      exact hS3m0 q (Finset.mem_erase.mpr ⟨hqQ, hwedgeB j q hqS hw1 hw2 hw3⟩)
    · intro q hqS hw1 hw2 hw3 hqQ hqS3
      exact hTm0 q (Finset.mem_erase.mpr ⟨hqS3,
        Finset.mem_erase.mpr ⟨hqQ, hwedgeB j q hqS hw1 hw2 hw3⟩⟩)
    · intro q hqS hw1 hw2 hw3 hqQ
      exact hpair j Q q hQB (hwedgeB j q hqS hw1 hw2 hw3) (Ne.symm hqQ) hQminS
  push Not at hbig
  by_cases hmid : ∃ j : Fin 5, 2 ≤ (B j).card
  · -- exactly two points in one region: the two-point case
    obtain ⟨j, hj⟩ := hmid
    have hjc : (B j).card = 2 := by have := hbig j; omega
    have hne0 : (B j).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨Q, hQB, hQm0⟩ :=
      Finset.exists_min_image (B j) (fun q => -orient (P j) (P (j + 1)) q) hne0
    have hc1 : ((B j).erase Q).card = 1 := by rw [Finset.card_erase_of_mem hQB, hjc]
    obtain ⟨S3, hS3eq⟩ := Finset.card_eq_one.mp hc1
    have hS3e : S3 ∈ (B j).erase Q := by rw [hS3eq]; exact Finset.mem_singleton_self S3
    have hS3B := Finset.mem_of_mem_erase hS3e
    have hQS3 : Q ≠ S3 := Ne.symm (Finset.ne_of_mem_erase hS3e)
    obtain ⟨hQO, hQI⟩ := (hmemB j Q).mp hQB
    obtain ⟨hS3O, hS3I⟩ := (hmemB j S3).mp hS3B
    have hBj : B j = {Q, S3} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact hQB
        · rw [Finset.mem_singleton] at hx'; rw [hx']; exact hS3B
      · rw [hjc, Finset.card_pair_eq_two_iff.mpr hQS3]
    have hQminS : ∀ q ∈ S, 0 < orient M (P j) q → orient M (P (j + 1)) q < 0 →
        orient (P j) (P (j + 1)) q < 0 →
        -orient (P j) (P (j + 1)) Q ≤ -orient (P j) (P (j + 1)) q :=
      fun q hqS hw1 hw2 hw3 => hQm0 q (hwedgeB j q hqS hw1 hw2 hw3)
    have hdiffcard : (O \ B j).card = 2 := by rw [Finset.card_sdiff_of_subset (hBO j), hOcard, hjc]
    obtain ⟨X, Y, hXY, hXYeq⟩ := Finset.card_eq_two.mp hdiffcard
    have hXm : X ∈ O \ B j := by rw [hXYeq]; exact Finset.mem_insert_self X {Y}
    have hYm : Y ∈ O \ B j := by
      rw [hXYeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self Y)
    obtain ⟨hXO, hXnB⟩ := Finset.mem_sdiff.mp hXm
    obtain ⟨hYO, hYnB⟩ := Finset.mem_sdiff.mp hYm
    have hXreg : ∃ j' : Fin 5, j' ≠ j ∧ InB P M j' X := by
      obtain ⟨j', hj'⟩ := hwedgeEx X hXO
      refine ⟨j', ?_, hj'⟩
      rintro rfl
      exact hXnB ((hmemB j' X).mpr ⟨hXO, hj'⟩)
    have hYreg : ∃ j' : Fin 5, j' ≠ j ∧ InB P M j' Y := by
      obtain ⟨j', hj'⟩ := hwedgeEx Y hYO
      refine ⟨j', ?_, hj'⟩
      rintro rfl
      exact hYnB ((hmemB j' Y).mpr ⟨hYO, hj'⟩)
    have hsame : ∀ j' : Fin 5, InB P M j' X → InB P M j' Y →
        (-orient (P j') (P (j' + 1)) X ≤ -orient (P j') (P (j' + 1)) Y →
          0 < orient X (P j') Y ∧ 0 < orient (P (j' + 1)) X Y) ∧
        (-orient (P j') (P (j' + 1)) Y ≤ -orient (P j') (P (j' + 1)) X →
          0 < orient Y (P j') X ∧ 0 < orient (P (j' + 1)) Y X) := by
      intro j' hXI hYI
      have hXB' : X ∈ B j' := (hmemB j' X).mpr ⟨hXO, hXI⟩
      have hYB' : Y ∈ B j' := (hmemB j' Y).mpr ⟨hYO, hYI⟩
      have hBj' : B j' = {X, Y} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hXB'
          · rw [Finset.mem_singleton] at hx'; rw [hx']; exact hYB'
        · rw [Finset.card_pair_eq_two_iff.mpr hXY]
          have := hbig j'
          omega
      constructor
      · intro hle
        refine hpair j' X Y hXB' hYB' hXY ?_
        intro q hqS hw1 hw2 hw3
        have hq : q ∈ B j' := hwedgeB j' q hqS hw1 hw2 hw3
        rw [hBj'] at hq
        rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact le_refl _
        · rw [Finset.mem_singleton] at hq'; subst hq'; exact hle
      · intro hle
        refine hpair j' Y X hYB' hXB' (Ne.symm hXY) ?_
        intro q hqS hw1 hw2 hw3
        have hq : q ∈ B j' := hwedgeB j' q hqS hw1 hw2 hw3
        rw [hBj'] at hq
        rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact hle
        · rw [Finset.mem_singleton] at hq'; subst hq'; exact le_refl _
    have hSchar : ∀ q, q ∈ S ↔ (∃ m, q = P m) ∨ q = M ∨ q = Q ∨ q = S3 ∨ q = X ∨ q = Y := by
      intro q
      constructor
      · intro hqS
        by_cases hqM : q = M
        · exact Or.inr (Or.inl hqM)
        by_cases hqF : ∃ m, q = P m
        · exact Or.inl hqF
        · push Not at hqF
          have hqO : q ∈ O := (hmemO q).mpr ⟨hqS, hqM, hqF⟩
          by_cases hqB : q ∈ B j
          · rw [hBj] at hqB
            rcases Finset.mem_insert.mp hqB with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp h))))
          · have hq' : q ∈ O \ B j := Finset.mem_sdiff.mpr ⟨hqO, hqB⟩
            rw [hXYeq] at hq'
            rcases Finset.mem_insert.mp hq' with h | h
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp h)))))
      · rintro (⟨m, rfl⟩ | rfl | rfl | rfl | rfl | rfl)
        · exact hPS m
        · exact hMS
        · exact hOS _ hQO
        · exact hOS _ hS3O
        · exact hOS _ hXO
        · exact hOS _ hYO
    exact hcon (two_case S hgp P hinj hPS hccw M hMS hMint hcore j Q S3 X Y hSchar hQI hS3I
      hQS3 (hQm0 S3 hS3B) (hpair j Q S3 hQB hS3B hQS3 hQminS) hXreg hYreg hXY hsame)
  -- (L) every region holds at most one point: the final case
  push Not at hmid
  have hcard1 : ∀ (j : Fin 5), ∀ x ∈ B j, ∀ y ∈ B j, x = y := by
    intro j
    refine Finset.card_le_one.mp ?_
    have := hmid j
    omega
  choose! reg hreg using hwedgeEx
  have huq : ∀ x y : Point, x ∈ O → y ∈ O → reg x = reg y → x = y := by
    intro x y hx hy hxy
    exact hcard1 (reg x) x ((hmemB _ _).mpr ⟨hx, hreg x hx⟩) y
      ((hmemB _ _).mpr ⟨hy, by rw [hxy]; exact hreg y hy⟩)
  have hinjOn : Set.InjOn reg ↑O := by
    intro x hx y hy hxy
    exact huq x y hx hy hxy
  have himgcard : (O.image reg).card = 4 := by
    rw [Finset.card_image_of_injOn hinjOn, hOcard]
  have hcompl : ((Finset.univ : Finset (Fin 5)) \ O.image reg).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), himgcard, Finset.card_univ, Fintype.card_fin]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcompl
  have hknot : k ∉ O.image reg := by
    have hmem : k ∈ (Finset.univ : Finset (Fin 5)) \ O.image reg := by
      rw [hk]; exact Finset.mem_singleton_self k
    exact (Finset.mem_sdiff.mp hmem).2
  have hin : ∀ j : Fin 5, j ≠ k → ∃ q, q ∈ O ∧ reg q = j := by
    intro j hj
    by_contra hno
    have hmem : j ∈ (Finset.univ : Finset (Fin 5)) \ O.image reg := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, ?_⟩
      intro h
      obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp h
      exact hno ⟨q, hq, hq'⟩
    rw [hk, Finset.mem_singleton] at hmem
    exact hj hmem
  have hnek : ∀ a : Fin 5, a + 1 ≠ a ∧ a + 2 ≠ a ∧ a + 3 ≠ a ∧ a + 4 ≠ a := by decide
  obtain ⟨Qm, hQmO, hQmr⟩ := hin (k + 1) (hnek k).1
  obtain ⟨Q0, hQ0O, hQ0r⟩ := hin (k + 2) (hnek k).2.1
  obtain ⟨Q1, hQ1O, hQ1r⟩ := hin (k + 3) (hnek k).2.2.1
  obtain ⟨Q2, hQ2O, hQ2r⟩ := hin (k + 4) (hnek k).2.2.2
  have hQmI : InB P M (k + 1) Qm := by rw [← hQmr]; exact hreg Qm hQmO
  have hQ0I : InB P M (k + 2) Q0 := by rw [← hQ0r]; exact hreg Q0 hQ0O
  have hQ1I : InB P M (k + 3) Q1 := by rw [← hQ1r]; exact hreg Q1 hQ1O
  have hQ2I : InB P M (k + 4) Q2 := by rw [← hQ2r]; exact hreg Q2 hQ2O
  have g1 : ∀ a : Fin 5, a + 2 - 1 = a + 1 := by decide
  have g2 : ∀ a : Fin 5, a + 2 + 1 = a + 3 := by decide
  have g3 : ∀ a : Fin 5, a + 2 + 2 = a + 4 := by decide
  have hOchar : ∀ q ∈ O, q = Qm ∨ q = Q0 ∨ q = Q1 ∨ q = Q2 := by
    intro q hq
    have hrk : reg q ≠ k := by
      intro h; exact hknot (Finset.mem_image.mpr ⟨q, hq, h⟩)
    have hcases : ∀ a b : Fin 5, b ≠ a → b = a + 1 ∨ b = a + 2 ∨ b = a + 3 ∨ b = a + 4 := by
      decide
    rcases hcases k (reg q) hrk with h | h | h | h
    · exact Or.inl (huq q Qm hq hQmO (by rw [h, hQmr]))
    · exact Or.inr (Or.inl (huq q Q0 hq hQ0O (by rw [h, hQ0r])))
    · exact Or.inr (Or.inr (Or.inl (huq q Q1 hq hQ1O (by rw [h, hQ1r]))))
    · exact Or.inr (Or.inr (Or.inr (huq q Q2 hq hQ2O (by rw [h, hQ2r]))))
  refine hcon (final_case S hgp P hinj hPS hccw M hMS hMint hcore (k + 2) Qm Q0 Q1 Q2
    ?_ hQ0I ?_ ?_ ?_)
  · rw [g1 k]; exact hQmI
  · rw [g2 k]; exact hQ1I
  · rw [g3 k]; exact hQ2I
  · intro q
    constructor
    · intro hqS
      by_cases hqM : q = M
      · exact Or.inr (Or.inl hqM)
      by_cases hqF : ∃ m, q = P m
      · exact Or.inl hqF
      · push Not at hqF
        have hqO : q ∈ O := (hmemO q).mpr ⟨hqS, hqM, hqF⟩
        rcases hOchar q hqO with h | h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · rintro (⟨m, rfl⟩ | rfl | rfl | rfl | rfl | rfl)
      · exact hPS m
      · exact hMS
      · exact hOS _ hQmO
      · exact hOS _ hQ0O
      · exact hOS _ hQ1O
      · exact hOS _ hQ2O

end Horton
