/-
Released under the MIT license.
Finite supporting-line lemmas for the remaining Nicolas Case I.A geometry.
This module does not yet prove the complete sampled replacement is convex.
-/
import JSP198NicolasCaseISampled

noncomputable section
open Classical Horton
namespace JSP198.Nicolas

/-- At a change from an invisible edge to a visible edge, the common
vertex is an actual tangent point: the entire convex polygon lies on one
side of the line joining it to the exterior point. -/
theorem invisible_visible_transition_support
    (Q : Finset Point) (hgp : GeneralPosition Q) (h3 : 3 ≤ Q.card)
    (a b c x : Point) (hab : BoundaryEdge Q a b) (hbc : BoundaryEdge Q b c)
    (hprev : orient a b x < 0) (hnext : 0 < orient b c x) :
    ∀ z ∈ Q, orient b x z ≤ 0 := by
  apply ib_corner_nonpos Q hgp h3 a b c x hab hbc
  · rw [← orient_rotate a b x]
    exact hprev.le
  · have he : orient b x c = -orient b c x := by unfold orient; ring
    rw [he]
    linarith

/-- Two distinct vertices cannot both be transitions from invisible to
visible boundary edges for the same exterior point. This is the concrete
finite geometric input to visibility-interval arguments. -/
theorem invisible_visible_transition_unique
    (S Q : Finset Point) (hgp : GeneralPosition S) (hQS : Q ⊆ S)
    (h3 : 3 ≤ Q.card) (x a b c d e f : Point)
    (hx : x ∈ S) (hxQ : x ∉ Q)
    (hab : BoundaryEdge Q a b) (hbc : BoundaryEdge Q b c)
    (hde : BoundaryEdge Q d e) (hef : BoundaryEdge Q e f)
    (hprev : orient a b x < 0) (hnext : 0 < orient b c x)
    (hprev' : orient d e x < 0) (hnext' : 0 < orient e f x) : b = e := by
  by_contra hbe
  have hb := invisible_visible_transition_support Q (gp_subset hgp hQS) h3
    a b c x hab hbc hprev hnext e hde.2.1
  have he := invisible_visible_transition_support Q (gp_subset hgp hQS) h3
    d e f x hde hef hprev' hnext' b hab.2.1
  have hbx : b ≠ x := by intro h; exact hxQ (h ▸ hab.2.1)
  have hex : e ≠ x := by intro h; exact hxQ (h ▸ hde.2.1)
  have hn := hgp b (hQS hab.2.1) x hx e (hQS hde.2.1) hbx hbe hex.symm
  have hid : orient e x b = -orient b x e := by unfold orient; ring
  rw [hid] at he
  exact hn (by linarith)

/-- Three increasing indices of a genuine convex boundary enumeration have
the clockwise orientation. This supplies the four actual outer vertices
used in the finite endpoint certificate. -/
theorem ia_cycle_triple_neg
    (Q : Finset Point) (hQ : InConvexPosition Q) (hgp : GeneralPosition Q)
    (n : ℕ) (q : ℕ → Point) (hmem : ∀ i, q i ∈ Q)
    (hedge : ∀ i, BoundaryEdge Q (q i) (q (i+1)))
    (hinj : Function.Injective (fun i : Fin n => q i.val))
    (i j k : ℕ) (hij : i < j) (hjk : j < k) (hk : k < n) :
    orient (q i) (q j) (q k) < 0 := by
  have hne (u v : ℕ) (hu : u < n) (hv : v < n) (huv : u ≠ v) : q u ≠ q v := by
    intro hh
    have he : (⟨u,hu⟩ : Fin n) = ⟨v,hv⟩ := hinj hh
    exact huv (congrArg Fin.val he)
  have step (l : ℕ) (hil : i < l) (hl : l+1 < n) :
      orient (q i) (q l) (q (l+1)) < 0 := by
    have hh := (hedge l).strict hgp (hmem i)
      (hne i l (by omega) (by omega) (by omega))
      (hne i (l+1) (by omega) hl (by omega))
    have he : orient (q i) (q l) (q (l+1)) = orient (q l) (q (l+1)) (q i) := by
      unfold orient; ring
    rwa [he]
  have aux : ∀ d : ℕ, j+d < n → 0 < d → orient (q i) (q j) (q (j+d)) < 0 := by
    intro d
    induction d with
    | zero => intro _ hd; omega
    | succ d ih =>
      intro hd _
      by_cases hd0 : d = 0
      · subst d
        simpa using step j hij hd
      · have h1 := ih (by omega) (by omega)
        have h2 := step (j+d) (by omega) (by omega)
        have hp1 : 0 < orient (q i) (q (j+d+1)) (q (j+d)) := by
          have he : orient (q i) (q (j+d+1)) (q (j+d)) =
              -orient (q i) (q (j+d)) (q (j+d+1)) := by unfold orient; ring
          rw [he]; linarith
        have hp2 : 0 < orient (q i) (q (j+d)) (q j) := by
          have he : orient (q i) (q (j+d)) (q j) =
              -orient (q i) (q j) (q (j+d)) := by unfold orient; ring
          rw [he]; linarith
        have hp := orient_pos_trans_at_vertex Q hQ hgp (q i) (q (j+d+1))
          (q (j+d)) (q j) (hmem i) (hmem _) (hmem _) (hmem _) hp1 hp2
        have he : orient (q i) (q j) (q (j+d+1)) =
            -orient (q i) (q (j+d+1)) (q j) := by unfold orient; ring
        change orient (q i) (q j) (q (j+d+1)) < 0
        rw [he]; linarith
  have hh := aux (k-j) (by omega) (by omega)
  simpa only [Nat.add_sub_of_le (by omega : j ≤ k)] using hh

end JSP198.Nicolas

#print axioms JSP198.Nicolas.invisible_visible_transition_support
#print axioms JSP198.Nicolas.invisible_visible_transition_unique
#print axioms JSP198.Nicolas.ia_cycle_triple_neg
