import Erdos1017.MatchingColors

/-! Actual edge-disjoint triangles and an injection of rejected candidates
into missing cross edges. Original source; UNCOMPILED. -/

open scoped BigOperators

namespace Erdos1017

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

local instance (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

def missingPairs (G : SimpleGraph V) (X Y : Finset V) : Finset (V × V) :=
  (X.product Y).filter (fun uv => ¬G.Adj uv.1 uv.2)

theorem missingPairs_card (G : SimpleGraph V) (X Y : Finset V) :
    (missingPairs G X Y).card = missingCount G X Y := by
  classical
  simp only [missingPairs, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.product_eq_sprod, missingCount]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : G.Adj u v <;> simp [h]

namespace ColoredPairSelection

variable {G : SimpleGraph V} {X Y : Finset V} {E : Finset (Finset V)}

def goodPairs (S : ColoredPairSelection X Y E) (G : SimpleGraph V) :
    Finset (Finset V) := S.retained.filter (fun e => ∀u ∈ e, G.Adj u (S.apex e))

def badPairs (S : ColoredPairSelection X Y E) (G : SimpleGraph V) :
    Finset (Finset V) := S.retained.filter (fun e => ¬∀u ∈ e, G.Adj u (S.apex e))

theorem badPairs_card_le (S : ColoredPairSelection X Y E)
    (hsub : ∀ e ∈ E, e ⊆ X) :
    (S.badPairs G).card ≤ missingCount G X Y := by
  classical
  have witness (e : S.badPairs G) : ∃u ∈ e.val, ¬G.Adj u (S.apex e.val) := by
    have h := (Finset.mem_filter.mp e.property).2
    push_neg at h
    exact h
  let pick (e : S.badPairs G) := Classical.choose (witness e)
  have hpick (e : S.badPairs G) :
      pick e ∈ e.val ∧ ¬G.Adj (pick e) (S.apex e.val) :=
    Classical.choose_spec (witness e)
  let f : S.badPairs G → missingPairs G X Y := fun e =>
    ⟨(pick e, S.apex e.val), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨hsub e.val (S.subset (Finset.mem_filter.mp e.property).1) (hpick e).1,
          S.apex_mem e.val (Finset.mem_filter.mp e.property).1⟩, (hpick e).2⟩⟩
  have hf : Function.Injective f := by
    intro e d hed
    have hp : pick e = pick d := congrArg (fun z => z.val.1) hed
    have ha : S.apex e.val = S.apex d.val := congrArg (fun z => z.val.2) hed
    apply Subtype.ext
    apply S.matching e.val (Finset.mem_filter.mp e.property).1
      d.val (Finset.mem_filter.mp d.property).1 ha (pick e) (hpick e).1
    simpa only [hp] using (hpick d).1
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, missingPairs_card] using hcard

theorem totalPairs_le_good_add_discard_add_missing (S : ColoredPairSelection X Y E)
    (hsub : ∀e ∈ E, e ⊆ X) :
    E.card ≤ (S.goodPairs G).card + (E \ S.retained).card + missingCount G X Y := by
  classical
  have hsplit : (S.goodPairs G).card + (S.badPairs G).card = S.retained.card := by
    exact Finset.card_filter_add_card_filter_not _
  have hrest := Finset.card_sdiff_add_card_eq_card S.subset
  have hbad := S.badPairs_card_le (G := G) hsub
  omega

theorem triangle_inter_left (S : ColoredPairSelection X Y E)
    (hXY : Disjoint X Y) (hsub : ∀e ∈ E, e ⊆ X)
    {e : Finset V} (he : e ∈ S.retained) :
    insert (S.apex e) e ∩ X = e := by
  classical
  have hax : S.apex e ∉ X := by
    intro ha
    exact Finset.disjoint_left.mp hXY ha (S.apex_mem e he)
  ext u
  constructor
  · intro hu
    obtain ⟨hu, huX⟩ := Finset.mem_inter.mp hu
    rcases Finset.mem_insert.mp hu with h | h
    · subst u; exact False.elim (hax huX)
    · exact h
  · intro hu
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_insert_of_mem hu, hsub e (S.subset he) hu⟩

theorem triangle_image_injective (S : ColoredPairSelection X Y E)
    (hXY : Disjoint X Y) (hsub : ∀e ∈ E, e ⊆ X) :
    Set.InjOn (fun e => insert (S.apex e) e) (↑S.retained : Set (Finset V)) := by
  intro e he d hd hed
  have h := congrArg (fun C : Finset V => C ∩ X) hed
  simpa only [S.triangle_inter_left hXY hsub he,
    S.triangle_inter_left hXY hsub hd] using h

def trianglePacking (S : ColoredPairSelection X Y E)
    (hXY : Disjoint X Y)
    (hpairs : ∀e ∈ E, e.card = 2 ∧ e ⊆ X ∧ IsClique G e) :
    CliquePacking G where
  blocks := (S.goodPairs G).image (fun e => insert (S.apex e) e)
  nontrivial := by
    classical
    intro C hC
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
    have heR := (Finset.mem_filter.mp he).1
    have hp := hpairs e (S.subset heR)
    have hne : S.apex e ∉ e := by
      intro h
      exact Finset.disjoint_left.mp hXY (hp.2.1 h) (S.apex_mem e heR)
    simp [Finset.card_insert_of_notMem hne, hp.1]
  clique := by
    classical
    intro C hC u hu v hv huv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨heR, hgood⟩ := Finset.mem_filter.mp he
    have hclique := (hpairs e (S.subset heR)).2.2
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact False.elim (huv rfl)
      · exact (hgood v hv).symm
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hgood u hu
      · exact hclique u hu v hv huv
  unique := by
    classical
    intro C hC D hD u huC v hvC huD hvD huv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hD
    have heR := (Finset.mem_filter.mp he).1
    have hfR := (Finset.mem_filter.mp hf).1
    have heP := hpairs e (S.subset heR)
    have hfP := hpairs f (S.subset hfR)
    have notY {z : V} (hz : z ∈ X) : z ∉ Y :=
      fun hy => Finset.disjoint_left.mp hXY hz hy
    have common {z : V} (hze : z ∈ insert (S.apex e) e)
        (hzf : z ∈ insert (S.apex f) f) (hzY : z ∈ Y) :
        S.apex e = S.apex f := by
      have heq : z = S.apex e := (Finset.mem_insert.mp hze).resolve_right
        (fun h => notY (heP.2.1 h) hzY)
      have hfq : z = S.apex f := (Finset.mem_insert.mp hzf).resolve_right
        (fun h => notY (hfP.2.1 h) hzY)
      exact heq.symm.trans hfq
    have hEF : e = f := by
      by_cases huY : u ∈ Y
      · have ha := common huC huD huY
        have hue : u = S.apex e := (Finset.mem_insert.mp huC).resolve_right
          (fun h => notY (heP.2.1 h) huY)
        have hvE : v ∈ e := (Finset.mem_insert.mp hvC).resolve_left
          (fun h => huv (hue.trans h.symm))
        have hvF : v ∈ f := (Finset.mem_insert.mp hvD).resolve_left
          (fun h => huv (hue.trans (ha.trans h.symm)))
        exact S.matching e heR f hfR ha v hvE hvF
      · have huE : u ∈ e := (Finset.mem_insert.mp huC).resolve_left
          (fun h => huY (h.symm ▸ S.apex_mem e heR))
        have huF : u ∈ f := (Finset.mem_insert.mp huD).resolve_left
          (fun h => huY (h.symm ▸ S.apex_mem f hfR))
        by_cases hvY : v ∈ Y
        · exact S.matching e heR f hfR (common hvC hvD hvY) u huE huF
        · have hvE : v ∈ e := (Finset.mem_insert.mp hvC).resolve_left
            (fun h => hvY (h.symm ▸ S.apex_mem e heR))
          have hvF : v ∈ f := (Finset.mem_insert.mp hvD).resolve_left
            (fun h => hvY (h.symm ▸ S.apex_mem f hfR))
          have hpair : ({u,v} : Finset V).card = 2 := by simp [huv]
          have hpe : ({u,v} : Finset V) = e :=
            Finset.eq_of_subset_of_card_le (by
              intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact huE
              · obtain rfl := Finset.mem_singleton.mp hz; exact hvE) (by omega)
          have hpf : ({u,v} : Finset V) = f :=
            Finset.eq_of_subset_of_card_le (by
              intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact huF
              · obtain rfl := Finset.mem_singleton.mp hz; exact hvF) (by omega)
          exact hpe.symm.trans hpf
    subst f
    rfl

theorem trianglePacking_count (S : ColoredPairSelection X Y E)
    (hXY : Disjoint X Y)
    (hpairs : ∀e ∈ E, e.card = 2 ∧ e ⊆ X ∧ IsClique G e) :
    (S.trianglePacking hXY hpairs).count = (S.goodPairs G).card := by
  classical
  apply Finset.card_image_of_injOn
  intro e he f hf h
  exact S.triangle_image_injective hXY (fun e he => (hpairs e he).2.1)
    (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h

theorem trianglePacking_card (S : ColoredPairSelection X Y E)
    (hXY : Disjoint X Y)
    (hpairs : ∀e ∈ E, e.card = 2 ∧ e ⊆ X ∧ IsClique G e) :
    ∀ C ∈ (S.trianglePacking hXY hpairs).blocks, C.card = 3 := by
  classical
  intro C hC
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
  have heR := (Finset.mem_filter.mp he).1
  have hp := hpairs e (S.subset heR)
  have hne : S.apex e ∉ e := by
    intro h
    exact Finset.disjoint_left.mp hXY (hp.2.1 h) (S.apex_mem e heR)
  simp [Finset.card_insert_of_notMem hne, hp.1]

end ColoredPairSelection

end

end Erdos1017
