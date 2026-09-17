import EmptyPentagon.Definitions

/-!
Elementary geometric end of the finite Erdős--Szekeres argument.
The definitions imported above are preserved from the MIT-licensed PR283 source.
This file proves convex independence from uniform ordered triple orientation;
it does not assume or claim the finite Ramsey selection step.
-/

noncomputable section
namespace Horton

def ESPositive (p : Fin 25 → Point) : Prop :=
  ∀ i j k, i < j → j < k → 0 < orient (p i) (p j) (p k)

private theorem es_orient_cycle (a b c : Point) :
    orient a b c = orient b c a := by unfold orient; ring

private theorem es_orient_same_left (a b : Point) : orient a b a = 0 := by
  simp [orient]

private theorem es_orient_same_right (a b : Point) : orient a b b = 0 := by
  unfold orient; ring

private def esNext (i : Fin 25) : Fin 25 :=
  if h : i.val + 1 < 25 then ⟨i.val + 1, h⟩ else 0

private def esPrev (i : Fin 25) : Fin 25 :=
  if h : 0 < i.val then ⟨i.val - 1, by omega⟩ else 24

private theorem es_next_prev_ne (i : Fin 25) : esNext i ≠ esPrev i := by
  simp only [esNext, esPrev]
  split_ifs <;> intro h <;> have := congrArg Fin.val h <;> simp at this <;> omega

private theorem es_cyclic_pos {p : Fin 25 → Point} (hp : ESPositive p)
    (i j k : Fin 25)
    (h : (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)) :
    0 < orient (p i) (p j) (p k) := by
  rcases h with h | h | h
  · exact hp i j k h.1 h.2
  · rw [es_orient_cycle]
    exact hp j k i h.1 h.2
  · rw [es_orient_cycle, es_orient_cycle]
    exact hp k i j h.1 h.2

private theorem es_next_pos {p : Fin 25 → Point} (hp : ESPositive p)
    (i j : Fin 25) (hji : j ≠ i) (hjn : j ≠ esNext i) :
    0 < orient (p i) (p (esNext i)) (p j) := by
  apply es_cyclic_pos hp
  simp only [esNext] at hjn ⊢
  split_ifs at hjn ⊢ with hi
  · have hneq : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hneq' : j.val ≠ i.val + 1 := fun h => hjn (Fin.ext h)
    simp only [Fin.lt_def, Fin.val_mk]
    omega
  · have hneq : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hneq' : j.val ≠ 0 := fun h => hjn (Fin.ext h)
    simp only [Fin.lt_def, Fin.val_zero]
    have := i.isLt
    have := j.isLt
    omega

private theorem es_prev_pos {p : Fin 25 → Point} (hp : ESPositive p)
    (i j : Fin 25) (hji : j ≠ i) (hjp : j ≠ esPrev i) :
    0 < orient (p (esPrev i)) (p i) (p j) := by
  apply es_cyclic_pos hp
  simp only [esPrev] at hjp ⊢
  split_ifs at hjp ⊢ with hi
  · have hneq : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hneq' : j.val ≠ i.val - 1 := fun h => hjp (Fin.ext h)
    simp only [Fin.lt_def, Fin.val_mk]
    omega
  · have hneq : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have hneq' : j.val ≠ 24 := fun h => hjp (Fin.ext h)
    simp only [Fin.lt_def]
    have := j.isLt
    norm_num
    omega

private def esOrientLinear (a b : Point) : Point →ₗ[ℝ] ℝ where
  toFun x := (b.1 - a.1) * x.2 - (b.2 - a.2) * x.1
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

private theorem es_orient_linear (a b x : Point) :
    orient a b x = esOrientLinear a b x - esOrientLinear a b a := by
  simp only [orient, esOrientLinear, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- Every ordered triple positive implies all 25 points are convex independent.
The order is arbitrary: no distinct-x-coordinate hypothesis is needed. -/
theorem convexIndependent_of_esPositive {p : Fin 25 → Point} (hp : ESPositive p) :
    ConvexIndependent ℝ p := by
  intro s i hi
  by_contra hnot
  let L : Point →ₗ[ℝ] ℝ :=
    esOrientLinear (p i) (p (esNext i)) + esOrientLinear (p (esPrev i)) (p i)
  have hstrict : ∀ j, j ≠ i → L (p i) < L (p j) := by
    intro j hji
    have hn : 0 ≤ orient (p i) (p (esNext i)) (p j) := by
      by_cases h : j = esNext i
      · rw [h, es_orient_same_right]
      · exact (es_next_pos hp i j hji h).le
    have hv : 0 ≤ orient (p (esPrev i)) (p i) (p j) := by
      by_cases h : j = esPrev i
      · rw [h, es_orient_same_left]
      · exact (es_prev_pos hp i j hji h).le
    have hs : 0 < orient (p i) (p (esNext i)) (p j) +
        orient (p (esPrev i)) (p i) (p j) := by
      by_cases h : j = esNext i
      · have hv' := es_prev_pos hp i j hji (by rw [h]; exact es_next_prev_ne i)
        linarith
      · have hn' := es_next_pos hp i j hji h
        linarith
    have hzero := es_orient_same_right (p (esPrev i)) (p i)
    rw [es_orient_linear] at hzero
    simp only [es_orient_linear] at hs
    change esOrientLinear (p i) (p (esNext i)) (p i) +
        esOrientLinear (p (esPrev i)) (p i) (p i) <
      esOrientLinear (p i) (p (esNext i)) (p j) +
        esOrientLinear (p (esPrev i)) (p i) (p j)
    linarith
  have hconv : Convex ℝ {x : Point | L (p i) < L x} :=
    (convex_Ioi (𝕜 := ℝ) (L (p i))).linear_preimage L
  have hsub : p '' s ⊆ {x : Point | L (p i) < L x} := by
    rintro _ ⟨j, hj, rfl⟩
    exact hstrict j (fun h => hnot (h ▸ hj))
  have := convexHull_min hsub hconv hi
  exact lt_irrefl (L (p i)) this

theorem convexIndependent_of_esNegative {p : Fin 25 → Point}
    (hp : ∀ i j k, i < j → j < k → orient (p i) (p j) (p k) < 0) :
    ConvexIndependent ℝ p := by
  have hpos : ESPositive (fun i => p (Fin.rev i)) := by
    intro i j k hij hjk
    have h := hp (Fin.rev k) (Fin.rev j) (Fin.rev i)
      (Fin.rev_lt_rev.mpr hjk) (Fin.rev_lt_rev.mpr hij)
    have heq : orient (p (Fin.rev i)) (p (Fin.rev j)) (p (Fin.rev k)) =
        - orient (p (Fin.rev k)) (p (Fin.rev j)) (p (Fin.rev i)) := by
      unfold orient
      ring
    rw [heq]
    linarith
  have hc := (convexIndependent_of_esPositive hpos).comp_embedding
    (Fin.revPerm.toEmbedding : Fin 25 ↪ Fin 25)
  change ConvexIndependent ℝ (fun i => p (Fin.rev (Fin.rev i))) at hc
  simpa only [Fin.rev_rev] using hc

end Horton

#print axioms Horton.convexIndependent_of_esPositive
#print axioms Horton.convexIndependent_of_esNegative
