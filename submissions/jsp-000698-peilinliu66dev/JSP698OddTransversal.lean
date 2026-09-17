import Mathlib

/-!
Finite algebra for the odd-transversal theorem used in Erdős 842.
The odd Eulerian-transversal count is proved for an arbitrary finite number
of equal odd-sized blocks; in the application every block has size three.
This is the parity component of Petrov's argument (arXiv:1512.06205).
The proof below replaces functional-graph cycle selection by first discarding
non-surjective functions and then pairing permutations with their inverses.
-/

namespace JSP698.OddTransversal

open Finset

noncomputable section

variable {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I]

abbrev F2 := ZMod 2

/-- The diagonal term records choosing no outgoing edge. -/
def kernel (A : I → I → C → C → F2) (i j : I) (a b : C) : F2 :=
  if i = j then 1 else A i j a b

def weight (A : I → I → C → C → F2) (f : I → I) (x : I → C) : F2 :=
  ∏ i, kernel A i (f i) (x i) (x (f i))

/-- Source-coordinate averaging of the off-diagonal adjacency kernel. -/
def CrossEven (A : I → I → C → C → F2) : Prop :=
  ∀ i j, i ≠ j → ∀ b, ∑ a, A i j a b = 0

def Symmetric (A : I → I → C → C → F2) : Prop :=
  ∀ i j a b, A i j a b = A j i b a

theorem kernel_symm (A : I → I → C → C → F2) (hA : Symmetric A)
    (i j : I) (a b : C) : kernel A i j a b = kernel A j i b a := by
  classical
  by_cases h : i = j
  · subst j; simp [kernel]
  · simp [kernel, h, Ne.symm h, hA i j a b]

theorem weight_id (A : I → I → C → C → F2) (x : I → C) :
    weight A id x = 1 := by
  classical
  simp [weight, kernel]

/-- Reversing all cycles at once preserves a permutation term. -/
theorem weight_inv (A : I → I → C → C → F2) (hA : Symmetric A)
    (σ : Equiv.Perm I) (x : I → C) : weight A (σ⁻¹ : Equiv.Perm I) x = weight A σ x := by
  classical
  unfold weight
  calc
    (∏ i, kernel A i (σ⁻¹ i) (x i) (x (σ⁻¹ i)))
        = ∏ i, kernel A (σ i) i (x (σ i)) (x i) := by
      simpa using (Equiv.prod_comp σ
        (fun i => kernel A i (σ⁻¹ i) (x i) (x (σ⁻¹ i)))).symm
    _ = ∏ i, kernel A i (σ i) (x i) (x (σ i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact kernel_symm A hA _ _ _ _

/-- A vertex with no incoming arrow appears in exactly one factor. -/
theorem sum_weight_update_eq_zero_of_no_preimage
    (A : I → I → C → C → F2) (hA : CrossEven A)
    (f : I → I) (p : I) (hp : ∀ i, f i ≠ p) (x : I → C) :
    ∑ a, weight A f (Function.update x p a) = 0 := by
  classical
  have hfp : p ≠ f p := (hp p).symm
  have hfactor (a : C) :
      weight A f (Function.update x p a) =
        A p (f p) a (x (f p)) *
          ∏ i ∈ Finset.univ.erase p, kernel A i (f i) (x i) (x (f i)) := by
    unfold weight
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    simp only [Function.update_self, Function.update_of_ne (hp p), kernel,
      if_neg hfp]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hip : i ≠ p := (Finset.mem_erase.mp hi).1
    simp only [Function.update_of_ne hip, Function.update_of_ne (hp i)]
  simp_rw [hfactor]
  rw [← Finset.sum_mul, hA p (f p) hfp, zero_mul]

/-- Product expansion yields one term for each outgoing-arrow function. -/
theorem expand_product (A : I → I → C → C → F2) (x : I → C) :
    (∏ i, ∑ j, kernel A i j (x i) (x j)) = ∑ f : I → I, weight A f x := by
  classical
  simpa [weight] using (Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset I))
    (fun i j => kernel A i j (x i) (x j)))

/-- Fibrewise zero sums imply the full Cartesian-product sum is zero. -/
theorem sum_eq_zero_of_sum_update (F : (I → C) → F2) (p : I)
    (hF : ∀ x : I → C, ∑ a, F (Function.update x p a) = 0) :
    ∑ x, F x = 0 := by
  classical
  by_cases hC : Nonempty C
  · let c₀ : C := Classical.choice hC
    rw [← (Equiv.funSplitAt p C).symm.sum_comp F, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro y _
    let x : I → C := (Equiv.funSplitAt p C).symm (c₀, y)
    convert hF x using 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    funext i
    by_cases hi : i = p
    · subst i; simp [Equiv.funSplitAt_symm_apply]
    · simp [Equiv.funSplitAt_symm_apply, Function.update_of_ne hi, x, hi]
  · have hI : Nonempty I := ⟨p⟩
    have : IsEmpty C := not_nonempty_iff.mp hC
    have : IsEmpty (I → C) := ⟨fun x => isEmptyElim (x p)⟩
    simp

theorem sum_weight_eq_zero_of_not_surjective
    (A : I → I → C → C → F2) (hA : CrossEven A)
    (f : I → I) (hf : ¬ Function.Surjective f) :
    ∑ x, weight A f x = 0 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, ∀ i, f i ≠ p := by
    simpa [Function.Surjective] using hf
  apply sum_eq_zero_of_sum_update _ p
  intro x
  exact sum_weight_update_eq_zero_of_no_preimage A hA f p hp x

/-- A nonidentity self-inverse permutation has a two-cycle; its squared
adjacency factor is a single factor in the Boolean field. -/
theorem sum_weight_eq_zero_of_involution
    (A : I → I → C → C → F2) (hA : CrossEven A) (hs : Symmetric A)
    (σ : Equiv.Perm I) (hinv : σ⁻¹ = σ) (hne : σ ≠ 1) :
    ∑ x, weight A σ x = 0 := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
    by_contra! h
    apply hne
    ext p
    exact h p
  have hsq (i : I) : σ (σ i) = i := by
    have h := σ.symm_apply_apply i
    change (σ⁻¹ : Equiv.Perm I) (σ i) = i at h
    rwa [hinv] at h
  have hpq : p ≠ σ p := hp.symm
  apply sum_eq_zero_of_sum_update _ p
  intro x
  have hfactor (a : C) :
      weight A σ (Function.update x p a) =
        A p (σ p) a (x (σ p)) *
          ∏ i ∈ (Finset.univ.erase p).erase (σ p),
            kernel A i (σ i) (x i) (x (σ i)) := by
    unfold weight
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    rw [← Finset.mul_prod_erase _ _ (show σ p ∈ Finset.univ.erase p by simp [hp])]
    have hrest :
        (∏ i ∈ (Finset.univ.erase p).erase (σ p),
          kernel A i (σ i) (Function.update x p a i) (Function.update x p a (σ i))) =
        ∏ i ∈ (Finset.univ.erase p).erase (σ p), kernel A i (σ i) (x i) (x (σ i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hip : i ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hiq : i ≠ σ p := (Finset.mem_erase.mp hi).1
      have hsip : σ i ≠ p := by
        intro he
        apply hiq
        simpa [hsq] using congrArg σ he
      simp only [Function.update_of_ne hip, Function.update_of_ne hsip]
    rw [hrest]
    simp only [Function.update_self, Function.update_of_ne hp, hsq,
      kernel, if_neg hpq, if_neg hp]
    rw [hs (σ p) p (x (σ p)) a, ← mul_assoc, ← sq,
      show (A p (σ p) a (x (σ p))) ^ 2 = A p (σ p) a (x (σ p)) from
        ZMod.pow_card _]
  simp_rw [hfactor]
  rw [← Finset.sum_mul, hA p (σ p) hpq, zero_mul]

theorem sum_functions_eq_sum_perms
    (A : I → I → C → C → F2) (hA : CrossEven A) :
    (∑ f : I → I, ∑ x, weight A f x) =
      ∑ σ : Equiv.Perm I, ∑ x, weight A σ x := by
  classical
  let S : Finset (I → I) := Finset.univ.image (fun σ : Equiv.Perm I => (σ : I → I))
  calc
    (∑ f : I → I, ∑ x, weight A f x) = ∑ f ∈ S, ∑ x, weight A f x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro f _ hf
      apply sum_weight_eq_zero_of_not_surjective A hA f
      intro hsur
      apply hf
      let σ : Equiv.Perm I := Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hsur, hsur⟩
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
    _ = ∑ σ : Equiv.Perm I, ∑ x, weight A σ x := by
      unfold S
      rw [Finset.sum_image]
      intro σ _ τ _ h
      exact Equiv.ext (congrFun h)

theorem sum_perm_weights_eq_one
    (A : I → I → C → C → F2) (hA : CrossEven A) (hs : Symmetric A)
    (hodd : Odd (Fintype.card C)) :
    (∑ σ : Equiv.Perm I, ∑ x, weight A σ x) = 1 := by
  classical
  have hinverse (σ : Equiv.Perm I) :
      (∑ x, weight A (σ⁻¹ : Equiv.Perm I) x) = ∑ x, weight A σ x := by
    apply Finset.sum_congr rfl
    intro x _
    exact weight_inv A hs σ x
  have hzero : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm I)).erase 1,
      ∑ x, weight A σ x) = 0 := by
    apply Finset.sum_involution (fun σ _ => σ⁻¹)
    · intro σ _
      rw [hinverse]
      rw [← two_mul]
      rw [show (2 : F2) = 0 by decide, zero_mul]
    · intro σ hσ hne hinv
      apply hne
      exact sum_weight_eq_zero_of_involution A hA hs σ hinv (Finset.mem_erase.mp hσ).1
    · intro σ _
      simp
    · intro σ hσ
      simpa using hσ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm I)), hzero, add_zero]
  have hcard : (Fintype.card C : F2) = 1 := hodd.natCast_zmod_two
  simp only [Equiv.Perm.coe_one, weight_id, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Fintype.card_fun, Nat.cast_pow, hcard, one_pow]

/-- The algebraic odd-transversal identity. The diagonal kernel is 1 and
off-diagonal cross-block row sums vanish. -/
theorem odd_transversal_kernel_identity
    (A : I → I → C → C → F2) (hA : CrossEven A) (hs : Symmetric A)
    (hodd : Odd (Fintype.card C)) :
    (∑ x : I → C, ∏ i, ∑ j, kernel A i j (x i) (x j)) = 1 := by
  simp_rw [expand_product]
  rw [Finset.sum_comm, sum_functions_eq_sum_perms A hA]
  exact sum_perm_weights_eq_one A hA hs hodd

theorem odd_transversal_identity
    (A : I → I → C → C → F2) (hA : CrossEven A) (hs : Symmetric A)
    (hdiag : ∀ i a, A i i a a = 0) (hodd : Odd (Fintype.card C)) :
    (∑ x : I → C, ∏ i, (1 + ∑ j, A i j (x i) (x j))) = 1 := by
  have hrow (x : I → C) (i : I) :
      (∑ j, kernel A i j (x i) (x j)) = 1 + ∑ j, A i j (x i) (x j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [show kernel A i i (x i) (x i) = 1 by simp [kernel]]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [kernel, hji.symm]
  simpa only [hrow] using odd_transversal_kernel_identity A hA hs hodd

theorem f2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The number of transversals with every induced degree even is odd.
The degree is represented by its image in `ZMod 2`. -/
theorem odd_eulerian_transversals
    (A : I → I → C → C → F2) (hA : CrossEven A) (hs : Symmetric A)
    (hdiag : ∀ i a, A i i a a = 0) (hodd : Odd (Fintype.card C)) :
    Odd ((Finset.univ : Finset (I → C)).filter
      (fun x => ∀ i, ∑ j, A i j (x i) (x j) = 0)).card := by
  classical
  have hprod (x : I → C) :
      (∏ i, (1 + ∑ j, A i j (x i) (x j))) =
        if (∀ i, ∑ j, A i j (x i) (x j) = 0) then 1 else 0 := by
    by_cases h : ∀ i, ∑ j, A i j (x i) (x j) = 0
    · simp [h]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, ∑ j, A i j (x i) (x j) ≠ 0 := by simpa using h
      have hone := (f2_eq_zero_or_one (∑ j, A i j (x i) (x j))).resolve_left hi
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hone]
      decide
  apply ZMod.natCast_eq_one_iff_odd.mp
  calc
    (((Finset.univ : Finset (I → C)).filter
      (fun x => ∀ i, ∑ j, A i j (x i) (x j) = 0)).card : F2)
        = ∑ x : I → C, if (∀ i, ∑ j, A i j (x i) (x j) = 0) then 1 else 0 := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          simp only [Nat.cast_one, Finset.sum_filter]
    _ = ∑ x : I → C, ∏ i, (1 + ∑ j, A i j (x i) (x j)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (hprod x).symm
    _ = 1 := odd_transversal_identity A hA hs hdiag hodd

#print axioms sum_weight_update_eq_zero_of_no_preimage
#print axioms weight_inv
#print axioms odd_transversal_kernel_identity
#print axioms odd_transversal_identity
#print axioms odd_eulerian_transversals

end
end JSP698.OddTransversal
