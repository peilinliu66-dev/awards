import Erdos524.SoftMaximum

namespace Erdos524.SoftMaximum
open scoped BigOperators

noncomputable def momentNumerator {n : ℕ} (β : ℝ) (x v : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ i, (v i)^k*Real.exp (β*(x i+t*v i))

theorem momentNumerator_hasDerivAt {n : ℕ} (β : ℝ) (x v : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (momentNumerator β x v k) (β*momentNumerator β x v (k+1) t) t := by
  have hi (i : Fin n) : HasDerivAt (fun s : ℝ => (v i)^k*Real.exp (β*(x i+s*v i)))
      ((v i)^k*(Real.exp (β*(x i+t*v i))*(β*v i))) t := by
    convert ((((hasDerivAt_id t).mul_const (v i)).const_add (x i)).const_mul β).exp.const_mul ((v i)^k) using 1
    · funext s; simp only [id_eq]
    · simp only [id_eq]; ring
  have hs := HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
  convert hs using 1
  · funext s
    simp only [momentNumerator,Finset.sum_apply]
  · unfold momentNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem partition_path_hasDerivAt {n : ℕ} (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => partition β (fun i => x i+s*v i))
      (β*momentNumerator β x v 1 t) t := by
  convert momentNumerator_hasDerivAt β x v 0 t using 1
  funext s
  simp only [momentNumerator,pow_zero,one_mul,partition]

theorem directionalMoment_hasDerivAt {n : ℕ} (hn : 0<n) (β : ℝ) (x v : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (directionalMoment β x v k)
      (β*(directionalMoment β x v (k+1) t-directionalMoment β x v k t*directionalMoment β x v 1 t)) t := by
  have hZ := ne_of_gt (partition_pos hn β (fun i => x i+t*v i))
  have h := (momentNumerator_hasDerivAt β x v k t).div (partition_path_hasDerivAt β x v t) hZ
  convert h using 1
  · funext s
    rfl
  · unfold directionalMoment momentNumerator
    field_simp
    <;> ring

noncomputable def softPath {n : ℕ} (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) : ℝ :=
  softMax β (fun i => x i+t*v i)

theorem softPath_hasDerivAt {n : ℕ} (hn : 0<n) {β : ℝ} (hβ : β≠0)
    (x v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (softPath β x v) (directionalMoment β x v 1 t) t := by
  have hZ := ne_of_gt (partition_pos hn β (fun i => x i+t*v i))
  have h := ((partition_path_hasDerivAt β x v t).log hZ).div_const β
  convert h using 1
  · funext s; rfl
  · unfold directionalMoment momentNumerator
    field_simp
    simp only [mul_comm t]

noncomputable def softSecond {n : ℕ} (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) : ℝ :=
  β*(directionalMoment β x v 2 t-(directionalMoment β x v 1 t)^2)
noncomputable def softThird {n : ℕ} (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) : ℝ :=
  β^2*(directionalMoment β x v 3 t-3*directionalMoment β x v 2 t*directionalMoment β x v 1 t+
    2*(directionalMoment β x v 1 t)^3)
noncomputable def softFourth {n : ℕ} (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) : ℝ :=
  β^3*(directionalMoment β x v 4 t-4*directionalMoment β x v 3 t*directionalMoment β x v 1 t-
    3*(directionalMoment β x v 2 t)^2+
    12*directionalMoment β x v 2 t*(directionalMoment β x v 1 t)^2-
    6*(directionalMoment β x v 1 t)^4)

theorem softFirst_hasDerivAt {n : ℕ} (hn : 0<n) (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (directionalMoment β x v 1) (softSecond β x v t) t := by
  convert directionalMoment_hasDerivAt hn β x v 1 t using 1
  unfold softSecond
  ring

theorem softSecond_hasDerivAt {n : ℕ} (hn : 0<n) (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (softSecond β x v) (softThird β x v t) t := by
  have h1 := directionalMoment_hasDerivAt hn β x v 1 t
  have h2 := directionalMoment_hasDerivAt hn β x v 2 t
  convert (h2.sub (h1.pow 2)).const_mul β using 1
  · funext s; rfl
  · unfold softThird
    ring

theorem softThird_hasDerivAt {n : ℕ} (hn : 0<n) (β : ℝ) (x v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (softThird β x v) (softFourth β x v t) t := by
  have h1 := directionalMoment_hasDerivAt hn β x v 1 t
  have h2 := directionalMoment_hasDerivAt hn β x v 2 t
  have h3 := directionalMoment_hasDerivAt hn β x v 3 t
  convert ((h3.sub ((h2.mul h1).const_mul 3)).add ((h1.pow 3).const_mul 2)).const_mul (β^2) using 1
  · funext s
    dsimp only [softThird,Pi.sub_apply,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
    ring
  · unfold softFourth
    ring

end Erdos524.SoftMaximum
