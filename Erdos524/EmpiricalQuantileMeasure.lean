import Erdos524.AffineQuantileMesh
import Erdos524.CDFDiscrepancy

namespace Erdos524.QuantileCounting
open Set MeasureTheory
open scoped BigOperators

noncomputable def empirical {N : ℕ} (t : Fin N → ℝ) : Measure ℝ := ∑ i, Measure.dirac (t i)

instance empirical_finite {N : ℕ} (t : Fin N → ℝ) : IsFiniteMeasure (empirical t) := by
  unfold empirical
  infer_instance

theorem empirical_real_apply {N : ℕ} (t : Fin N → ℝ) (s : Set ℝ) [DecidablePred (fun i => t i ∈ s)] :
    (empirical t).real s = ((Finset.univ.filter (fun i => t i ∈ s)).card : ℝ) := by
  classical
  rw [measureReal_def,empirical,Measure.finsetSum_apply,ENNReal.toReal_sum (by finiteness)]
  simp [Measure.dirac_apply,Set.indicator_apply,apply_ite]

theorem integral_empirical {N : ℕ} (t : Fin N → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empirical t) = ∑ i, f (t i) := by
  unfold empirical
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by finiteness))]
  simp only [integral_dirac]

theorem empirical_atom_le_one {N : ℕ} (t : Fin N → ℝ) (ht : Function.Injective t) (x : ℝ) :
    (empirical t).real {x}≤1 := by
  classical
  rw [empirical_real_apply]
  have hc : (Finset.univ.filter (fun i => t i ∈ ({x}:Set ℝ))).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have h1 := (Finset.mem_filter.mp hi).2
    have h2 := (Finset.mem_filter.mp hj).2
    exact ht (h1.trans h2.symm)
  exact_mod_cast hc

noncomputable def clampedCDF (a b : ℝ) (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s<a then 0 else if b<s then q b else q s

theorem empirical_cdf_discrepancy {a b Q : ℝ} {q : ℝ → ℝ} {N : ℕ}
    (mesh : QuantileMesh a b q N) (hq : StrictMonoOn q (Icc a b))
    (hab : a≤b) (hqa : q a=0) (hqb : q b=Q) (hN : (N:ℝ)≤Q) (hQ : Q≤(N:ℝ)+1) :
    ∀ s : ℝ, |(empirical mesh.node).real (Iic s)-clampedCDF a b q s|≤1 := by
  classical
  intro s
  rw [empirical_real_apply]
  unfold clampedCDF
  by_cases hsa : s<a
  · rw [if_pos hsa]
    have hf : Finset.univ.filter (fun i => mesh.node i ∈ Iic s) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ hi
      have hm := (mesh.node_mem i).1
      exact not_le_of_gt (lt_of_lt_of_le hsa hm) hi
    rw [hf]
    norm_num
  · rw [if_neg hsa]
    by_cases hbs : b<s
    · rw [if_pos hbs,hqb]
      have hf : Finset.univ.filter (fun i => mesh.node i ∈ Iic s) = Finset.univ := by
        apply Finset.filter_eq_self.mpr
        intro i _
        exact (mesh.node_mem i).2.trans hbs.le
      rw [hf]
      simp only [Finset.card_univ,Fintype.card_fin,abs_le]
      constructor <;> linarith
    · rw [if_neg hbs]
      exact mesh.count_discrepancy hq hab hqa hqb hQ ⟨le_of_not_gt hsa,le_of_not_gt hbs⟩

end Erdos524.QuantileCounting
