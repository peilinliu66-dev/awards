import Erdos524.LaplaceStepKernel

namespace Erdos524.UniformPartition
open MeasureTheory Set Filter

noncomputable def cell {N : ℕ} (i : Fin N) : Set ℝ := Ico ((i:ℝ)/(N:ℝ)) (((i.val+1:ℕ):ℝ)/(N:ℝ))

theorem floor_on_cell {N : ℕ} (hN : 0<N) (i : Fin N) {s : ℝ} (hs : s∈cell i) : ⌊s*(N:ℝ)⌋₊=i.val := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hs0 : 0≤s := (by positivity : (0:ℝ)≤(i:ℝ)/(N:ℝ)).trans hs.1
  apply (Nat.floor_eq_iff (mul_nonneg hs0 hNp.le)).mpr
  constructor
  · exact (div_le_iff₀ hNp).mp hs.1
  · have h := (lt_div_iff₀ hNp).mp hs.2
    simpa only [Nat.cast_add,Nat.cast_one] using h

theorem cells_cover {N : ℕ} (hN : 0<N) : (⋃ i : Fin N, cell i)=Ico (0:ℝ) 1 := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  ext s
  constructor
  · intro hs
    obtain ⟨i,hi⟩ := mem_iUnion.mp hs
    constructor
    · exact (by positivity : (0:ℝ)≤(i:ℝ)/(N:ℝ)).trans hi.1
    · apply hi.2.trans_le
      apply (div_le_one hNp).mpr
      exact_mod_cast (show i.val+1≤N by omega)
  · intro hs
    let j : ℕ := ⌊s*(N:ℝ)⌋₊
    have hjle : (j:ℝ)≤s*(N:ℝ) := Nat.floor_le (mul_nonneg hs.1 hNp.le)
    have hjlt : (j:ℝ)<(N:ℝ) := hjle.trans_lt (by nlinarith [hs.2])
    have hj : j<N := by exact_mod_cast hjlt
    apply mem_iUnion.mpr
    refine ⟨⟨j,hj⟩,?_,?_⟩
    · exact (div_le_iff₀ hNp).mpr hjle
    · apply (lt_div_iff₀ hNp).mpr
      simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (s*(N:ℝ))

theorem cells_pairwise_disjoint {N : ℕ} (hN : 0<N) : Pairwise (fun i j : Fin N => Disjoint (cell i) (cell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro s hi hj
  apply hij
  apply Fin.ext
  exact (floor_on_cell hN i hi).symm.trans (floor_on_cell hN j hj)

theorem integral_floor_step {N : ℕ} (hN : 0<N) (F : ℕ → ℝ) :
    (∫ s in Ico (0:ℝ) 1, F ⌊s*(N:ℝ)⌋₊)= (∑ i : Fin N, F i.val)/(N:ℝ) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have he (i : Fin N) : Set.EqOn (fun s : ℝ => F ⌊s*(N:ℝ)⌋₊) (fun _ => F i.val) (cell i) := by
    intro s hs
    change F ⌊s*(N:ℝ)⌋₊=F i.val
    rw [floor_on_cell hN i hs]
  have hi (i : Fin N) : IntegrableOn (fun s : ℝ => F ⌊s*(N:ℝ)⌋₊) (cell i) := by
    apply (integrableOn_const (C := F i.val) (s := cell i) (by simp [cell])).congr_fun
    · exact fun s hs => (he i hs).symm
    · exact measurableSet_Ico
  have hmeas (i : Fin N) : MeasurableSet (cell i) := measurableSet_Ico
  rw [← cells_cover hN,integral_iUnion_fintype hmeas (cells_pairwise_disjoint hN) hi]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [setIntegral_congr_fun (hmeas i) (he i),setIntegral_const]
  have hlen : (((i.val+1:ℕ):ℝ)/(N:ℝ))-(i:ℝ)/(N:ℝ)=1/(N:ℝ) := by push_cast; ring
  simp only [cell,Measure.real,Real.volume_Ico,hlen,ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤1/(N:ℝ)),smul_eq_mul]
  ring

end Erdos524.UniformPartition
