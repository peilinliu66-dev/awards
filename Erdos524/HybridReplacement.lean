import Erdos524.ProductCoordinateReplacement

namespace Erdos524.ProductCoordinateReplacement
open MeasureTheory

noncomputable def hybridFamily {N : ℕ} (μ ν : Fin N → Measure ℝ) (k : ℕ) (i : Fin N) : Measure ℝ :=
  if i.val < k then ν i else μ i

instance hybrid_probability {N : ℕ} (μ ν : Fin N → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, IsProbabilityMeasure (ν j)] (k : ℕ) (i : Fin N) :
    IsProbabilityMeasure (hybridFamily μ ν k i) := by
  unfold hybridFamily
  split <;> infer_instance

theorem integral_pi_replacement {n : ℕ} (μ ν : Fin (n+1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, IsProbabilityMeasure (ν j)]
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : Measurable f) (hbound : ∀ z, ‖f z‖≤1)
    (B : Fin (n+1) → ℝ)
    (hinner : ∀ (i : Fin (n+1)) (y : Fin n → ℝ),
      |(∫ t, f (insertCoordinate i t y) ∂μ i)-(∫ t, f (insertCoordinate i t y) ∂ν i)|≤B i) :
    |(∫ z, f z ∂Measure.pi μ)-(∫ z, f z ∂Measure.pi ν)|≤∑ i, B i := by
  let E : ℕ → ℝ := fun k => ∫ z, f z ∂Measure.pi (hybridFamily μ ν k)
  have hstep (k : ℕ) (hk : k<n+1) : |E k-E (k+1)|≤B ⟨k,hk⟩ := by
    let i : Fin (n+1) := ⟨k,hk⟩
    apply integral_pi_change_one (hybridFamily μ ν k) (hybridFamily μ ν (k+1)) i
    · intro j
      have hj : (i.succAbove j).val ≠ k := by
        intro he
        have : i.succAbove j=i := Fin.ext he
        exact Fin.succAbove_ne i j this
      simp only [hybridFamily]
      split_ifs <;> simp_all <;> omega
    · exact hf
    · exact hbound
    · intro y
      simpa [hybridFamily,i] using hinner i y
  let Bext : ℕ → ℝ := fun j => if hj : j<n+1 then B ⟨j,hj⟩ else 0
  have htel : ∀ k, k≤n+1 → |E 0-E k|≤∑ j ∈ Finset.range k, Bext j := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k≤n+1 := by omega
      have hs := hstep k (by omega)
      have ht := abs_add_le (E 0-E k) (E k-E (k+1))
      rw [Finset.sum_range_succ]
      have hi := ih hk'
      have hid : E 0-E k+(E k-E (k+1))=E 0-E (k+1) := by ring
      rw [hid] at ht
      have hb : Bext k=B ⟨k,by omega⟩ := by dsimp only [Bext]; rw [dif_pos (show k<n+1 by omega)]
      rw [hb]
      exact ht.trans (add_le_add hi hs)
  have hzero : hybridFamily μ ν 0=μ := by funext i; simp [hybridFamily]
  have hend : hybridFamily μ ν (n+1)=ν := by funext i; simp [hybridFamily,i.isLt]
  have he := htel (n+1) le_rfl
  rw [← Fin.sum_univ_eq_sum_range Bext (n+1)] at he
  have hb : (∑ i : Fin (n+1), Bext i.val)=∑ i, B i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Bext]
    rw [dif_pos i.isLt]
  rw [hb] at he
  simpa only [E,hzero,hend] using he

end Erdos524.ProductCoordinateReplacement
