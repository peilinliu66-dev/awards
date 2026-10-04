import Erdos524.UpperMeshCutoff

namespace Erdos524.CauchyKernel

theorem upperPointSet_nonempty {K : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : Real.pi^2 ≤ L) (hw : 1≤upperWidth L G K) :
    (upperPointSet L G K).Nonempty := by
  classical
  let j : Fin K := ⟨0,hK⟩
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hpi : 0<Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hLpos : 0<L := lt_of_lt_of_le hpi hL
  have hd : L/2 ≤ cellDeficit L j := by
    have hdiv : (1 : ℝ)/(2*K) ≤ 1/2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    unfold cellDeficit j
    simp only [Fin.val_mk, Nat.cast_zero, mul_zero, zero_add]
    nlinarith
  have hr : 1≤upperDensity L j := by
    unfold upperDensity
    apply (le_div_iff₀ hpi).mpr
    nlinarith
  have hprod : 1≤upperDensity L j*upperWidth L G K := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hw)]
  have hc : 0<upperCount L G j := Nat.floor_pos.mpr hprod
  let a : Fin (upperCount L G j) := ⟨0,hc⟩
  refine ⟨blockPoint (upperCenter L j) (upperDensity L j) a, ?_⟩
  exact Finset.mem_image.mpr ⟨⟨j,a⟩, Finset.mem_univ _, rfl⟩

end Erdos524.CauchyKernel
