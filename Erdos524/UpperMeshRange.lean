import Erdos524.UpperMeshAsymptotic

namespace Erdos524.CauchyKernel

theorem upperPointSet_max {K : ℕ} (hK : 0<K) {L G : ℝ}
    (hL : 0<L) (hw : 0≤upperWidth L G K) {x : ℝ} (hx : x ∈ upperPointSet L G K) :
    x≤2*L-G := by
  classical
  obtain ⟨⟨j,a⟩, _, rfl⟩ := Finset.mem_image.mp hx
  have h := (abs_le.mp (blockPoint_within (upperCenter L j) (upperDensity_pos hK hL j)
    (upperCount_le hK hL hw j) a)).2
  have hk : (0:ℝ)<K := by positivity
  have hj : (j:ℝ)+1≤K := by exact_mod_cast j.isLt
  have he : upperCenter L j+upperWidth L G K/2 = 2*((j:ℝ)+1)*L/K-G := by
    unfold upperCenter upperWidth
    ring
  have hr : 2*((j:ℝ)+1)*L/K≤2*L := by
    apply (div_le_iff₀ hk).mpr
    nlinarith
  linarith

theorem upperPointSet_exp_range {K : ℕ} (hK : 0<K) {L : ℝ} (hL : 2≤L)
    (hw : 0≤upperWidth L (4*Real.log L) K) {x : ℝ}
    (hx : x ∈ upperPointSet L (4*Real.log L) K) :
    L^4≤Real.exp x ∧ Real.exp x≤Real.exp (2*L) := by
  refine ⟨upper_mesh_exp_min hK hL hw hx, Real.exp_le_exp.mpr ?_⟩
  have h := upperPointSet_max hK (by linarith : 0<L) hw hx
  have hlog := Real.log_nonneg (by linarith : 1≤L)
  linarith

end Erdos524.CauchyKernel
