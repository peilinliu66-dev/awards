import Erdos524.QuantileCounting

namespace Erdos524.QuantileCounting
open Set

noncomputable def affineCDF (a A B s : ℝ) : ℝ := (s-a)*(A-B*(s+a)/2)

theorem affineCDF_difference (a A B x y : ℝ) :
    affineCDF a A B y-affineCDF a A B x = (y-x)*(A-B*(y+x)/2) := by
  unfold affineCDF
  ring

theorem affineCDF_continuous (a A B : ℝ) : Continuous (affineCDF a A B) := by
  unfold affineCDF
  fun_prop

@[simp] theorem affineCDF_left (a A B : ℝ) : affineCDF a A B a=0 := by
  simp [affineCDF]

theorem affineCDF_strictMono {a b A B : ℝ} (hB : 0≤B) (hr : 0<A-B*b) :
    StrictMonoOn (affineCDF a A B) (Icc a b) := by
  intro x hx y hy hxy
  apply sub_pos.mp
  rw [affineCDF_difference]
  apply mul_pos (sub_pos.mpr hxy)
  have hprod := mul_le_mul_of_nonneg_left (show (y+x)/2≤b by linarith [hx.2,hy.2]) hB
  nlinarith

theorem affineCDF_slope_bounds {a b A B : ℝ} (hB : 0≤B) {x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x≤y) :
    (A-B*b)*(y-x) ≤ affineCDF a A B y-affineCDF a A B x ∧
      affineCDF a A B y-affineCDF a A B x ≤ (A-B*a)*(y-x) := by
  rw [affineCDF_difference]
  have havg : a≤(y+x)/2 ∧ (y+x)/2≤b := by constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
  have hb := mul_le_mul_of_nonneg_left havg.2 hB
  have ha := mul_le_mul_of_nonneg_left havg.1 hB
  constructor
  · have h := mul_le_mul_of_nonneg_right (show A-B*b≤A-B*((y+x)/2) by linarith) (sub_nonneg.mpr hxy)
    nlinarith
  · have h := mul_le_mul_of_nonneg_right (show A-B*((y+x)/2)≤A-B*a by linarith) (sub_nonneg.mpr hxy)
    nlinarith

theorem affineCDF_total_pos {a b A B : ℝ} (hab : a<b) (hB : 0≤B) (hr : 0<A-B*b) :
    0<affineCDF a A B b := by
  have h := affineCDF_strictMono hB hr (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  rwa [affineCDF_left] at h

theorem exists_affine_quantile_mesh {a b A B : ℝ} (hab : a<b) (hB : 0≤B) (hr : 0<A-B*b) :
    Nonempty (QuantileMesh a b (affineCDF a A B) ⌊affineCDF a A B b⌋₊) :=
  exists_quantileMesh hab.le (affineCDF_continuous a A B).continuousOn
    (affineCDF_left a A B) rfl (Nat.floor_le (affineCDF_total_pos hab hB hr).le)

theorem affine_quantile_separation {a b A B : ℝ} (hab : a≤b) (hB : 0≤B) (hr : 0<A-B*b)
    (mesh : QuantileMesh a b (affineCDF a A B) ⌊affineCDF a A B b⌋₊) :
    ∀ i j : Fin ⌊affineCDF a A B b⌋₊, i < j → ((j:ℝ)-(i:ℝ))/(A-B*a) ≤ mesh.node j-mesh.node i := by
  have hM : 0<A-B*a := by
    have h := mul_le_mul_of_nonneg_left hab hB
    linarith
  exact mesh.separation (affineCDF_strictMono hB hr) hM
    (fun x hx y hy hxy => (affineCDF_slope_bounds hB hx hy hxy).2)

theorem affine_quantile_discrepancy {a b A B : ℝ} (hab : a≤b) (hB : 0≤B) (hr : 0<A-B*b)
    (mesh : QuantileMesh a b (affineCDF a A B) ⌊affineCDF a A B b⌋₊)
    {s : ℝ} (hs : s ∈ Icc a b) :
    |((Finset.univ.filter (fun i => mesh.node i≤s)).card : ℝ)-affineCDF a A B s|≤1 :=
  mesh.count_discrepancy (affineCDF_strictMono hB hr) hab (affineCDF_left a A B) rfl
    (Nat.lt_floor_add_one _).le hs

end Erdos524.QuantileCounting
