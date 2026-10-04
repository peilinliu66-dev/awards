import Erdos524.DyadicUpperScale
import Erdos524.ModerateSignTail

namespace Erdos524.GeometricWalkScale
open Filter
open Erdos524.DyadicUpperScale

def endpoint (B j : ℕ) : ℕ := B^j
def blockLength (B j : ℕ) : ℕ := endpoint B (j+1)-endpoint B j

theorem endpoint_strictMono {B : ℕ} (hB : 1<B) : StrictMono (endpoint B) := by
  apply strictMono_nat_of_lt_succ
  intro j
  change B^j<B^(j+1)
  rw [pow_succ]
  have hp : 0<B^j := pow_pos (by omega) _
  nlinarith

theorem endpoint_pos {B : ℕ} (hB : 1<B) (j : ℕ) : 0<endpoint B j := pow_pos (by omega) _

theorem blockLength_identity {B : ℕ} (hB : 1<B) (j : ℕ) : blockLength B j=(B-1)*B^j := by
  unfold blockLength endpoint
  rw [pow_succ,Nat.sub_mul,one_mul]
  rw [Nat.mul_comm (B^j) B]

theorem blockLength_pos {B : ℕ} (hB : 1<B) (j : ℕ) : 0<blockLength B j := by
  unfold blockLength
  exact Nat.sub_pos_of_lt (endpoint_strictMono hB (Nat.lt_succ_self j))

theorem log_endpoint_succ {B : ℕ} (hB : 1<B) (j : ℕ) :
    Real.log (Real.log (endpoint B (j+1):ℝ))=Real.log (j+1:ℝ)+Real.log (Real.log (B:ℝ)) := by
  have hb : 0<Real.log (B:ℝ) := Real.log_pos (by exact_mod_cast hB)
  simp only [endpoint,Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one]
  rw [Real.log_mul (by positivity) hb.ne']

theorem log_blockLength {B : ℕ} (hB : 1<B) (j : ℕ) :
    Real.log (blockLength B j:ℝ)=Real.log ((B:ℝ)-1)+(j:ℝ)*Real.log (B:ℝ) := by
  have hb : (1:ℝ)<B := by exact_mod_cast hB
  rw [blockLength_identity hB,Nat.cast_mul,Nat.cast_sub (by omega : 1≤B)]
  simp only [Nat.cast_one,Nat.cast_pow]
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow]

noncomputable def threshold (B : ℕ) (c : ℝ) (j : ℕ) : ℝ :=
  c*upperScale (endpoint B (j+1))/Real.sqrt (blockLength B j:ℝ)

theorem threshold_sq {B : ℕ} (hB : 1<B) {c : ℝ} (j : ℕ)
    (hl : 0≤Real.log (Real.log (endpoint B (j+1):ℝ))) :
    (threshold B c j)^2=2*(c^2*(B:ℝ)/((B:ℝ)-1))*Real.log (Real.log (endpoint B (j+1):ℝ)) := by
  have hb : (1:ℝ)<B := by exact_mod_cast hB
  have hm : (0:ℝ)<blockLength B j := by exact_mod_cast blockLength_pos hB j
  unfold threshold upperScale
  rw [div_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hm.le]
  rw [blockLength_identity hB]
  simp only [endpoint,pow_succ,Nat.cast_mul,Nat.cast_sub (by omega : 1≤B),Nat.cast_one,Nat.cast_pow]
  field_simp
  <;> ring

theorem eventually_threshold_bound {B : ℕ} (hB : 1<B) {c : ℝ} (hc : 0<c) :
    ∀ᶠ j : ℕ in atTop, 0≤threshold B c j ∧
      (threshold B c j)^2≤2*(c^2*(B:ℝ)/((B:ℝ)-1))*Real.log (j+2:ℝ)+
        2*(c^2*(B:ℝ)/((B:ℝ)-1))*|Real.log (Real.log (B:ℝ))| := by
  have ht := (endpoint_strictMono hB).tendsto_atTop
  have hl := (loglog_nat_tendsto.comp (ht.comp (tendsto_add_atTop_nat 1))).eventually (eventually_ge_atTop (0:ℝ))
  filter_upwards [hl] with j hj
  constructor
  · unfold threshold; exact div_nonneg (mul_nonneg hc.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · rw [threshold_sq hB j hj,log_endpoint_succ hB]
    have hlog := Real.log_le_log (by positivity : (0:ℝ)<j+1) (show (j+1:ℝ)≤j+2 by linarith)
    have hB' : (1:ℝ)<B := by exact_mod_cast hB
    have hcoeff : 0≤2*(c^2*(B:ℝ)/((B:ℝ)-1)) := by positivity
    have := le_abs_self (Real.log (Real.log (B:ℝ)))
    nlinarith

end Erdos524.GeometricWalkScale
