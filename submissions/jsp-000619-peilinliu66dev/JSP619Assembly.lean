import JSP619Expansion
import JSP619Bands
import JSP619CycleExtraction
import JSP619Components

/-!
# JSP-000619 / Erdos 752: assembly, explicit constants, all s >= 1

The intermediate interface hMoore : JSP619.MooreBound is proved in
JSP619Expansion and instantiated by every terminal theorem in JSP619.lean.
No unproved mathematical input remains in those terminal theorems.

The resulting conclusion concerns the cardinality of lengths of actual
SimpleGraph.Walk.IsCycle witnesses. The explicit constants are
  k0 = 576,   c_s = 1 / (24 * 192^s).
Mathematical attribution: Sudakov--Verstraete, Theorem 2.2; relaxed constants.
-/
noncomputable section
open Finset Function
namespace JSP619
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Core -> expansion -> DFS path -> equal-return cycles in a connected graph. -/
theorem cycle_count_connected_of_moore (hMoore : MooreBound.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (d s m : ℕ) (hd : 0 < d) (hs : 0 < s) (hm : 2 ≤ m)
    (hdeg : ∀ v, 48 * (d + 1) ≤ G.degree v) (hgirth : HighGirth G s)
    (hsize : 3 * m ≤ d ^ s) :
    m ≤ 4 * (cycleLengths G).card := by
  classical
  let r : V := Classical.choice hconn.nonempty
  let T := layerTreeOfConnected hconn r
  obtain ⟨i, B, hBne, hBsub, hBdeg⟩ := T.exists_band_core d hdeg
  obtain ⟨b, hb⟩ := hBne
  letI : Nonempty ↥B := ⟨⟨b, hb⟩⟩
  let H := induced (band G T.level i) B
  let f : H →g G := (bandHom G T.level i).comp (inducedHom (band G T.level i) B)
  have hf : Injective f := Subtype.val_injective
  have hHdeg : ∀ v : ↥B, 6 * (d + 1) ≤ H.degree v := by
    intro v
    rw [induced_degree]
    exact hBdeg v.1 v.2
  have hHgirth : HighGirth H s := highGirth_map f hf hgirth
  obtain ⟨x, y, p, hp, hplen⟩ :=
    long_path_of_minDegree hMoore H d s m hd hs (by omega) hHdeg hHgirth hsize
  let P := p.map f
  have hP : P.IsPath := hp.map hf
  have hPlen : 2 * m ≤ P.length := by simpa [P] using hplen
  have hhigh : ∀ v ∈ P.support, i ≤ T.level v := by
    intro v hv
    have hv' : v ∈ p.support.map f := by simpa [P] using hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv'
    have hh := mem_bandVertices.mp (hBsub w.2)
    change i ≤ T.level w.1
    omega
  have hstep : ∀ j : ℕ, j < P.length →
      min (T.level (P.getVert j)) (T.level (P.getVert (j + 1))) = i := by
    intro j hj
    have hj' : j < p.length := by simpa [P] using hj
    have h := p.adj_getVert_succ hj'
    change G.Adj (p.getVert j).1 (p.getVert (j + 1)).1 ∧
      min (T.level (p.getVert j).1) (T.level (p.getVert (j + 1)).1) = i at h
    have h1 : P.getVert j = (p.getVert j).1 := SimpleGraph.Walk.getVert_map f p j
    have h2 : P.getVert (j + 1) = (p.getVert (j + 1)).1 :=
      SimpleGraph.Walk.getVert_map f p (j + 1)
    rw [h1, h2]
    exact h.2
  exact cycle_count_of_band_path T m i hm P hP hPlen hhigh hstep

/-- Connected-component reduction preserves the same numerical bound. -/
theorem cycle_count_of_moore (hMoore : MooreBound.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (d s m : ℕ) (hd : 0 < d) (hs : 0 < s) (hm : 2 ≤ m)
    (hdeg : ∀ v, 48 * (d + 1) ≤ G.degree v) (hgirth : HighGirth G s)
    (hsize : 3 * m ≤ d ^ s) :
    m ≤ 4 * (cycleLengths G).card := by
  classical
  let r : V := Classical.choice (inferInstance : Nonempty V)
  let A := componentVertices G r
  let H := induced G A
  have hHd : ∀ v : ↥A, 48 * (d + 1) ≤ H.degree v := by
    intro v
    rw [component_degree]
    exact hdeg v.1
  have hHg : HighGirth H s := highGirth_map (inducedHom G A)
    Subtype.val_injective hgirth
  have hc := cycle_count_connected_of_moore hMoore H (component_connected G r)
    d s m hd hs hm hHd hHg hsize
  have hcard : (cycleLengths H).card ≤ (cycleLengths G).card :=
    card_cycleLengths_map_le (inducedHom G A) Subtype.val_injective
  exact hc.trans (Nat.mul_le_mul_left 4 hcard)

lemma nat_pow_mono_base {a b : ℕ} (h : a ≤ b) (s : ℕ) : a ^ s ≤ b ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, pow_succ]
    exact Nat.mul_le_mul ih h

lemma nat_le_pow_of_pos (d s : ℕ) (hd : 0 < d) (hs : 0 < s) : d ≤ d ^ s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have hp : 1 ≤ d ^ t := Nat.succ_le_of_lt (pow_pos hd _)
  rw [pow_succ]
  simpa using Nat.mul_le_mul_right d hp

/-- Explicit integer form of the full original bound, with the Moore input visible. -/
theorem erdos752_nat_from_moore (hMoore : MooreBound.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (s k : ℕ) (hs : 0 < s) (hk : 576 ≤ k)
    (hdeg : ∀ v, k ≤ G.degree v) (hgirth : HighGirth G s) :
    k ^ s ≤ (24 * 192 ^ s) * (cycleLengths G).card := by
  classical
  let d := k / 96
  let m := d ^ s / 3
  have hd6 : 6 ≤ d := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 96)).mpr
    omega
  have hd : 0 < d := by omega
  have hd96 : 96 * d ≤ k := Nat.mul_div_le k 96
  have hdegD : ∀ v, 48 * (d + 1) ≤ G.degree v := by
    intro v
    have h := hdeg v
    omega
  have hrem : k % 96 < 96 := Nat.mod_lt k (by decide)
  have hdec : k % 96 + 96 * d = k := Nat.mod_add_div k 96
  have hkd : k ≤ 192 * d := by omega
  have hpow : 6 ≤ d ^ s := hd6.trans (nat_le_pow_of_pos d s hd hs)
  have hm : 2 ≤ m := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
    omega
  have hsize : 3 * m ≤ d ^ s := Nat.mul_div_le (d ^ s) 3
  have hpowm : d ^ s ≤ 6 * m := by
    have hr := Nat.mod_lt (d ^ s) (by decide : 0 < 3)
    have he : d ^ s % 3 + 3 * m = d ^ s := Nat.mod_add_div (d ^ s) 3
    omega
  have hcount := cycle_count_of_moore hMoore G d s m hd hs hm hdegD hgirth hsize
  have hpowCount : d ^ s ≤ 24 * (cycleLengths G).card := by omega
  calc
    k ^ s ≤ (192 * d) ^ s := nat_pow_mono_base hkd s
    _ = 192 ^ s * d ^ s := mul_pow _ _ _
    _ ≤ 192 ^ s * (24 * (cycleLengths G).card) :=
      Nat.mul_le_mul_left _ hpowCount
    _ = (24 * 192 ^ s) * (cycleLengths G).card := by ring

/-- The fixed positive constant in the Omega_s statement. -/
def erdos752Constant (s : ℕ) : ℝ := 1 / (24 * (192 : ℝ) ^ s)

lemma erdos752Constant_pos (s : ℕ) : 0 < erdos752Constant s := by
  unfold erdos752Constant
  positivity

/-- Real-valued original statement, uniformly over all k >= 576 and all finite
nonempty graphs. This intermediate theorem takes the proved Moore interface explicitly. -/
theorem erdos752_from_moore (hMoore : MooreBound.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (s k : ℕ) (hs : 0 < s) (hk : 576 ≤ k)
    (hdeg : ∀ v, k ≤ G.degree v) (hgirth : HighGirth G s) :
    erdos752Constant s * (k : ℝ) ^ s ≤ ((cycleLengths G).card : ℝ) := by
  have hn := erdos752_nat_from_moore hMoore G s k hs hk hdeg hgirth
  have hr : (k : ℝ) ^ s ≤ (24 * (192 : ℝ) ^ s) * ((cycleLengths G).card : ℝ) := by
    exact_mod_cast hn
  have hpos : 0 < 24 * (192 : ℝ) ^ s := by positivity
  unfold erdos752Constant
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using hr)

/-- Adapter from Mathlib's natural-valued girth convention. -/
theorem erdos752_girth_from_moore (hMoore : MooreBound.{u})
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (s k : ℕ) (hs : 0 < s) (hk : 576 ≤ k)
    (hdeg : ∀ v, k ≤ G.degree v) (hgirth : 2 * s < G.girth) :
    erdos752Constant s * (k : ℝ) ^ s ≤ ((cycleLengths G).card : ℝ) :=
  erdos752_from_moore hMoore G s k hs hk hdeg (highGirth_of_girth hgirth)

#print axioms JSP619.erdos752_from_moore
#print axioms JSP619.erdos752_girth_from_moore
end JSP619
end
