import FareyGoldbach.ChenBalancedPairs
import FareyGoldbach.ChenSwitchingBoxes

/-! # Exact dyadic intervals for the balanced semiprime carrier -/

open Finset
open scoped Classical

namespace FareyGoldbach

def chenBalancedBoxPairs (N L i : ℕ) : Finset (ℕ×ℕ) :=
  (chenBalancedPairs N L).filter (fun p => chenShellIndex p.1=i)

def chenBalancedBoxLo (m : ℕ) : ℕ := max 1 m

theorem chenBalancedBoxLo_pos (m : ℕ) : 1≤chenBalancedBoxLo m := le_max_left ..

def chenBalancedBoxActive (L i m : ℕ) : Prop :=
  2^i<m ∧ L<m ∧ m.Prime

noncomputable def chenBalancedBoxA (L i k m : ℕ) : ℂ :=
  if chenBalancedBoxActive L i m ∧ m.Coprime k then 1 else 0

theorem chenBalancedBoxA_norm_le (L i k m : ℕ) : ‖chenBalancedBoxA L i k m‖≤1 := by
  unfold chenBalancedBoxA
  split_ifs <;> simp

private theorem balanced_shape {N L m w : ℕ} :
    (m,w)∈chenBalancedPairs N L ↔ m.Prime ∧ w.Prime ∧ L<m ∧ m≤w ∧ m*w<N := by
  simp only [chenBalancedPairs,Finset.mem_filter,Finset.mem_product,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨⟨_,hm⟩,_,hw⟩,hL,hmw,hn⟩
    exact ⟨hm,hw,hL,hmw,hn⟩
  · rintro ⟨hm,hw,hL,hmw,hn⟩
    exact ⟨⟨⟨hmw.trans ((Nat.le_mul_of_pos_left w hm.pos).trans hn.le),hm⟩,
      (Nat.le_mul_of_pos_left w hm.pos).trans hn.le,hw⟩,hL,hmw,hn⟩

private theorem chenBalancedBoxPairs_mem {N L i m w : ℕ} :
    (m,w)∈chenBalancedBoxPairs N L i ↔ m∈Finset.Icc 1 (chenSwitchBoxM i) ∧
      chenBalancedBoxActive L i m ∧
      w∈Finset.Icc (chenBalancedBoxLo m) (chenSwitchBoxHi N i m) ∧ w.Prime := by
  have hpow : 0 < (2:ℕ)^i := by positivity
  constructor
  · intro h
    obtain ⟨hp,hi⟩ := Finset.mem_filter.mp h
    obtain ⟨hm,hw,hL,hmw,hN⟩ := balanced_shape.mp hp
    have hs := chenShell_mem hm.two_le
    change chenShellIndex m=i at hi
    rw [hi] at hs
    obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hs
    have hW : w≤chenSwitchBoxW N i := by
      change w≤N/(2^i)
      apply (Nat.le_div_iff_mul_le hpow).mpr
      rw [Nat.mul_comm]
      exact (Nat.mul_le_mul_right _ hl.le).trans hN.le
    have hcap : w≤(N-1)/m := by
      apply (Nat.le_div_iff_mul_le hm.pos).mpr
      rw [Nat.mul_comm]
      omega
    exact ⟨Finset.mem_Icc.mpr ⟨hm.pos,hu⟩,⟨hl,hL,hm⟩,
      Finset.mem_Icc.mpr ⟨max_le hw.pos hmw,le_min hW hcap⟩,hw⟩
  · rintro ⟨hm,⟨hl,hL,hmP⟩,hw,hwP⟩
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hw
    have hcap : w≤(N-1)/m := hhi.trans (min_le_right ..)
    have hmul := (Nat.le_div_iff_mul_le hmP.pos).mp hcap
    rw [Nat.mul_comm] at hmul
    have hp : 0<m*w := Nat.mul_pos hmP.pos hwP.pos
    refine Finset.mem_filter.mpr ⟨balanced_shape.mpr
      ⟨hmP,hwP,hL,(le_max_right _ _).trans hlo,by omega⟩,?_⟩
    exact chenShellIndex_eq_of_mem (Finset.mem_Ioc.mpr ⟨hl,(Finset.mem_Icc.mp hm).2⟩)

noncomputable def chenBalancedBoxSum {q : ℕ} (N L i k : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m∈Finset.Icc 1 (chenSwitchBoxM i), chenBalancedBoxA L i k m*χ (m:ZMod q)*
    (∑ w∈Finset.Icc (chenBalancedBoxLo m) (chenSwitchBoxHi N i m),
      chenSwitchBoxB k w*χ (w:ZMod q))

/-- Each box is an exact product of one coefficient sequence with an interval
sum that depends on the first coordinate. -/
theorem chenBalancedBoxSum_eq {q : ℕ} (N L i k : ℕ)
    (χ : DirichletCharacter ℂ q) :
    chenBalancedBoxSum N L i k χ =
      ∑ p∈chenBalancedBoxPairs N L i,
        (if p.1.Coprime k then χ (p.1:ZMod q) else 0)*
        (if p.2.Coprime k then χ (p.2:ZMod q) else 0) := by
  let A := Finset.Icc 1 (chenSwitchBoxM i)
  let W := Finset.Icc 1 (chenSwitchBoxW N i)
  have heq : chenBalancedBoxPairs N L i =
      (A ×ˢ W).filter (fun p => chenBalancedBoxActive L i p.1 ∧
        p.2∈Finset.Icc (chenBalancedBoxLo p.1) (chenSwitchBoxHi N i p.1) ∧ p.2.Prime) := by
    ext p
    rcases p with ⟨m,w⟩
    rw [chenBalancedBoxPairs_mem,Finset.mem_filter,Finset.mem_product]
    dsimp
    constructor
    · rintro ⟨hm,ha,hw,hp⟩
      exact ⟨⟨hm,Finset.mem_Icc.mpr
        ⟨(chenBalancedBoxLo_pos _).trans (Finset.mem_Icc.mp hw).1,
          (Finset.mem_Icc.mp hw).2.trans (chenSwitchBoxHi_le ..)⟩⟩,ha,hw,hp⟩
    · rintro ⟨⟨hm,_⟩,ha,hw,hp⟩
      exact ⟨hm,ha,hw,hp⟩
  unfold chenBalancedBoxSum
  rw [heq,Finset.sum_filter,Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  let T := Finset.Icc (chenBalancedBoxLo m) (chenSwitchBoxHi N i m)
  have hT : T ⊆ W := fun w hw => Finset.mem_Icc.mpr
    ⟨(chenBalancedBoxLo_pos _).trans (Finset.mem_Icc.mp hw).1,
      (Finset.mem_Icc.mp hw).2.trans (chenSwitchBoxHi_le ..)⟩
  rw [Finset.mul_sum, ←Finset.sum_subset hT (fun w _ hw => by
    simp only [show w∉Finset.Icc (chenBalancedBoxLo m) (chenSwitchBoxHi N i m) from hw,
      false_and, and_false, ite_false])]
  refine Finset.sum_congr rfl fun w hw => ?_
  change w∈T at hw
  by_cases ha : chenBalancedBoxActive L i m <;> by_cases hm : m.Coprime k <;>
    by_cases hp : w.Prime <;> by_cases hk : w.Coprime k <;>
    simp [chenBalancedBoxA,chenSwitchBoxB,ha,hm,hp,hk,show w∈Finset.Icc (chenBalancedBoxLo m)
      (chenSwitchBoxHi N i m) from hw]

theorem chenBalanced_masked_sum_eq_sum_boxes {q : ℕ} (N L k : ℕ)
    (χ : DirichletCharacter ℂ q) :
    (∑ p∈chenBalancedPairs N L,
        (if p.1.Coprime k then χ (p.1:ZMod q) else 0)*
        (if p.2.Coprime k then χ (p.2:ZMod q) else 0)) =
      ∑ i∈Finset.range (N.log2+1), chenBalancedBoxSum N L i k χ := by
  simp_rw [chenBalancedBoxSum_eq,chenBalancedBoxPairs]
  apply (Finset.sum_fiberwise_of_maps_to ?_ _).symm
  rintro ⟨m,w⟩ hp
  obtain ⟨hm,hw,_,_,hN⟩ := balanced_shape.mp hp
  exact chenShellIndex_mem_range hm.two_le
    ((Nat.le_mul_of_pos_right m hw.pos).trans hN.le)

theorem chenBalancedBoxSum_eq_zero_of_empty {q : ℕ} {N L i k : ℕ}
    (he : chenBalancedBoxPairs N L i=∅) (χ : DirichletCharacter ℂ q) :
    chenBalancedBoxSum N L i k χ=0 := by rw [chenBalancedBoxSum_eq,he,Finset.sum_empty]

theorem chenBalancedBox_ranges {N L i : ℕ}
    (hy : (N:ℝ)^((1:ℝ)/4)+1≤(L:ℝ)) (hN : 1≤N)
    (hne : (chenBalancedBoxPairs N L i).Nonempty) :
    1≤chenSwitchBoxW N i ∧ chenSwitchBoxW N i≤N ∧
      (chenSwitchBoxM i:ℝ)*(chenSwitchBoxW N i:ℝ)≤2*(N:ℝ) ∧
      (chenSwitchBoxM i:ℝ)≤2*(N:ℝ)^((3:ℝ)/4) ∧
      (chenSwitchBoxW N i:ℝ)≤2*(N:ℝ)^((3:ℝ)/4) := by
  obtain ⟨⟨m,w⟩,hp⟩ := hne
  obtain ⟨hm,⟨hl,hLm,_⟩,hw,hwP⟩ := chenBalancedBoxPairs_mem.mp hp
  obtain ⟨_,_,_,hmw,hprod⟩ := balanced_shape.mp (Finset.mem_filter.mp hp).1
  have hW₁ : 1≤chenSwitchBoxW N i :=
    Nat.le_trans hwP.pos ((Finset.mem_Icc.mp hw).2.trans (chenSwitchBoxHi_le ..))
  have hW₂ : chenSwitchBoxW N i≤N := Nat.div_le_self ..
  let Q : ℕ := 2^i
  have hprodQ : Q*chenSwitchBoxW N i≤N := by
    dsimp [Q,chenSwitchBoxW]
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self .. 
  have hMW : (chenSwitchBoxM i:ℝ)*(chenSwitchBoxW N i:ℝ)≤2*(N:ℝ) := by
    unfold chenSwitchBoxM
    exact_mod_cast (show (2*2^i)*chenSwitchBoxW N i≤2*N by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hprodQ)
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hpwr : (N:ℝ)^(1/4:ℝ)*(N:ℝ)^(3/4:ℝ)=(N:ℝ) := by
    rw [←Real.rpow_add hn, show (1/4:ℝ)+3/4=1 by norm_num, Real.rpow_one]
  have hYP : (N:ℝ)^(1/4:ℝ)≤(L:ℝ) := by linarith only [hy]
  have hym : L≤m := hLm.le
  have hyw : L≤w := hym.trans hmw
  have hmPow : (m:ℝ)≤(N:ℝ)^(3/4:ℝ) := by
    apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hn (1/4:ℝ))).mp
    rw [hpwr]
    exact (mul_le_mul_of_nonneg_right (hYP.trans (Nat.cast_le.mpr hyw)) (Nat.cast_nonneg _)).trans
      (by exact_mod_cast (show w*m≤N by rw [Nat.mul_comm]; exact hprod.le))
  have hMpow : (chenSwitchBoxM i:ℝ)≤2*(N:ℝ)^(3/4:ℝ) := by
    have hQ : (Q:ℝ)≤(m:ℝ) := Nat.cast_le.mpr hl.le
    change ((2*Q:ℕ):ℝ)≤_
    rw [Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hQ,hmPow]
  have hwPow : (chenSwitchBoxW N i:ℝ)≤2*(N:ℝ)^(3/4:ℝ) := by
    apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hn (1/4:ℝ))).mp
    rw [←mul_assoc,mul_comm ((N:ℝ)^(1/4:ℝ)) 2,mul_assoc,hpwr]
    apply le_trans (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)) hMW
    exact hYP.trans (Nat.cast_le.mpr (hym.trans (Finset.mem_Icc.mp hm).2))
  exact ⟨hW₁,hW₂,hMW,hMpow,hwPow⟩

end FareyGoldbach
