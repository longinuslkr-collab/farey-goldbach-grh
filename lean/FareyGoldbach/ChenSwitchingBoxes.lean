import FareyGoldbach.ChenSwitchingPairs
import FareyGoldbach.ChenSwitchingScales

/-! # Exact dyadic boxes for the first two prime factors -/

open Finset
open scoped Classical

namespace FareyGoldbach

def chenSwitchBoxPairs (N z y i : ℕ) : Finset (ℕ×ℕ) :=
  (chenSwitchPairs N z y).filter (fun p => chenShellIndex p.1=i)

def chenSwitchBoxM (i : ℕ) : ℕ := 2*2^i

def chenSwitchBoxW (N i : ℕ) : ℕ := N/(2^i)

def chenSwitchBoxLo (m : ℕ) : ℕ := max 1 (chenSwitchV m)

def chenSwitchBoxHi (N i m : ℕ) : ℕ := min (chenSwitchBoxW N i) ((N-1)/m)

def chenSwitchBoxActive (z y i m : ℕ) : Prop :=
  2^i<m ∧ chenSwitchActive z y m

noncomputable def chenSwitchBoxA (z y i k m : ℕ) : ℂ :=
  if chenSwitchBoxActive z y i m ∧ m.Coprime k then 1 else 0

noncomputable def chenSwitchBoxB (k w : ℕ) : ℂ :=
  if w.Prime ∧ w.Coprime k then 1 else 0

theorem chenSwitchBoxA_norm_le (z y i k m : ℕ) : ‖chenSwitchBoxA z y i k m‖≤1 := by
  unfold chenSwitchBoxA
  split_ifs <;> simp

theorem chenSwitchBoxB_norm_le (k w : ℕ) : ‖chenSwitchBoxB k w‖≤1 := by
  unfold chenSwitchBoxB
  split_ifs <;> simp

theorem chenSwitchBoxLo_pos (m : ℕ) : 1≤chenSwitchBoxLo m := le_max_left ..

theorem chenSwitchBoxHi_le (N i m : ℕ) : chenSwitchBoxHi N i m≤chenSwitchBoxW N i := min_le_left ..

private theorem chenSwitchBoxPairs_mem {N z y i m w : ℕ} :
    (m,w)∈chenSwitchBoxPairs N z y i ↔
      m∈Finset.Icc 1 (chenSwitchBoxM i) ∧
      chenSwitchBoxActive z y i m ∧
      w∈Finset.Icc (chenSwitchBoxLo m) (chenSwitchBoxHi N i m) ∧ w.Prime := by
  have hpow : 0 < (2:ℕ)^i := by positivity
  constructor
  · intro h
    obtain ⟨hp,hi⟩ := Finset.mem_filter.mp h
    obtain ⟨hm,ha,hw,hvw,hN⟩ := mem_chenSwitchPairs_iff.mp hp
    have hm2 : 2≤m := by
      have hv : 2≤chenSwitchV m := ha.2.1.two_le
      have hV : chenSwitchV m ≤ m := Nat.div_le_self ..
      omega
    have hs := chenShell_mem hm2
    change chenShellIndex m=i at hi
    rw [hi] at hs
    obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hs
    have hW : w≤chenSwitchBoxW N i := by
      change w≤N/(2^i)
      apply (Nat.le_div_iff_mul_le hpow).mpr
      rw [Nat.mul_comm]
      exact (Nat.mul_le_mul_right _ hl.le).trans hN.le
    have hcap : w≤(N-1)/m := by
      apply (Nat.le_div_iff_mul_le hm).mpr
      rw [Nat.mul_comm]
      omega
    exact ⟨Finset.mem_Icc.mpr ⟨hm,hu⟩,⟨hl,ha⟩,
      Finset.mem_Icc.mpr ⟨max_le hw.pos hvw,le_min hW hcap⟩,hw⟩
  · rintro ⟨hm,⟨hl,ha⟩,hw,hwp⟩
    have hm' := (Finset.mem_Icc.mp hm).1
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hw
    have hcap : w≤(N-1)/m := hhi.trans (min_le_right ..)
    have hmul := (Nat.le_div_iff_mul_le hm').mp hcap
    rw [Nat.mul_comm] at hmul
    have hp : 0<m*w := Nat.mul_pos hm' hwp.pos
    have hmw : m*w<N := by omega
    refine Finset.mem_filter.mpr ⟨mem_chenSwitchPairs_iff.mpr
      ⟨hm',ha,hwp,(le_max_right _ _).trans hlo,hmw⟩,?_⟩
    exact chenShellIndex_eq_of_mem (Finset.mem_Ioc.mpr ⟨hl,(Finset.mem_Icc.mp hm).2⟩)

noncomputable def chenSwitchBoxSum {q : ℕ} (N z y i k : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m∈Finset.Icc 1 (chenSwitchBoxM i), chenSwitchBoxA z y i k m*χ (m:ZMod q)*
    (∑ w∈Finset.Icc (chenSwitchBoxLo m) (chenSwitchBoxHi N i m),
      chenSwitchBoxB k w*χ (w:ZMod q))

/-- Each box is an exact product of one coefficient sequence with an interval
sum that depends on the first coordinate. -/
theorem chenSwitchBoxSum_eq {q : ℕ} (N z y i k : ℕ)
    (χ : DirichletCharacter ℂ q) :
    chenSwitchBoxSum N z y i k χ =
      ∑ p∈chenSwitchBoxPairs N z y i,
        (if p.1.Coprime k then χ (p.1:ZMod q) else 0)*
        (if p.2.Coprime k then χ (p.2:ZMod q) else 0) := by
  let A := Finset.Icc 1 (chenSwitchBoxM i)
  let W := Finset.Icc 1 (chenSwitchBoxW N i)
  have heq : chenSwitchBoxPairs N z y i =
      (A ×ˢ W).filter (fun p => chenSwitchBoxActive z y i p.1 ∧
        p.2∈Finset.Icc (chenSwitchBoxLo p.1) (chenSwitchBoxHi N i p.1) ∧ p.2.Prime) := by
    ext p
    rcases p with ⟨m,w⟩
    rw [chenSwitchBoxPairs_mem,Finset.mem_filter,Finset.mem_product]
    dsimp
    constructor
    · rintro ⟨hm,ha,hw,hp⟩
      exact ⟨⟨hm,Finset.mem_Icc.mpr
        ⟨(chenSwitchBoxLo_pos _).trans (Finset.mem_Icc.mp hw).1,
          (Finset.mem_Icc.mp hw).2.trans (chenSwitchBoxHi_le ..)⟩⟩,ha,hw,hp⟩
    · rintro ⟨⟨hm,_⟩,ha,hw,hp⟩
      exact ⟨hm,ha,hw,hp⟩
  unfold chenSwitchBoxSum
  rw [heq,Finset.sum_filter,Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  let T := Finset.Icc (chenSwitchBoxLo m) (chenSwitchBoxHi N i m)
  have hT : T ⊆ W := fun w hw => Finset.mem_Icc.mpr
    ⟨(chenSwitchBoxLo_pos _).trans (Finset.mem_Icc.mp hw).1,
      (Finset.mem_Icc.mp hw).2.trans (chenSwitchBoxHi_le ..)⟩
  rw [Finset.mul_sum, ←Finset.sum_subset hT (fun w _ hw => by
    simp only [show w∉Finset.Icc (chenSwitchBoxLo m) (chenSwitchBoxHi N i m) from hw,
      false_and, and_false, ite_false])]
  refine Finset.sum_congr rfl fun w hw => ?_
  change w∈T at hw
  by_cases ha : chenSwitchBoxActive z y i m <;> by_cases hm : m.Coprime k <;>
    by_cases hp : w.Prime <;> by_cases hk : w.Coprime k <;>
    simp [chenSwitchBoxA,chenSwitchBoxB,ha,hm,hp,hk,show w∈Finset.Icc (chenSwitchBoxLo m)
      (chenSwitchBoxHi N i m) from hw]

theorem chenSwitch_masked_sum_eq_sum_boxes {q : ℕ} (N z y k : ℕ)
    (χ : DirichletCharacter ℂ q) :
    (∑ p∈chenSwitchPairs N z y,
        (if p.1.Coprime k then χ (p.1:ZMod q) else 0)*
        (if p.2.Coprime k then χ (p.2:ZMod q) else 0)) =
      ∑ i∈Finset.range (N.log2+1), chenSwitchBoxSum N z y i k χ := by
  simp_rw [chenSwitchBoxSum_eq,chenSwitchBoxPairs]
  apply (Finset.sum_fiberwise_of_maps_to ?_ _).symm
  rintro ⟨m,w⟩ hp
  obtain ⟨hm,ha,hw,_,hN⟩ := mem_chenSwitchPairs_iff.mp hp
  have hV : chenSwitchV m≤m := Nat.div_le_self ..
  have h₂ := ha.2.1.two_le
  exact chenShellIndex_mem_range (h₂.trans hV)
    ((Nat.le_mul_of_pos_right m hw.pos).trans hN.le)

theorem chenSwitchBoxSum_eq_zero_of_empty {q : ℕ} {N z y i k : ℕ}
    (he : chenSwitchBoxPairs N z y i=∅) (χ : DirichletCharacter ℂ q) :
    chenSwitchBoxSum N z y i k χ=0 := by rw [chenSwitchBoxSum_eq,he,Finset.sum_empty]

theorem chenSwitchBox_ranges {N z y i : ℕ}
    (hy : (N:ℝ)^((1:ℝ)/4)+1≤(y:ℝ)) (hN : 1≤N)
    (hne : (chenSwitchBoxPairs N z y i).Nonempty) :
    1≤chenSwitchBoxW N i ∧ chenSwitchBoxW N i≤N ∧
      (chenSwitchBoxM i:ℝ)*(chenSwitchBoxW N i:ℝ)≤2*(N:ℝ) ∧
      (chenSwitchBoxM i:ℝ)≤2*(N:ℝ)^((3:ℝ)/4) ∧
      (chenSwitchBoxW N i:ℝ)≤2*(N:ℝ)^((3:ℝ)/4) := by
  obtain ⟨⟨m,w⟩,hp⟩ := hne
  obtain ⟨hm,⟨hl,ha⟩,hw,hwP⟩ := chenSwitchBoxPairs_mem.mp hp
  obtain ⟨hm',ha',hwP',hvw,hprod⟩ := mem_chenSwitchPairs_iff.mp (Finset.mem_filter.mp hp).1
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
  have hYP : (N:ℝ)^(1/4:ℝ)≤(y:ℝ) := by linarith only [hy]
  have hyv : y≤chenSwitchV m := ha.2.2.2.2
  have hym : y≤m := hyv.trans (Nat.div_le_self ..)
  have hyw : y≤w := hyv.trans hvw
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
