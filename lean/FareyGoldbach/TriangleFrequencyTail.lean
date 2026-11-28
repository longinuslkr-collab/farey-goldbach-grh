import FareyGoldbach.TriangularFrequencyKernel

/-! # A uniform tail estimate for finite nonnegative squared-sinc convolutions -/

open Finset
open scoped BigOperators Classical

namespace FareyGoldbach

private theorem mass_in_half_block (s b : Finset ℕ) (a : ℕ→ℝ) {η B y : ℝ}
    (hη : 0<η) (ha : ∀ j∈s,0≤a j) (hb : b ⊆ s)
    (hconv : ∑ j∈s,a j*triangleFrequency η ((j:ℝ)-y) ≤ B)
    (hnear : ∀ j∈b,|(j:ℝ)-y|≤1/(2*η)) :
    ∑ j∈b,a j ≤ 4*B := by
  have h : (1/4:ℝ) * ∑ j∈b,a j ≤ B := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) <|
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (f:=fun j => a j*triangleFrequency η ((j:ℝ)-y)) hb
        (fun j hj _ => mul_nonneg (ha j hj) (triangleFrequency_nonneg ..))) hconv
    rw [mul_comm (1/4:ℝ)]
    exact mul_le_mul_of_nonneg_left (triangleFrequency_near hη (hnear j hj)) (ha j (hb hj))
  linarith

private lemma centered_block_near {η v k : ℝ} (hη : 0<η) (hlo : k≤η*v)
    (hhi : η*v≤k+1) : |v-(k+1/2)/η| ≤ 1/(2*η) := by
  apply (le_div_iff₀ (by positivity : 0<2*η)).2
  rw [←abs_of_pos (by positivity : 0<2*η), ←abs_mul]
  have he : (v-(k+1/2)/η)*(2*η) = 2*(η*v-k)-1 := by field_simp; ring
  rw [he,abs_le]; constructor <;> linarith

private lemma shell_mass (s b : Finset ℕ) (a : ℕ→ℝ) {η B x : ℝ}
    (hη : 0<η) (ha : ∀ j∈s,0≤a j) (hb : b⊆s)
    (hconv : ∀ y : ℝ,∑ j∈s,a j*triangleFrequency η ((j:ℝ)-y) ≤ B)
    (k : ℕ) (hband : ∀ j∈b, (k:ℝ)≤η*|(j:ℝ)-x| ∧ η*|(j:ℝ)-x|≤(k:ℝ)+1) :
    ∑ j∈b,a j ≤ 8*B := by
  let p := fun j:ℕ => x≤(j:ℝ)
  let d := ((k:ℝ)+1/2)/η
  have hp := mass_in_half_block s (b.filter p) a hη ha (fun _ hj => hb (Finset.mem_filter.mp hj).1)
    (hconv (x+d)) (fun j hj => by
      obtain ⟨hb',hs⟩ := Finset.mem_filter.mp hj
      obtain ⟨hlo,hhi⟩ := hband j hb'
      rw [show (j:ℝ)-(x+d) = |(j:ℝ)-x|-d by rw [abs_of_nonneg (sub_nonneg.mpr hs)]; ring]
      exact centered_block_near hη hlo hhi)
  have hm := mass_in_half_block s (b.filter (fun j => ¬p j)) a hη ha (fun _ hj => hb (Finset.mem_filter.mp hj).1)
    (hconv (x-d)) (fun j hj => by
      obtain ⟨hb',hs⟩ := Finset.mem_filter.mp hj
      obtain ⟨hlo,hhi⟩ := hband j hb'
      rw [show (j:ℝ)-(x-d) = -(|(j:ℝ)-x|-d) by rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hs))]; ring,
        abs_neg]
      exact centered_block_near hη hlo hhi)
  have he := Finset.sum_filter_add_sum_filter_not b p a
  linarith only [hp,hm,he]

private theorem sum_inverse_square_block (M N : ℕ) (hM : 1≤M) (hMN : M≤N) :
    (∑ k ∈ Finset.Ico M N,1/(k:ℝ)^2) ≤ 2*(1/(M:ℝ)-1/(N:ℝ)) := by
  induction N,hMN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk' : (1:ℝ)≤k := by exact_mod_cast hM.trans hk
    have hk0 : (0:ℝ)<k := zero_lt_one.trans_le hk'
    have hs : 1/(k:ℝ)^2 ≤ 2*(1/(k:ℝ)-1/((k:ℝ)+1)) := by
      field_simp; nlinarith
    rw [Finset.sum_Ico_succ_top hk,Nat.cast_succ]
    linarith only [ih,hs]

/-- A bound at every real translate controls the spectral tail at the chosen
center, uniformly in the finite support and the bandwidth. -/
theorem triangleFrequency_tail (s : Finset ℕ) (a : ℕ→ℝ) {η B : ℝ}
    (hη : 0<η) (ha : ∀ j∈s,0≤a j)
    (hconv : ∀ y : ℝ,∑ j∈s,a j*triangleFrequency η ((j:ℝ)-y) ≤ B)
    (M : ℕ) (hM : 1≤M) (x : ℝ) :
    ∑ j∈s.filter (fun j : ℕ => (M:ℝ)/η≤|(j:ℝ)-x|),a j*triangleFrequency η ((j:ℝ)-x) ≤ 16*B/M := by
  let t := s.filter fun j : ℕ => (M:ℝ)/η≤|(j:ℝ)-x|
  let k (j : ℕ) := ⌊η*|(j:ℝ)-x|⌋₊
  let N := max M (t.sup k+1)
  let T := Finset.Ico M N
  let w (j : ℕ) := a j*triangleFrequency η ((j:ℝ)-x)
  have hB : 0≤B := le_trans (Finset.sum_nonneg (fun j hj => mul_nonneg (ha j hj) (triangleFrequency_nonneg ..))) (hconv x)
  have hmap (j) (hj : j∈t) : k j∈T := by
    refine Finset.mem_Ico.mpr ⟨Nat.le_floor ?_,lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup hj)) (le_max_right ..)⟩
    have h := (div_le_iff₀ hη).mp (Finset.mem_filter.mp hj).2
    simpa only [mul_comm η] using h
  have hf := Finset.sum_fiberwise_of_maps_to (s:=t) (t:=T) (g:=k) hmap w
  change ∑ j∈t,w j ≤ _
  rw [←hf]
  have hs (m : ℕ) (hm : m∈T) : ∑ j∈t.filter (fun j => k j=m),w j ≤ (8*B)*(1/(m:ℝ)^2) := by
    let b := t.filter fun j => k j=m
    have hsub : b⊆s := (Finset.filter_subset ..).trans (Finset.filter_subset ..)
    have hband (j) (hj : j∈b) : (m:ℝ)≤η*|(j:ℝ)-x| ∧ η*|(j:ℝ)-x|≤(m:ℝ)+1 := by
      have he := (Finset.mem_filter.mp hj).2
      rw [←he]
      exact ⟨Nat.floor_le (by positivity), (Nat.lt_floor_add_one _).le⟩
    have hmass := shell_mass s b a hη ha hsub hconv m hband
    have hm0 : (0:ℝ)<m := Nat.cast_pos.mpr (hM.trans (Finset.mem_Ico.mp hm).1)
    calc _ ≤ ∑ j∈b,a j*(1/(m:ℝ)^2) := by
           refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (ha j (hsub hj))
           have hlo := (hband j hj).1
           have hz : (j:ℝ)-x ≠ 0 := fun h => by rw [h,abs_zero,mul_zero] at hlo; linarith
           exact (triangleFrequency_decay hη hz).trans (one_div_le_one_div_of_le (sq_pos_of_pos hm0)
             (pow_le_pow_left₀ hm0.le hlo 2))
         _ ≤ _ := by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hmass (by positivity)
  refine (Finset.sum_le_sum hs).trans ?_
  rw [←Finset.mul_sum]
  have h := sum_inverse_square_block M N hM (le_max_left ..)
  have h' := mul_le_mul_of_nonneg_left h (by positivity : 0≤8*B)
  have hn : 0≤(8*B)*(1/(N:ℝ)) := by positivity
  dsimp only [T]
  refine h'.trans ?_
  calc _ ≤ (8*B)*(2*(1/(M:ℝ))) := by linarith only [hn]
       _ = _ := by ring

end FareyGoldbach
