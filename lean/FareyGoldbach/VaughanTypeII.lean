import FareyGoldbach.ChenLargeConductor

/-! # Vaughan Type II sums over the large conductors -/

open Finset
open scoped Classical

namespace FareyGoldbach

theorem vaughan_large_conductor_interval_bound (M W D R N : ℕ) (a b : ℕ→ℂ) (lo hi : ℕ→ℕ)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B) (hN : 1≤N) (hW : 1≤W) (hWN : W≤N)
    (hDN : D≤N) (hR : 1≤R) (hMW : (M:ℝ)*W≤2*N)
    (hM : (M:ℝ)≤2*(N:ℝ)^(4/5:ℝ)) (hWpow : (W:ℝ)≤2*(N:ℝ)^(4/5:ℝ))
    (ha : (∑ m∈Icc 1 M, ‖a m‖^2)≤(M:ℝ)*A^2)
    (hb : (∑ w∈Icc 1 W, ‖b w‖^2)≤(W:ℝ)*B^2)
    (hlo : ∀ m∈Icc 1 M,1≤lo m) (hhi : ∀ m∈Icc 1 M,hi m≤W) :
    (∑ q∈Ioc R D, chenPrimitiveNorm q (fun χ =>
      ∑ m∈Icc 1 M, a m*χ (m:ZMod q)*(∑ w∈Icc (lo m) (hi m),b w*χ (w:ZMod q)))/(q:ℝ)) ≤
      100000*(chenSwitchLog N)^2*(A*B)*((N:ℝ)/R+(N:ℝ)^(9/10:ℝ)+(D:ℝ)*Real.sqrt N) := by
  simpa only [show ((1:ℝ)+4/5)/2=9/10 by norm_num] using
    chen_large_conductor_interval_energy M W D R N a b lo hi (α:=4/5) hA hB hN hW hWN hDN hR
      hMW hM hWpow ha hb hlo hhi

/-- Split the first variable into exact binary shells. On each shell the
hyperbola height is at most X divided by the shell's lower endpoint. -/
theorem vaughan_typeII_large_conductor (U V X D R N : ℕ) (a b : ℕ→ℂ) (lo : ℕ→ℕ)
    {A B : ℝ} (hA : 0≤A) (hB : 0≤B) (hN : 1≤N) (hU : 1≤U) (hX : X≤N)
    (hV : V≤N) (hD : D≤N) (hR : 1≤R) (hsmall : (N:ℝ)^(1/5:ℝ)≤(U:ℝ)+1)
    (hbig : (V:ℝ)≤2*(N:ℝ)^(4/5:ℝ))
    (ha : ∀ t≤N, (∑ m∈Icc 1 t, ‖a m‖^2)≤(t:ℝ)*A^2)
    (hb : ∀ t≤N, (∑ w∈Icc 1 t, ‖b w‖^2)≤(t:ℝ)*B^2) (hlo : ∀ m, 1≤lo m) :
    (∑ q∈Ioc R D, chenPrimitiveNorm q (fun χ =>
      ∑ m∈Icc (U+1) V, a m*χ (m:ZMod q)*(∑ w∈Icc (lo m) (X/m),b w*χ (w:ZMod q)))/(q:ℝ)) ≤
      300000*(chenSwitchLog N)^3*(A*B)*((N:ℝ)/R+(N:ℝ)^(9/10:ℝ)+(D:ℝ)*Real.sqrt N) := by
  let J := range (N.log2+1)
  let S (i : ℕ) := (Icc (U+1) V).filter (fun m => chenShellIndex m=i)
  let P (i q : ℕ) (χ : DirichletCharacter ℂ q) :=
    ∑ m∈S i, a m*χ (m:ZMod q)*(∑ w∈Icc (lo m) (X/m),b w*χ (w:ZMod q))
  let G := (N:ℝ)/R+(N:ℝ)^(9/10:ℝ)+(D:ℝ)*Real.sqrt N
  let L := chenSwitchLog N
  have hL : 0≤L := zero_le_one.trans (one_le_chenSwitchLog hN)
  have hG : 0≤G := by dsimp [G]; positivity
  have hsplit (q : ℕ) (χ : DirichletCharacter ℂ q) :
      ∑ m∈Icc (U+1) V, a m*χ (m:ZMod q)*(∑ w∈Icc (lo m) (X/m),b w*χ (w:ZMod q))
      = ∑ i∈J,P i q χ := by
    simp only [P,S,sum_filter]
    rw [Finset.sum_comm (s:=J)]
    apply Finset.sum_congr rfl
    intro m hm
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hm
    rw [sum_ite_eq]
    simp [J,chenShellIndex_mem_range (by omega : 2≤m) (h₂.trans hV)]
  have heach (i : ℕ) : (∑ q∈Ioc R D, chenPrimitiveNorm q (P i q)/(q:ℝ)) ≤
      100000*L^2*(A*B)*G := by
    let k := 2^i
    let H := max (U+1) (k+1)
    let M := min V (2*k)
    let W := max 1 (X/H)
    let a' (m : ℕ) := if m∈S i then a m else 0
    let hi (m : ℕ) := min W (X/m)
    have hH : 0<H := by dsimp [H]; omega
    have hkH : k≤H := by dsimp [H]; omega
    have hUH : U+1≤H := le_max_left .. 
    have hM : M≤V := min_le_left .. 
    have hW : 1≤W := le_max_left ..
    have hWN : W≤N := max_le hN ((Nat.div_le_self ..).trans hX)
    have hMN := hM.trans hV
    have hMW : M*W≤2*N := by
      by_cases h : X/H≤1
      · have hw : W=1 := max_eq_left h
        rw [hw,mul_one]
        omega
      · have hw : W=X/H := max_eq_right (by omega)
        rw [hw]
        calc _ ≤ (2*H)*(X/H) := Nat.mul_le_mul_right _ ((min_le_right ..).trans
                                    (Nat.mul_le_mul_left 2 hkH))
             _ = 2*((X/H)*H) := by ring
             _ ≤ 2*N := Nat.mul_le_mul_left _ ((Nat.div_mul_le_self X H).trans hX)
    have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
    have hn₀ := zero_lt_one.trans_le hn
    have hK : (N:ℝ)^(1/5:ℝ)≤H :=
      hsmall.trans (by exact_mod_cast hUH)
    have hWpow : (W:ℝ)≤2*(N:ℝ)^(4/5:ℝ) := by
      have hp := Real.one_le_rpow hn (by norm_num : (0:ℝ)≤4/5)
      have hprod : (N:ℝ)^(4/5:ℝ)*(N:ℝ)^(1/5:ℝ)=(N:ℝ) := by
        rw [←Real.rpow_add hn₀]; norm_num
      have hnat : ((X/H:ℕ):ℝ)≤(X:ℝ)/(H:ℝ) := Nat.cast_div_le
      have hx : (X:ℝ)≤(N:ℝ)^(4/5:ℝ)*(H:ℝ) :=
        (Nat.cast_le.mpr hX).trans (hprod.symm.le.trans
          (mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg hn₀.le _)))
      change ((max 1 (X/H):ℕ):ℝ)≤_
      rw [Nat.cast_max,Nat.cast_one]
      exact max_le (by linarith only [hp]) (hnat.trans (((div_le_iff₀
        (Nat.cast_pos.mpr hH)).mpr hx).trans (by linarith only [hp])))
    have hmem {m : ℕ} (hm : m∈S i) : m∈Icc 1 M ∧ H≤m := by
      obtain ⟨hm,hh⟩ := mem_filter.mp hm
      obtain ⟨hl,hu⟩ := mem_Icc.mp hm
      have shell := chenShell_mem (show 2≤m by omega)
      rw [hh] at shell
      obtain ⟨hl',hu'⟩ := mem_Ioc.mp shell
      exact ⟨mem_Icc.mpr ⟨by omega,le_min hu hu'⟩,max_le hl (by omega)⟩
    have hrepr (q : ℕ) (χ : DirichletCharacter ℂ q) :
        P i q χ = ∑ m∈Icc 1 M, a' m*χ (m:ZMod q)*(∑ w∈Icc (lo m) (hi m),b w*χ (w:ZMod q)) := by
      calc P i q χ = ∑ m∈S i, a' m*χ (m:ZMod q)*(∑ w∈Icc (lo m) (hi m),b w*χ (w:ZMod q)) := by
                       apply Finset.sum_congr rfl
                       intro m hm
                       have hw : X/m≤W := (Nat.div_le_div_left (hmem hm).2 hH).trans (le_max_right ..)
                       simp [a',hi,hm,min_eq_right hw]
           _ = _ := Finset.sum_subset (fun m hm => (hmem hm).1) (fun m _ hm => by simp [a',hm])
    have hnorm : (∑ m∈Icc 1 M,‖a' m‖^2)≤(M:ℝ)*A^2 := by
      apply le_trans _ (ha _ hMN)
      refine Finset.sum_le_sum fun m _ => ?_
      unfold a'
      split <;> first | rfl | simp
    have hfun (q : ℕ) : P i q = (fun χ : DirichletCharacter ℂ q =>
        ∑ m∈Icc 1 M, a' m*χ (m:ZMod q)*(∑ w∈Icc (lo m) (hi m),b w*χ (w:ZMod q))) :=
      funext (hrepr q)
    simp_rw [hfun]
    exact vaughan_large_conductor_interval_bound M W D R N a' b lo hi hA hB hN hW hWN hD hR
      (by exact_mod_cast hMW) ((Nat.cast_le.mpr hM).trans hbig) hWpow hnorm (hb _ hWN)
      (fun m _ => hlo m) (fun _ _ => min_le_left ..)
  simp_rw [hsplit]
  calc _ ≤ ∑ q∈Ioc R D, (∑ i∈J,chenPrimitiveNorm q (P i q))/(q:ℝ) := by
             refine Finset.sum_le_sum fun q _ => div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
             exact chenNorm_sum q J (fun i => P i q)
       _ = ∑ i∈J,∑ q∈Ioc R D,chenPrimitiveNorm q (P i q)/(q:ℝ) := by simp_rw [Finset.sum_div]; rw [Finset.sum_comm]
       _ ≤ ∑ _i∈J,100000*L^2*(A*B)*G := Finset.sum_le_sum fun i _ => heach i
       _ = (J.card:ℝ)*(100000*L^2*(A*B)*G) := by simp
       _ ≤ (3*L)*(100000*L^2*(A*B)*G) := mul_le_mul_of_nonneg_right (chen_log2_range_card_le hN) (by positivity)
       _ = _ := by dsimp only [L,G]; ring

theorem vaughan_typeII_cutoff_geometry {N X : ℕ} (hN : 1≤N) (hX : X≤N) :
    let U := chenPowerLevel (1/5) N
    1≤U ∧ (N:ℝ)^(1/5:ℝ)≤(U:ℝ)+1 ∧ U^2≤N ∧
    ((U^2:ℕ):ℝ)≤2*(N:ℝ)^(4/5:ℝ) ∧ ((X/(U+1):ℕ):ℝ)≤2*(N:ℝ)^(4/5:ℝ) := by
  let U := chenPowerLevel (1/5) N
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hn₀ := zero_lt_one.trans_le hn
  have hup : (U:ℝ)≤(N:ℝ)^(1/5:ℝ) := Nat.floor_le (Real.rpow_nonneg hn₀.le _)
  have hlow : (N:ℝ)^(1/5:ℝ)≤(U:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have h1 : 1≤U := (Nat.le_floor_iff (Real.rpow_nonneg hn₀.le _)).mpr (by
    simpa only [Nat.cast_one] using Real.one_le_rpow hn (by norm_num : (0:ℝ)≤1/5))
  have hu2 : ((U^2:ℕ):ℝ)≤(N:ℝ)^(2/5:ℝ) := by
    rw [Nat.cast_pow,sq, show (N:ℝ)^(2/5:ℝ)=(N:ℝ)^(1/5:ℝ)*(N:ℝ)^(1/5:ℝ) by
      rw [←Real.rpow_add hn₀]; norm_num]
    exact mul_le_mul hup hup (Nat.cast_nonneg _) (by positivity)
  have hbig := Real.rpow_nonneg hn₀.le (4/5:ℝ)
  have hpow : (N:ℝ)^(4/5:ℝ)*(N:ℝ)^(1/5:ℝ)=(N:ℝ) := by rw [←Real.rpow_add hn₀]; norm_num
  refine ⟨h1,hlow,Nat.cast_le (α:=ℝ).mp ((hu2.trans (Real.rpow_le_rpow_of_exponent_le hn
    (by norm_num : (2/5:ℝ)≤1))).trans_eq (Real.rpow_one _)),(hu2.trans
    (Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (2/5:ℝ)≤4/5))).trans (by linarith),?_⟩
  have hfloor : ((X/(U+1):ℕ):ℝ)≤(X:ℝ)/((U+1:ℕ):ℝ) := Nat.cast_div_le
  apply hfloor.trans
  rw [Nat.cast_add_one]
  apply le_trans ((div_le_iff₀ (by positivity : 0<(U:ℝ)+1)).mpr
    ((Nat.cast_le.mpr hX).trans (hpow.symm.le.trans (mul_le_mul_of_nonneg_left hlow hbig))))
  linarith

end FareyGoldbach
