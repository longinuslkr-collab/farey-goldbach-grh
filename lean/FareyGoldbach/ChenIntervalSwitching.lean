import FareyGoldbach.ChenLargeConductor
import FareyGoldbach.ChenSmallConductorInterval
import FareyGoldbach.ChenSwitchingAssembly
import FareyGoldbach.ChenSwitchingAsymptotics
import FareyGoldbach.ChenSwitchingBudgets

/-! # Unconditional distribution of reflected products with a final prime in an interval -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

/-- An active first factor is completed by a prime in its own interval. -/
noncomputable def chenIntervalSwitchPairs (N : ℕ) (active : ℕ → Prop) (lo : ℕ → ℕ) :
    Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun p ↦
    active p.1 ∧ p.2.Prime ∧ lo p.1 ≤ p.2 ∧ p.1 * p.2 < N

theorem mem_chenIntervalSwitchPairs {N m w : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ} :
    (m,w) ∈ chenIntervalSwitchPairs N active lo ↔
      0 < m ∧ active m ∧ w.Prime ∧ lo m ≤ w ∧ m*w < N := by
  constructor
  · intro h
    obtain ⟨hr, ha, hp, hl, hh⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_product.mp hr).1).1, ha, hp, hl, hh⟩
  · rintro ⟨hm, ha, hp, hl, hh⟩
    have hmN := (Nat.le_mul_of_pos_right m hp.pos).trans hh.le
    have hwN := (Nat.le_mul_of_pos_left w hm).trans hh.le
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hm, hmN⟩,
      Finset.mem_Icc.mpr ⟨hp.pos, hwN⟩⟩, ha, hp, hl, hh⟩

/-- Reflection of the product sequence about `N`. -/
noncomputable def chenIntervalSwitchCarrier (N : ℕ) (active : ℕ → Prop) (lo : ℕ → ℕ) : Finset ℕ :=
  (chenIntervalSwitchPairs N active lo).image (fun x ↦ N - x.1*x.2)

private theorem interval_reflect_injOn {N : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    (hinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1*p.2) (chenIntervalSwitchPairs N active lo)) :
    Set.InjOn (fun p : ℕ × ℕ ↦ N - p.1*p.2) (chenIntervalSwitchPairs N active lo) := by
  rintro ⟨m,w⟩ hx ⟨s,t⟩ hy he
  have hx' := (mem_chenIntervalSwitchPairs.mp hx).2.2.2.2
  have hy' := (mem_chenIntervalSwitchPairs.mp hy).2.2.2.2
  apply hinj hx hy
  change N - m*w = N - s*t at he
  change m*w = s*t
  omega

private theorem interval_reflect_card {N : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    (hinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1*p.2) (chenIntervalSwitchPairs N active lo)) :
    (chenIntervalSwitchCarrier N active lo).card = (chenIntervalSwitchPairs N active lo).card :=
  card_image_of_injOn (interval_reflect_injOn hinj)

private theorem interval_reflect_progression {N d : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    (hinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1*p.2) (chenIntervalSwitchPairs N active lo)) :
    (chenDivisible (chenIntervalSwitchCarrier N active lo) d).card =
      ((chenIntervalSwitchPairs N active lo).filter (fun x ↦ (x.1*x.2)%d = N%d)).card := by
  let F := (chenIntervalSwitchPairs N active lo).filter (fun x ↦ (x.1*x.2)%d = N%d)
  have hF : chenDivisible (chenIntervalSwitchCarrier N active lo) d =
      F.image (fun p ↦ N-p.1*p.2) := by
    ext b
    rw [chenDivisible, chenIntervalSwitchCarrier]
    simp only [F, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨⟨m,w⟩, hp, rfl⟩, hd⟩
      exact ⟨(m,w), ⟨hp, (Nat.modEq_iff_dvd' (mem_chenIntervalSwitchPairs.mp hp).2.2.2.2.le).mpr hd⟩, rfl⟩
    · rintro ⟨⟨m,w⟩, ⟨hp, hd⟩, rfl⟩
      exact ⟨⟨(m,w), hp, rfl⟩, (Nat.modEq_iff_dvd' (mem_chenIntervalSwitchPairs.mp hp).2.2.2.2.le).mp hd⟩
  rw [hF]
  exact card_image_of_injOn (fun _ h₁ _ h₂ h ↦
    interval_reflect_injOn hinj (mem_filter.mp h₁).1 (mem_filter.mp h₂).1 h)

private noncomputable def intervalBoxPairs (N : ℕ) (active : ℕ → Prop) (lo : ℕ → ℕ) (i : ℕ) :
    Finset (ℕ × ℕ) :=
  (chenIntervalSwitchPairs N active lo).filter (fun p ↦ chenShellIndex p.1 = i)

private def intervalBoxLo (lo : ℕ → ℕ) (m : ℕ) : ℕ := max 1 (lo m)

private noncomputable def intervalBoxA (active : ℕ → Prop) (i k m : ℕ) : ℂ :=
  if 2^i < m ∧ active m ∧ m.Coprime k then 1 else 0

private theorem intervalBoxA_norm_le (active : ℕ → Prop) (i k m : ℕ) :
    ‖intervalBoxA active i k m‖ ≤ 1 := by
  unfold intervalBoxA
  split_ifs <;> simp

private theorem mem_intervalBoxPairs {N i m w : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    (hactive : ∀ m, active m → 2 ≤ m) :
    (m,w) ∈ intervalBoxPairs N active lo i ↔
      m ∈ Finset.Icc 1 (chenSwitchBoxM i) ∧ (2^i < m ∧ active m) ∧
      w ∈ Finset.Icc (intervalBoxLo lo m) (chenSwitchBoxHi N i m) ∧ w.Prime := by
  have hpow : 0 < (2:ℕ)^i := by positivity
  constructor
  · intro h
    obtain ⟨hp, hi⟩ := Finset.mem_filter.mp h
    obtain ⟨hm, ha, hw, hlo, hN⟩ := mem_chenIntervalSwitchPairs.mp hp
    have hs := chenShell_mem (hactive _ ha)
    change chenShellIndex m = i at hi
    rw [hi] at hs
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hs
    have hW : w ≤ chenSwitchBoxW N i := by
      change w ≤ N/(2^i)
      apply (Nat.le_div_iff_mul_le hpow).mpr
      rw [Nat.mul_comm]
      exact (Nat.mul_le_mul_right _ hl.le).trans hN.le
    have hcap : w ≤ (N-1)/m := by
      apply (Nat.le_div_iff_mul_le hm).mpr
      rw [Nat.mul_comm]
      omega
    exact ⟨Finset.mem_Icc.mpr ⟨hm,hu⟩, ⟨hl,ha⟩,
      Finset.mem_Icc.mpr ⟨max_le hw.pos hlo, le_min hW hcap⟩, hw⟩
  · rintro ⟨hm, ⟨hl,ha⟩, hw, hwp⟩
    have hm' := (Finset.mem_Icc.mp hm).1
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hw
    have hcap : w ≤ (N-1)/m := hhi.trans (min_le_right ..)
    have hmul := (Nat.le_div_iff_mul_le hm').mp hcap
    rw [Nat.mul_comm] at hmul
    have hp : 0 < m*w := Nat.mul_pos hm' hwp.pos
    have hmw : m*w < N := by omega
    refine Finset.mem_filter.mpr ⟨mem_chenIntervalSwitchPairs.mpr
      ⟨hm',ha,hwp,(le_max_right _ _).trans hlo,hmw⟩,?_⟩
    exact chenShellIndex_eq_of_mem (Finset.mem_Ioc.mpr ⟨hl,(Finset.mem_Icc.mp hm).2⟩)

private noncomputable def intervalBoxSum {q : ℕ} (N : ℕ) (active : ℕ → Prop) (lo : ℕ → ℕ)
    (i k : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (chenSwitchBoxM i), intervalBoxA active i k m*χ (m:ZMod q)*
    (∑ w ∈ Finset.Icc (intervalBoxLo lo m) (chenSwitchBoxHi N i m),
      chenSwitchBoxB k w*χ (w:ZMod q))

private theorem intervalBoxSum_eq {q N i k : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    (hactive : ∀ m, active m → 2 ≤ m) (χ : DirichletCharacter ℂ q) :
    intervalBoxSum N active lo i k χ = ∑ p ∈ intervalBoxPairs N active lo i,
      chenMaskedChar χ k p.1 * chenMaskedChar χ k p.2 := by
  let A := Finset.Icc 1 (chenSwitchBoxM i)
  let W := Finset.Icc 1 (chenSwitchBoxW N i)
  have heq : intervalBoxPairs N active lo i =
      (A ×ˢ W).filter (fun p ↦ (2^i < p.1 ∧ active p.1) ∧
        p.2 ∈ Finset.Icc (intervalBoxLo lo p.1) (chenSwitchBoxHi N i p.1) ∧ p.2.Prime) := by
    ext p
    rcases p with ⟨m,w⟩
    rw [mem_intervalBoxPairs hactive, Finset.mem_filter, Finset.mem_product]
    dsimp
    constructor
    · rintro ⟨hm,ha,hw,hp⟩
      exact ⟨⟨hm,Finset.mem_Icc.mpr
        ⟨(le_max_left 1 (lo m)).trans (Finset.mem_Icc.mp hw).1,
          (Finset.mem_Icc.mp hw).2.trans (chenSwitchBoxHi_le ..)⟩⟩,ha,hw,hp⟩
    · rintro ⟨⟨hm,_⟩,ha,hw,hp⟩
      exact ⟨hm,ha,hw,hp⟩
  unfold intervalBoxSum
  rw [heq,Finset.sum_filter,Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  let T := Finset.Icc (intervalBoxLo lo m) (chenSwitchBoxHi N i m)
  have hT : T ⊆ W := fun w hw ↦ Finset.mem_Icc.mpr
    ⟨(le_max_left 1 (lo m)).trans (Finset.mem_Icc.mp hw).1,
      (Finset.mem_Icc.mp hw).2.trans (chenSwitchBoxHi_le ..)⟩
  rw [Finset.mul_sum, ←Finset.sum_subset hT (fun w _ hw ↦ by
    simp only [show w ∉ Finset.Icc (intervalBoxLo lo m) (chenSwitchBoxHi N i m) from hw,
      false_and, and_false, ite_false])]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  change w ∈ T at hw
  by_cases hi : 2^i < m <;> by_cases ha : active m <;> by_cases hm : m.Coprime k <;>
    by_cases hp : w.Prime <;> by_cases hk : w.Coprime k <;>
    simp [intervalBoxA,chenSwitchBoxB,chenMaskedChar,hi,ha,hm,hp,hk,
      show w ∈ Finset.Icc (intervalBoxLo lo m) (chenSwitchBoxHi N i m) from hw]

private theorem interval_masked_sum_eq_boxes {q N k : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    (hactive : ∀ m, active m → 2 ≤ m) (χ : DirichletCharacter ℂ q) :
    (∑ p ∈ chenIntervalSwitchPairs N active lo, chenMaskedChar χ k p.1 * chenMaskedChar χ k p.2) =
      ∑ i ∈ Finset.range (N.log2+1), intervalBoxSum N active lo i k χ := by
  simp_rw [intervalBoxSum_eq hactive, intervalBoxPairs]
  apply (Finset.sum_fiberwise_of_maps_to ?_ _).symm
  rintro ⟨m,w⟩ hp
  obtain ⟨_,ha,hw,_,hN⟩ := mem_chenIntervalSwitchPairs.mp hp
  exact chenShellIndex_mem_range (hactive _ ha) ((Nat.le_mul_of_pos_right m hw.pos).trans hN.le)

private theorem intervalBox_ranges {N i : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    (hN : 1 ≤ N) (hactive : ∀ m, active m → 2 ≤ m)
    (houter : ∀ m, active m → (N:ℝ)^(1/4:ℝ) ≤ m)
    (hinner : ∀ m, active m → (N:ℝ)^(1/4:ℝ)+1 ≤ (lo m:ℝ))
    (hne : (intervalBoxPairs N active lo i).Nonempty) :
    1 ≤ chenSwitchBoxW N i ∧ chenSwitchBoxW N i ≤ N ∧
      (chenSwitchBoxM i:ℝ)*(chenSwitchBoxW N i:ℝ) ≤ 2*(N:ℝ) ∧
      (chenSwitchBoxM i:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ) ∧
      (chenSwitchBoxW N i:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ) := by
  obtain ⟨⟨m,w⟩, hp⟩ := hne
  obtain ⟨hm, ⟨hl,ha⟩, hw, hwP⟩ := (mem_intervalBoxPairs hactive).mp hp
  obtain ⟨_, _, _, hlo, hprod⟩ := mem_chenIntervalSwitchPairs.mp (Finset.mem_filter.mp hp).1
  have hW₁ : 1 ≤ chenSwitchBoxW N i :=
    hwP.pos.trans_le ((Finset.mem_Icc.mp hw).2.trans (chenSwitchBoxHi_le ..))
  have hW₂ : chenSwitchBoxW N i ≤ N := Nat.div_le_self ..
  let Q : ℕ := 2^i
  have hprodQ : Q*chenSwitchBoxW N i ≤ N := by
    dsimp [Q,chenSwitchBoxW]
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self ..
  have hMW : (chenSwitchBoxM i:ℝ)*(chenSwitchBoxW N i:ℝ) ≤ 2*(N:ℝ) := by
    unfold chenSwitchBoxM
    exact_mod_cast (show (2*2^i)*chenSwitchBoxW N i ≤ 2*N by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hprodQ)
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hpwr : (N:ℝ)^(1/4:ℝ)*(N:ℝ)^(3/4:ℝ) = (N:ℝ) := by
    rw [←Real.rpow_add hn, show (1/4:ℝ)+3/4=1 by norm_num, Real.rpow_one]
  have hyw : (N:ℝ)^(1/4:ℝ) ≤ w := by
    linarith only [hinner _ ha, Nat.cast_le (α:=ℝ).mpr hlo]
  have hmPow : (m:ℝ) ≤ (N:ℝ)^(3/4:ℝ) := by
    apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hn (1/4:ℝ))).mp
    rw [hpwr]
    exact (mul_le_mul_of_nonneg_right hyw (Nat.cast_nonneg _)).trans
      (by exact_mod_cast (show w*m ≤ N by rw [Nat.mul_comm]; exact hprod.le))
  have hMpow : (chenSwitchBoxM i:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ) := by
    have hQ : (Q:ℝ) ≤ (m:ℝ) := Nat.cast_le.mpr hl.le
    change ((2*Q:ℕ):ℝ) ≤ _
    rw [Nat.cast_mul,Nat.cast_ofNat]
    linarith only [hQ,hmPow]
  have hWpow : (chenSwitchBoxW N i:ℝ) ≤ 2*(N:ℝ)^(3/4:ℝ) := by
    apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hn (1/4:ℝ))).mp
    rw [←mul_assoc,mul_comm ((N:ℝ)^(1/4:ℝ)) 2,mul_assoc,hpwr]
    apply le_trans (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)) hMW
    exact (houter _ ha).trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2)
  exact ⟨hW₁,hW₂,hMW,hMpow,hWpow⟩

private theorem interval_masked_mass_le_boxes {q N k : ℕ} [NeZero q] {active : ℕ → Prop} {lo : ℕ → ℕ}
    (hactive : ∀ m, active m → 2 ≤ m) :
    chenMaskedPrimitiveMass (chenIntervalSwitchPairs N active lo) q k/(q.totient:ℝ) ≤
      ∑ i ∈ Finset.range (N.log2+1), chenPrimitiveNorm q (intervalBoxSum N active lo i k)/(q:ℝ) := by
  let S := (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive)
  rw [chenMaskedPrimitiveMass_of_pos]
  simp_rw [interval_masked_sum_eq_boxes hactive]
  calc _ ≤ (∑ χ ∈ S, ∑ i ∈ Finset.range (N.log2+1), ‖intervalBoxSum N active lo i k χ‖)/(q.totient:ℝ) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum fun χ _ ↦ norm_sum_le _ _
    _ = _ := by
      rw [Finset.sum_comm (s:=S)]
      simp only [Finset.sum_div,chenPrimitiveNorm_div_eq_avg,S]

private theorem intervalSwitch_error_le_of_boxes {N z D : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    {B : ℝ} (hN : 1≤N) (hz : 0<z) (hD : D≤N) (hB : 0≤B)
    (hactive : ∀ m, active m → 2≤m)
    (hinj : Set.InjOn (fun x : ℕ×ℕ ↦ x.1*x.2) (chenIntervalSwitchPairs N active lo))
    (hrough : ∀ x ∈ chenIntervalSwitchPairs N active lo, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → z≤p)
    (hboxes : ∀ k ∈ Finset.Ico 1 D, ∀ i ∈ Finset.range (N.log2+1),
      (∑ q ∈ Finset.Ico 2 D, chenPrimitiveNorm q (intervalBoxSum N active lo i k)/(q:ℝ))≤B) :
    chenReducedError N D (chenAPError (chenIntervalSwitchCarrier N active lo)
      (chenIntervalSwitchCarrier N active lo).card) ≤
      4*(chenSwitchLog N)^3*((N:ℝ)/(z:ℝ)) + 6*(chenSwitchLog N)^3*B := by
  let P := chenIntervalSwitchPairs N active lo
  let L := chenSwitchLog N
  let R := Finset.Ico 1 D
  have hprod (x : ℕ×ℕ) (hx : x∈P) : 0<x.1*x.2 ∧ x.1*x.2≤N := by
    obtain ⟨hm,_,hw,_,hn⟩ := mem_chenIntervalSwitchPairs.mp hx
    exact ⟨Nat.mul_pos hm hw.pos, hn.le⟩
  have hpc := chenPair_principal_correction P hN hz hD hinj hprod hrough
  have hsum (k : ℕ) (hk : k∈R) :
      ∑ q ∈ Finset.Ico 2 D, chenMaskedPrimitiveMass P q k/(q.totient:ℝ)≤3*L*B := by
    calc _ ≤ ∑ q ∈ Finset.Ico 2 D, ∑ i ∈ Finset.range (N.log2+1),
            chenPrimitiveNorm q (intervalBoxSum N active lo i k)/(q:ℝ) := by
            apply Finset.sum_le_sum
            intro q hq
            let _ : NeZero q := ⟨by have := (Finset.mem_Ico.mp hq).1; omega⟩
            exact interval_masked_mass_le_boxes hactive
      _ ≤ ∑ _i ∈ Finset.range (N.log2+1), B := by
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum (fun i hi ↦ hboxes k hk i hi)
      _ ≤ _ := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right (chen_log2_range_card_le hN) hB
  have hR : R ⊆ Finset.Icc 1 N := fun k hk ↦
    Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1,(Finset.mem_Ico.mp hk).2.le.trans hD⟩
  have hL : 0≤L := zero_le_one.trans (one_le_chenSwitchLog hN)
  have htot :
      ∑ k ∈ R, (1/(k.totient:ℝ))*(∑ q ∈ Finset.Ico 2 D,chenMaskedPrimitiveMass P q k/(q.totient:ℝ)) ≤
        6*L^3*B := by
    calc _ ≤ ∑ k ∈ R,(1/(k.totient:ℝ))*(3*L*B) :=
          Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_left (hsum k hk) (by positivity)
      _ = (∑ k ∈ R, 1/(k.totient:ℝ))*(3*L*B) := by rw [Finset.sum_mul]
      _ ≤ (2*L^2)*(3*L*B) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (Finset.sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ ↦ by positivity)).trans
          (chen_sum_inv_totient_le hN)
      _ = _ := by ring
  apply le_trans _ (add_le_add hpc htot)
  simpa only [chenReducedError, chenAPError, P, interval_reflect_progression hinj,
    interval_reflect_card hinj] using chenPairAP_sum_le P N D

private theorem intervalSwitch_sum_conductors_split (E : ℕ→ℝ) (hE : ∀ q,0≤E q) (D R : ℕ) :
    (∑ q ∈ Finset.Ico 2 D,E q)≤
      (∑ q ∈ Finset.Icc 2 R,E q)+(∑ q ∈ Finset.Ioc R D,E q) := by
  rw [←Finset.sum_filter_add_sum_filter_not (Finset.Ico 2 D) (·≤R)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun q _ _ ↦ hE q)
    intro q hq
    obtain ⟨hD,hR⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hD).1,hR⟩
  · apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun q _ _ ↦ hE q)
    intro q hq
    obtain ⟨hD,hR⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hR,(Finset.mem_Ico.mp hD).2.le⟩

private theorem intervalBox_low_bound {N i k R : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    {B : ℝ} (hB : 0≤B)
    (h : ∀ q : ℕ, ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2≤q → q≤R → ‖intervalBoxSum N active lo i k χ‖≤B) :
    (∑ q ∈ Finset.Icc 2 R,chenPrimitiveNorm q (intervalBoxSum N active lo i k)/(q:ℝ))≤(R:ℝ)*B := by
  calc _ ≤ ∑ _q ∈ Finset.Icc 2 R,B := by
          apply Finset.sum_le_sum
          intro q hq
          obtain ⟨hq₂,hqR⟩ := Finset.mem_Icc.mp hq
          let _ : NeZero q := ⟨by omega⟩
          exact chenPrimitiveNorm_div_le_of_bound _ hB (fun χ hχ ↦ h q χ hχ hq₂ hqR)
    _ ≤ _ := by
      rw [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hB
      rw [Nat.card_Icc]
      exact_mod_cast (show R+1-2≤R by omega)

private theorem intervalBox_sum_le_of_local {N i k D R : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ}
    {C : ℝ} (hN : 1≤N) (hD : D≤N) (hR : 1≤R) (hC : 0≤C)
    (hactive : ∀ m, active m → 2≤m)
    (houter : ∀ m, active m → (N:ℝ)^(1/4:ℝ) ≤ m)
    (hinner : ∀ m, active m → (N:ℝ)^(1/4:ℝ)+1 ≤ (lo m:ℝ))
    (hsmall : ∀ q : ℕ, ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2≤q → q≤R →
      ‖intervalBoxSum N active lo i k χ‖≤
        C*((N:ℝ)/(chenSwitchLog N)^30+(N:ℝ)^(3/4:ℝ)*chenSwitchLog N)) :
    (∑ q ∈ Finset.Ico 2 D,chenPrimitiveNorm q (intervalBoxSum N active lo i k)/(q:ℝ))≤
      (R:ℝ)*(C*((N:ℝ)/(chenSwitchLog N)^30+(N:ℝ)^(3/4:ℝ)*chenSwitchLog N)) +
      100000*(chenSwitchLog N)^2*((N:ℝ)/R+(N:ℝ)^(7/8:ℝ)+(D:ℝ)*Real.sqrt N) := by
  let E (q : ℕ) := chenPrimitiveNorm q (intervalBoxSum N active lo i k)/(q:ℝ)
  have hE (q : ℕ) : 0≤E q := div_nonneg (chenPrimitiveNorm_nonneg ..) (Nat.cast_nonneg _)
  have hL : 0≤chenSwitchLog N := zero_le_one.trans (one_le_chenSwitchLog hN)
  by_cases hne : (intervalBoxPairs N active lo i).Nonempty
  · apply (intervalSwitch_sum_conductors_split E hE D R).trans
    apply add_le_add
    · exact intervalBox_low_bound (by positivity) hsmall
    · obtain ⟨hW,hWN,hMW,hM,hWpow⟩ := intervalBox_ranges hN hactive houter hinner hne
      exact chen_large_conductor_interval_bound (chenSwitchBoxM i) (chenSwitchBoxW N i) D R N
        (intervalBoxA active i k) (chenSwitchBoxB k) (intervalBoxLo lo) (chenSwitchBoxHi N i)
        hN hW hWN hD hR hMW hM hWpow
        (fun m _ ↦ intervalBoxA_norm_le active i k m) (fun w _ ↦ chenSwitchBoxB_norm_le k w)
        (fun m _ ↦ le_max_left 1 (lo m)) (fun m _ ↦ chenSwitchBoxHi_le N i m)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    have heq (q : ℕ) : E q=0 := by
      unfold E chenPrimitiveNorm
      split_ifs <;> simp [intervalBoxSum_eq hactive,he]
    change (∑ q ∈ Finset.Ico 2 D,E q)≤_
    simp_rw [heq]
    rw [Finset.sum_const_zero]
    positivity

private theorem intervalSwitch_conductor_cutoff_bounds {N : ℕ} (hN : 1≤N) :
    let L := chenSwitchLog N
    let R := ⌈L^12⌉₊
    1≤R ∧ L^12 ≤ (R:ℝ) ∧ (R:ℝ)≤2*L^12 := by
  let L := chenSwitchLog N
  let R := ⌈L^12⌉₊
  have hL := one_le_chenSwitchLog hN
  have h₁ : (1:ℝ)≤L^12 := one_le_pow₀ hL
  have h₂ : L^12≤(R:ℝ) := Nat.le_ceil _
  have h₃ : (R:ℝ)<L^12+1 := Nat.ceil_lt_add_one (by positivity)
  exact ⟨by exact_mod_cast h₁.trans h₂,h₂,by linarith only [h₁,h₃]⟩

private theorem intervalSwitch_finite_majorant {θ C : ℝ} (hθ : 0<θ) (hhalf : θ<1/2)
    (hC : 0≤C) {N z : ℕ} {active : ℕ → Prop} {lo : ℕ → ℕ} (hN : 1≤N)
    (hz : (N:ℝ)^(1/16:ℝ)≤(z:ℝ))
    (hactive : ∀ m, active m → 2≤m)
    (houter : ∀ m, active m → (N:ℝ)^(1/4:ℝ) ≤ m)
    (hinner : ∀ m, active m → (N:ℝ)^(1/4:ℝ)+1 ≤ (lo m:ℝ))
    (hinj : Set.InjOn (fun x : ℕ×ℕ ↦ x.1*x.2) (chenIntervalSwitchPairs N active lo))
    (hrough : ∀ x ∈ chenIntervalSwitchPairs N active lo, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → z≤p)
    (hsmall : ∀ k i q : ℕ, ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      k∈Finset.Ico 1 (chenPowerLevel θ N) → χ.IsPrimitive →
      2≤q → q≤⌈(chenSwitchLog N)^12⌉₊ →
      ‖intervalBoxSum N active lo i k χ‖≤
        C*((N:ℝ)/(chenSwitchLog N)^30+(N:ℝ)^(3/4:ℝ)*chenSwitchLog N)) :
    chenReducedError N (chenPowerLevel θ N) (chenAPError (chenIntervalSwitchCarrier N active lo)
      (chenIntervalSwitchCarrier N active lo).card) ≤
      (4+6*(2*C+200000))*((N:ℝ)/(chenSwitchLog N)^4 +
        (N:ℝ)^max (15/16:ℝ) (θ+1/2)*(chenSwitchLog N)^20) := by
  let L := chenSwitchLog N
  let R := ⌈L^12⌉₊
  let D := chenPowerLevel θ N
  let β := max (15/16:ℝ) (θ+1/2)
  let H := (N:ℝ)^β
  let B := (2*C+200000)*((N:ℝ)/L^7+H*L^16)
  have hn : (1:ℝ)≤N := Nat.one_le_cast.mpr hN
  have hp : (0:ℝ)<N := zero_lt_one.trans_le hn
  have hL : 1≤L := one_le_chenSwitchLog hN
  have hH : 0≤H := by dsimp only [H]; positivity
  obtain ⟨hR,hR₁,hR₂⟩ := intervalSwitch_conductor_cutoff_bounds hN
  have hRpos : (0:ℝ)<R := Nat.cast_pos.mpr hR
  have hD : D≤N := chenPowerLevel_le_self (by linarith only [hhalf]) hN
  have hzpos : 0<z := Nat.cast_pos.mp ((Real.rpow_pos_of_pos hp _).trans_le hz)
  have hβ₁ : (15/16:ℝ)≤β := le_max_left ..
  have hM : (N:ℝ)^(3/4:ℝ)≤H := Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hβ₁])
  have hW : (N:ℝ)^(7/8:ℝ)≤H := Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hβ₁])
  have hDpow : (D:ℝ)*Real.sqrt N≤H := by
    rw [Real.sqrt_eq_rpow]
    calc _ ≤ (N:ℝ)^θ*(N:ℝ)^(1/2:ℝ) := mul_le_mul_of_nonneg_right
          (Nat.floor_le (zero_le_one.trans (Real.one_le_rpow hn hθ.le))) (by positivity)
      _ = (N:ℝ)^(θ+1/2) := by rw [Real.rpow_add hp]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (le_max_right ..)
  have hZpow : (N:ℝ)/(z:ℝ)≤H := by
    calc _ ≤ (N:ℝ)/(N:ℝ)^(1/16:ℝ) :=
          div_le_div_of_nonneg_left hp.le (by positivity) hz
      _ = (N:ℝ)^(15/16:ℝ) := by
        rw [show (15/16:ℝ)=1-1/16 by norm_num,Real.rpow_sub hp,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn hβ₁
  have hB : 0≤B := by dsimp only [B]; positivity
  have hb (k : ℕ) (hk : k∈Finset.Ico 1 D) (i : ℕ) (_hi : i∈Finset.range (N.log2+1)) :
      (∑ q∈Finset.Ico 2 D,chenPrimitiveNorm q
          (intervalBoxSum N active lo i k)/(q:ℝ))≤B := by
    apply (intervalBox_sum_le_of_local hN hD hR hC hactive houter hinner
      (fun q _ χ hχ hq hqR ↦ hsmall k i q χ hk hχ hq hqR)).trans
    have hlow : (N:ℝ)/L^30+(N:ℝ)^(3/4:ℝ)*L ≤ (N:ℝ)/L^30+H*L :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hM (zero_le_one.trans hL))
    have hhigh : (N:ℝ)/R+(N:ℝ)^(7/8:ℝ)+(D:ℝ)*Real.sqrt N ≤
        (N:ℝ)/R+H+H := add_le_add (add_le_add (le_refl _) hW) hDpow
    calc _ ≤ (R:ℝ)*(C*((N:ℝ)/L^30+H*L))+
              100000*L^2*((N:ℝ)/R+H+H) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hlow hC) (Nat.cast_nonneg _))
              (mul_le_mul_of_nonneg_left hhigh (by positivity))
      _ ≤ B := chenSwitchBox_budget_absorb hL hp.le hH hRpos hC hR₁ hR₂
  apply (intervalSwitch_error_le_of_boxes hN hzpos hD hB hactive hinj hrough hb).trans
  apply le_trans (add_le_add (mul_le_mul_of_nonneg_left hZpow (by positivity)) (le_refl _))
  exact chenSwitchTotal_budget_absorb hL hp.le hH hC

/-- Distribution to every fixed power below one half, uniform in the active prefix set and
lower endpoint of the final prime. The two factors of each product are at least a quarter power. -/
theorem chen_intervalSwitch_reduced_error_of_smallConductor
    (hSmall : SmallConductorPrimeTwists) {θ : ℝ} (hθ : 0<θ) (hhalf : θ<1/2)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (z : ℕ) (active : ℕ → Prop) (lo : ℕ → ℕ),
      (N:ℝ)^(1/16:ℝ) ≤ (z:ℝ) →
      (∀ m, active m → 2≤m) →
      (∀ m, active m → (N:ℝ)^(1/4:ℝ) ≤ m) →
      (∀ m, active m → (N:ℝ)^(1/4:ℝ)+1 ≤ (lo m:ℝ)) →
      Set.InjOn (fun x : ℕ×ℕ ↦ x.1*x.2) (chenIntervalSwitchPairs N active lo) →
      (∀ x ∈ chenIntervalSwitchPairs N active lo, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → z≤p) →
      chenReducedError N (chenPowerLevel θ N) (chenAPError (chenIntervalSwitchCarrier N active lo)
        (chenIntervalSwitchCarrier N active lo).card) ≤ ε*chenLogScale N := by
  obtain ⟨C,hC,hCevt⟩ := chen_small_conductor_interval_bound hSmall
  have hβ : max (15/16:ℝ) (θ+1/2)<1 := max_lt (by norm_num) (by linarith only [hhalf])
  have hBudget := chenSwitching_budget_small hβ (show (0:ℝ)≤4+6*(2*C+200000) by positivity) hε
  filter_upwards [hBudget,hCevt,eventually_ge_atTop (1:ℕ)] with N hBudget hsmall hN
  intro z active lo hz hactive houter hinner hinj hrough
  apply (intervalSwitch_finite_majorant hθ hhalf hC.le hN hz hactive houter hinner hinj hrough ?_).trans hBudget
  intro k i q _ χ hk hχ hq hqR
  have hk₁ := (Finset.mem_Ico.mp hk).1
  have hkN := (Finset.mem_Ico.mp hk).2.le.trans
    (chenPowerLevel_le_self (by linarith only [hhalf]) hN)
  by_cases hne : (intervalBoxPairs N active lo i).Nonempty
  · obtain ⟨_,_,hMW,hM,_⟩ := intervalBox_ranges hN hactive houter hinner hne
    have hlo (m : ℕ) (_hm : m∈Finset.Icc 1 (chenSwitchBoxM i))
        (hm₀ : intervalBoxA active i k m≠0) :
        (N:ℝ)^(1/4:ℝ)+1≤(intervalBoxLo lo m:ℝ) := by
      have he : 2^i < m ∧ active m ∧ m.Coprime k := by
        by_contra hn
        exact hm₀ (ite_eq_right hn)
      exact (hinner _ he.2.1).trans (Nat.cast_le.mpr (le_max_right 1 (lo m)))
    exact hsmall (chenSwitchBoxM i) (chenSwitchBoxW N i) k q χ
      (intervalBoxA active i k) (intervalBoxLo lo) (chenSwitchBoxHi N i)
      hχ hq hqR hk₁ hkN hMW hM (fun m _ ↦ intervalBoxA_norm_le active i k m) hlo
      (fun m _ ↦ chenSwitchBoxHi_le N i m)
  · simp [intervalBoxSum_eq hactive, Finset.not_nonempty_iff_eq_empty.mp hne]
    have hL : 0≤chenSwitchLog N := zero_le_one.trans (one_le_chenSwitchLog hN)
    positivity

end FareyGoldbach
