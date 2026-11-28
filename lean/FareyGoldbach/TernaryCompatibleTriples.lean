import FareyGoldbach.ShortFixedPairGoldbach

/-! # Compatible reduced residue triples for the ternary Goldbach problem -/

open Finset
open scoped Classical BigOperators

namespace FareyGoldbach

/-- The three residues are ordered; repeated residues are allowed. -/
noncomputable def ternaryCompatibleTriples (r n : ℕ) :
    Finset (ReducedClass r × ReducedClass r × ReducedClass r) :=
  ((coprimeClasses r).attach ×ˢ ((coprimeClasses r).attach ×ˢ (coprimeClasses r).attach)).filter
    fun t => n % r = (t.1.val + t.2.1.val + t.2.2.val) % r

private abbrev pairResidues (r : ℕ) (s : ℤ) :=
  {x : ZMod r // IsUnit x ∧ IsUnit ((s : ZMod r) - x)}

private noncomputable def pairCRT {a b : ℕ} (hab : a.Coprime b) (s : ℤ) :
    pairResidues (a*b) s ≃ pairResidues a s × pairResidues b s := by
  let e := ZMod.chineseRemainder hab
  have hp (x : ZMod (a*b)) : IsUnit x ∧ IsUnit ((s : ZMod (a*b))-x) ↔
      (IsUnit (e x).1 ∧ IsUnit ((s : ZMod a)-(e x).1)) ∧
      (IsUnit (e x).2 ∧ IsUnit ((s : ZMod b)-(e x).2)) := by
    rw [← MulEquiv.isUnit_map e (x:=x), ← MulEquiv.isUnit_map e (x:=((s : ZMod (a*b))-x))]
    rw [map_sub, map_intCast, Prod.isUnit_iff,Prod.isUnit_iff]
    tauto
  refine { toFun := fun x => (⟨(e x.val).1,((hp _).mp x.property).1⟩,
                              ⟨(e x.val).2,((hp _).mp x.property).2⟩)
           invFun := fun y => ⟨e.symm (y.1.val,y.2.val),(hp _).mpr (by
             rw [e.apply_symm_apply]; exact ⟨y.1.property,y.2.property⟩)⟩
           left_inv := ?_, right_inv := ?_ }
  · intro x; apply Subtype.ext; exact e.symm_apply_apply _
  · rintro ⟨x,y⟩; apply Prod.ext <;> apply Subtype.ext <;> simp

private noncomputable def pairFactor (p : ℕ) : ℝ :=
  if p=2 then 1 else 1-1/((p:ℝ)-1)^2

private lemma pairFactor_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ pairFactor p := by
  by_cases h : p=2
  · simp [pairFactor,h]
  have h₃ : (3:ℝ)≤p := by exact_mod_cast (show 3≤p by have := hp.two_le; omega)
  dsimp [pairFactor]; rw [ite_eq_right h]
  have hden : 1 ≤ ((p:ℝ)-1)^2 := by nlinarith
  linarith only [div_le_one_of_le₀ hden (by positivity : 0 ≤ ((p:ℝ)-1)^2)]

private lemma primePowerPairs {p : ℕ} (hp : p.Prime) (k : ℕ) (s : ℤ)
    (he : p=2 → Even s) :
    (p - (if p=2 then 1 else 2)) * p^k ≤ Nat.card (pairResidues (p^(k+1)) s) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let q := p^(k+1)
  have hq : 0<q := pow_pos hp.pos _
  let : NeZero q := ⟨hq.ne'⟩
  let πq := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)
  have hu (x : ZMod q) : IsUnit x ↔ πq x ≠ 0 := by
    obtain ⟨a,rfl⟩ := ZMod.natCast_zmod_surjective x
    change IsUnit (a : ZMod (p^(k+1))) ↔ πq a ≠ 0
    rw [map_natCast, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)]
    exact (not_congr (ZMod.natCast_eq_zero_iff a p)).symm
  let R := ((Finset.univ : Finset (ZMod p)).erase 0).erase (s : ZMod p)
  have hr (x : {x // x∈R}) : (x.val ≠ (s : ZMod p) ∧ x.val ≠ 0) := by
    have h := Finset.mem_erase.mp x.property
    exact ⟨h.1,(Finset.mem_erase.mp h.2).1⟩
  have hcard : p - (if p=2 then 1 else 2) ≤ R.card := by
    have h0 : ((Finset.univ : Finset (ZMod p)).erase 0).card = p-1 := by
      simp [Finset.card_erase_of_mem, ZMod.card]
    by_cases h : p=2
    · have hs : (s : ZMod p) = 0 := by subst p; exact (he rfl).intCast_zmod_two
      simp [R,h,hs,h0]
    · have h' := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (ZMod p)).erase 0) (a := (s : ZMod p))
      dsimp [R]; rw [ite_eq_right h]; omega
  let code (v : {x // x∈R} × Fin (p^k)) := v.1.val.val + p*v.2.val
  have hcode (v : {x // x∈R} × Fin (p^k)) : code v < q := by
    have h₁ := v.1.val.val_lt
    have h₂ := v.2.isLt
    dsimp [code,q]; rw [pow_succ]
    nlinarith only [h₁,Nat.mul_le_mul_left p (show v.2.val+1≤p^k by omega)]
  have hred (v : {x // x∈R} × Fin (p^k)) : πq (code v : ZMod q) = v.1.val := by
    rw [map_natCast]; simp [code]
  let f (v : {x // x∈R} × Fin (p^k)) : pairResidues q s :=
    ⟨(code v : ZMod q),(hu _).mpr (by rw [hred]; exact (hr v.1).2),
      (hu _).mpr (by rw [map_sub,map_intCast,hred]; exact sub_ne_zero.mpr (hr v.1).1.symm)⟩
  have hf : Function.Injective f := by
    intro v w h
    have hrw : v.1.val = w.1.val := (hred v).symm.trans ((congrArg (fun z : pairResidues q s => πq z.val) h).trans (hred w))
    have hev := congrArg (fun z : pairResidues q s => z.val.val) h
    change (code v : ZMod q).val = (code w : ZMod q).val at hev
    rw [ZMod.val_natCast_of_lt (hcode v),ZMod.val_natCast_of_lt (hcode w)] at hev
    have hc : v.1.val.val = w.1.val.val := congrArg ZMod.val hrw
    have h₂ : v.2.val = w.2.val := by
      dsimp [code] at hev; rw [hc] at hev
      exact Nat.eq_of_mul_eq_mul_left hp.pos (Nat.add_left_cancel hev)
    exact Prod.ext (Subtype.ext hrw) (Fin.ext h₂)
  have hl := Nat.card_le_card_of_injective f hf
  apply (Nat.mul_le_mul_right (p^k) hcard).trans
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] using hl

private lemma pair_count_product (r : ℕ) :
    ∀ (s : ℤ), 0<r → (2∣r → Even s) →
      (r.totient : ℝ)^2*(∏ p ∈ r.primeFactors, pairFactor p) ≤
        (r:ℝ)*(Nat.card (pairResidues r s):ℝ) := by
  induction r using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one =>
    intro s _ _
    have h : Nonempty (pairResidues 1 s) := ⟨⟨1,isUnit_one,by
      rw [Subsingleton.elim (((s:ZMod 1)-1)) 1]; exact isUnit_one⟩⟩
    simpa using (show (1:ℝ) ≤ (Nat.card (pairResidues 1 s):ℝ) by
      exact_mod_cast (Nat.card_pos (α := pairResidues 1 s)))
  | prime_pow p n hp hn =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    intro s _ he
    have hnat := primePowerPairs hp k s (fun hh => he (hh ▸ dvd_pow_self p (Nat.succ_ne_zero k)))
    have hreal : (((p-(if p=2 then 1 else 2):ℕ):ℝ) * (p:ℝ)^k) ≤ Nat.card (pairResidues (p^(k+1)) s) := by exact_mod_cast hnat
    rw [Nat.totient_prime_pow_succ hp, Nat.primeFactors_prime_pow (Nat.succ_ne_zero _) hp,
      Finset.prod_singleton, Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hp.one_lt.le,Nat.cast_one, Nat.cast_pow,pow_succ (p:ℝ) k]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hreal (by positivity : 0≤(p:ℝ)^k*p))
    by_cases hh : p=2
    · subst p; norm_num [pairFactor]
      nlinarith only [sq_nonneg ((2:ℝ)^k)]
    · have hp3 : 3≤p := by have := hp.two_le; omega
      simp only [pairFactor,ite_eq_right hh, Nat.cast_sub (show 2≤p by omega), Nat.cast_ofNat]
      have hne : (p:ℝ)-1 ≠ 0 := by
        have h3 : (3:ℝ)≤p := by exact_mod_cast hp3
        linarith
      have hi : ((p:ℝ)-1)^2*(1-1/((p:ℝ)-1)^2) = (p:ℝ)*((p:ℝ)-2) := by field_simp; ring
      apply le_of_eq
      calc _ = ((p:ℝ)^k)^2 * (((p:ℝ)-1)^2*(1-1/((p:ℝ)-1)^2)) := by ring
           _ = _ := by rw [hi]; ring
  | coprime a b ha hb hab hA hB =>
    intro s _ he
    have ha0 := (zero_lt_one.trans ha)
    have hb0 := (zero_lt_one.trans hb)
    have : NeZero a := ⟨ha0.ne'⟩
    have : NeZero b := ⟨hb0.ne'⟩
    have A := hA s ha0 (fun h => he (dvd_mul_of_dvd_left h _))
    have B := hB s hb0 (fun h => he (dvd_mul_of_dvd_right h _))
    have hfit := Nat.card_congr (pairCRT hab s)
    rw [Nat.card_prod] at hfit
    have hnon : 0 ≤ (b.totient:ℝ)^2*∏ p ∈ b.primeFactors,pairFactor p :=
      mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun p hp => pairFactor_nonneg (Nat.prime_of_mem_primeFactors hp))
    have h := mul_le_mul A B hnon (by positivity)
    rw [Nat.totient_mul hab, Nat.primeFactors_mul ha0.ne' hb0.ne',
      Finset.prod_union hab.disjoint_primeFactors, hfit,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul]
    convert h using 1 <;> ring

private lemma pair_product_half (r : ℕ) : (1:ℝ)/2 ≤ ∏ p ∈ r.primeFactors,pairFactor p := by
  let M := max 2 r
  let S := (Finset.Icc 1 M).filter Nat.Prime
  have hbase := finiteEulerProd_ge_half 2 2 M (by decide) (le_max_left ..)
  have hf (p : ℕ) (hp : p.Prime) : 1+localFactor 2 2 p = pairFactor p := by
    by_cases h : p=2
    · simp [h,localFactor,pairFactor]
    · have hnd : ¬p ∣ 2 := fun hd => h ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
      simp [localFactor,pairFactor,h,hnd,sub_eq_add_neg]
  have hsub : r.primeFactors ⊆ S := by
    intro p hp
    obtain ⟨hp',hd,hr⟩ := Nat.mem_primeFactors.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp'.one_lt.le,
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hd).trans (le_max_right ..)⟩,hp'⟩
  have hone (p : ℕ) : pairFactor p ≤ 1 := by
    by_cases hp : p=2
    · simp [pairFactor,hp]
    · dsimp [pairFactor]; rw [ite_eq_right hp]; exact sub_le_self _ (by positivity)
  change _ ≤ ∏ p ∈ S,_ at hbase
  have hrw : (∏ p ∈ S, (1+localFactor 2 2 p)) = ∏ p ∈ S,pairFactor p :=
    Finset.prod_congr rfl fun p hp => hf p (Finset.mem_filter.mp hp).2
  rw [hrw,← Finset.prod_sdiff hsub] at hbase
  have he := real_prod_le_one (S \ r.primeFactors) pairFactor
    (fun p hp => pairFactor_nonneg (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2)
    (fun p _ => hone p)
  exact hbase.trans ((mul_le_mul_of_nonneg_right he (Finset.prod_nonneg fun p hp =>
    pairFactor_nonneg (Nat.prime_of_mem_primeFactors hp))).trans_eq (one_mul _))

private noncomputable def reducedOfUnit {r : ℕ} [NeZero r] (x : ZMod r) (hx : IsUnit x) :
    ReducedClass r :=
  ⟨x.val,mem_coprimeClasses.mpr ⟨x.val_lt,(ZMod.isUnit_iff_coprime _ _).mp (by simpa using hx)⟩⟩

private theorem ternary_fixed_fiber_lower {r n : ℕ} (hr : 0<r) (hn : Odd n) (b : ReducedClass r) :
    (1/2:ℝ)*(r.totient:ℝ)^2/r ≤
      (((ternaryCompatibleTriples r n).filter (fun t => t.1=b)).card:ℝ) := by
  let : NeZero r := ⟨hr.ne'⟩
  let s : ℤ := n - (b.val : ℤ)
  have he (hd : 2∣r) : Even s := by
    have hb : Odd b.val := ((mem_coprimeClasses.mp b.property).2.of_dvd_right hd).odd_of_right
    obtain ⟨i,hi⟩ := hn
    obtain ⟨j,hj⟩ := hb
    refine ⟨(i:ℤ)-(j:ℤ),?_⟩
    dsimp [s]; rw [hi,hj]; push_cast; ring
  have h := pair_count_product r s hr he
  have hl := mul_le_mul_of_nonneg_left (pair_product_half r) (sq_nonneg (r.totient:ℝ))
  have hbound : (1/2:ℝ)*(r.totient:ℝ)^2/r ≤ Nat.card (pairResidues r s) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hr)).2
    nlinarith only [hl,h]
  let T := (ternaryCompatibleTriples r n).filter fun t => t.1=b
  let f (x : pairResidues r s) : {t // t∈T} := by
    let c := reducedOfUnit x.val x.property.1
    let d := reducedOfUnit ((s : ZMod r)-x.val) x.property.2
    refine ⟨(b,c,d), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨by simp,?_⟩,rfl⟩⟩
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    change (n:ZMod r)=((b.val+c.val+d.val : ℕ) : ZMod r)
    push_cast
    change _ = _ + (x.val.val : ZMod r) + (((s : ZMod r)-x.val).val : ZMod r)
    rw [ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
    dsimp [s]; push_cast; ring
  have hi : Function.Injective f := by
    intro x y h
    have hc := congrArg (fun t : {t // t∈T} => (t.val.2.1.val : ZMod r)) h
    apply Subtype.ext
    change (x.val.val : ZMod r) = (y.val.val : ZMod r) at hc
    simpa using hc
  refine hbound.trans ?_
  exact_mod_cast (show Nat.card (pairResidues r s) ≤ T.card by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective f hi)

/-- Every odd target has at least a constant fraction of the expected number of
compatible ordered triples of reduced residues, for every positive modulus. -/
theorem ternaryCompatibleTriples_card_lower {r n : ℕ} (hr : 0 < r) (hn : Odd n) :
    (1/2:ℝ)*(r.totient:ℝ)^3/r ≤ ((ternaryCompatibleTriples r n).card:ℝ) := by
  let C := (coprimeClasses r).attach
  let T := ternaryCompatibleTriples r n
  have hf := Finset.card_eq_sum_card_fiberwise (s:=T) (t:=C) (f:=Prod.fst)
    (fun t _ => Finset.mem_attach _ t.1)
  rw [hf,Nat.cast_sum]
  calc _ = ∑ _b ∈ C, (1/2:ℝ)*(r.totient:ℝ)^2/r := by
           simp only [C,Finset.sum_const,Finset.card_attach,card_coprimeClasses,nsmul_eq_mul]
           ring
       _ ≤ _ := Finset.sum_le_sum fun b _ => ternary_fixed_fiber_lower hr hn b

end FareyGoldbach
