import FareyGoldbach.VaughanIdentity
import FareyGoldbach.ChenSwitchingScales

/-! # Finite twisted sums for Vaughan's decomposition -/

open Finset ArithmeticFunction
open scoped Classical

namespace FareyGoldbach

noncomputable def vaughanTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X : ℕ) (f : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ Icc 1 X, (f n : ℂ)*χ (n:ZMod q)

noncomputable def vaughanBilinear {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X l M lo : ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Icc l M, f m*χ (m:ZMod q) *
    (∑ w ∈ Icc lo (X/m), g w*χ (w:ZMod q))

private theorem vaughanTwist_sub {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X : ℕ) (f g : ArithmeticFunction ℝ) :
    vaughanTwist χ X (f-g) = vaughanTwist χ X f-vaughanTwist χ X g := by
  simp only [vaughanTwist,sub_apply,Complex.ofReal_sub,sub_mul,sum_sub_distrib]

private theorem vaughanTwist_add {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X : ℕ) (f g : ArithmeticFunction ℝ) :
    vaughanTwist χ X (f+g) = vaughanTwist χ X f+vaughanTwist χ X g := by
  simp only [vaughanTwist,add_apply,Complex.ofReal_add,add_mul,sum_add_distrib]

private theorem vaughanTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X : ℕ) (f g : ArithmeticFunction ℝ) :
    vaughanTwist χ X (f*g) = vaughanBilinear χ X 1 X 1
      (fun m => (f m:ℂ)) (fun w => (g w:ℂ)) := by
  let S := (Icc 1 X).sigma Nat.divisorsAntidiagonal
  let T := (Icc 1 X).sigma (fun m => Icc 1 (X/m))
  let a (p : Σ _ : ℕ, ℕ × ℕ) := (f p.2.1:ℂ)*(g p.2.2:ℂ)*χ (p.1:ZMod q)
  let b (p : Σ _ : ℕ, ℕ) := (f p.1:ℂ)*χ (p.1:ZMod q)*((g p.2:ℂ)*χ (p.2:ZMod q))
  calc
    _ = ∑ p ∈ S,a p := by
      simp only [vaughanTwist,S,sum_sigma,a]
      apply sum_congr rfl
      intro n _
      rw [ArithmeticFunction.mul_apply,Complex.ofReal_sum,sum_mul]
      simp only [Complex.ofReal_mul]
    _ = ∑ p ∈ T,b p := by
      refine Finset.sum_bij' (fun p _ => ⟨p.2.1,p.2.2⟩)
        (fun p _ => ⟨p.1*p.2,(p.1,p.2)⟩) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        have ⟨hn,hpair⟩ := mem_sigma.mp hp
        have ⟨he,hne⟩ := Nat.mem_divisorsAntidiagonal.mp hpair
        have hxy := (mem_Icc.mp hn).2
        have hm : 0 < p.2.1 := Nat.pos_of_ne_zero (by
          intro hm
          simp [hm] at he
          exact hne he.symm)
        have hw : 0 < p.2.2 := Nat.pos_of_ne_zero (by
          intro hw
          simp [hw] at he
          exact hne he.symm)
        have hle : p.2.1*p.2.2 ≤ X := by rwa [he]
        apply mem_sigma.mpr
        refine ⟨mem_Icc.mpr ⟨hm,(Nat.le_mul_of_pos_right _ hw).trans hle⟩,
          mem_Icc.mpr ⟨hw,(Nat.le_div_iff_mul_le hm).mpr ?_⟩⟩
        rw [Nat.mul_comm,he]
        exact hxy
      · intro p hp
        have ⟨hm,hw⟩ := mem_sigma.mp hp
        have hm₀ := (mem_Icc.mp hm).1
        have hw₀ := (mem_Icc.mp hw).1
        have hpos := Nat.mul_pos hm₀ hw₀
        have hle := (Nat.le_div_iff_mul_le hm₀).mp (mem_Icc.mp hw).2
        exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hpos,(Nat.mul_comm p.1 p.2) ▸ hle⟩,
          Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,hpos.ne'⟩⟩
      · rintro ⟨n,⟨m,w⟩⟩ hp
        have he := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hp).2).1
        simp only at he
        subst n
        rfl
      · intros
        rfl
      · intro p hp
        have he := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp hp).2).1
        dsimp only [a,b]
        rw [←he,Nat.cast_mul,map_mul]
        ring
    _ = _ := by simp only [T,sum_sigma,b,vaughanBilinear,mul_sum]

private theorem vaughanBilinear_restrict {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X l M lo : ℕ) (hl : 1≤l) (hlo : 1≤lo) (f g : ℕ → ℂ)
    (hleft : ∀ m < l, f m=0)
    (hright : ∀ m, M<m → f m=0 ∨ X/m<lo)
    (hinner : ∀ w < lo, g w=0) :
    vaughanBilinear χ X 1 X 1 f g = vaughanBilinear χ X l M lo f g := by
  let F (m : ℕ) := f m*χ (m:ZMod q)*(∑ w ∈ Icc lo (X/m),g w*χ (w:ZMod q))
  have he (m : ℕ) : (∑ w ∈ Icc 1 (X/m),g w*χ (w:ZMod q)) =
      ∑ w ∈ Icc lo (X/m),g w*χ (w:ZMod q) := by
    symm
    apply Finset.sum_subset (Icc_subset_Icc_left hlo)
    intro w hw hn
    have hw' : w<lo := by simp only [mem_Icc] at hw hn; omega
    rw [hinner w hw',zero_mul]
  simp_rw [vaughanBilinear,he]
  change (∑ m ∈ Icc 1 X,F m) = ∑ m ∈ Icc l M,F m
  let I := Icc l (min X M)
  have h₁ : I ⊆ Icc 1 X := fun m hm => by
    have hm' := mem_Icc.mp hm
    exact mem_Icc.mpr ⟨hl.trans hm'.1,hm'.2.trans (min_le_left ..)⟩
  have h₂ : I ⊆ Icc l M := fun m hm => by
    have hm' := mem_Icc.mp hm
    exact mem_Icc.mpr ⟨hm'.1,hm'.2.trans (min_le_right ..)⟩
  have hz (m : ℕ) (h : X/m<lo) : F m=0 := by
    simp only [F,Icc_eq_empty_of_lt h,sum_empty,mul_zero]
  calc
    _ = ∑ m ∈ I,F m := by
      symm
      apply sum_subset h₁
      intro m hm hn
      have h : m<l ∨ M<m := by simp only [I,mem_Icc,le_min_iff] at hm hn; omega
      rcases h with h | h
      · simp only [F,hleft _ h,zero_mul]
      · rcases hright _ h with h | h
        · simp only [F,h,zero_mul]
        · exact hz _ h
    _ = _ := by
      apply sum_subset h₂
      intro m hm hn
      have h : X<m := by simp only [I,mem_Icc,le_min_iff] at hm hn; omega
      apply hz
      rw [Nat.div_eq_of_lt h]
      exact hlo

theorem vaughan_mu_abs_le (V m : ℕ) : |vaughanMu V m|≤1 := by
  rw [vaughanMu,vaughanCut_apply]
  split_ifs
  · rw [ArithmeticFunction.intCoe_apply,←Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=m)
  · simp

theorem vaughan_alpha_abs_le (U V m : ℕ) :
    |vaughanAlpha U V m|≤Real.log (m:ℝ) := by
  rw [vaughanAlpha,ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ x ∈ m.divisorsAntidiagonal, |vaughanMu V x.1 * vaughanCut U vonMangoldt x.2| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le m.divisorsAntidiagonal
          (fun x => vaughanMu V x.1*vaughanCut U vonMangoldt x.2))
    _ ≤ ∑ x ∈ m.divisorsAntidiagonal, vonMangoldt x.2 := by
      apply sum_le_sum
      intro x _
      rw [vaughanCut_apply]
      split_ifs
      · rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_of_le_one_left vonMangoldt_nonneg (vaughan_mu_abs_le _ _)
      · simpa only [mul_zero,abs_zero] using (vonMangoldt_nonneg (n:=x.2))
    _ = Real.log (m:ℝ) := by
      rw [←ArithmeticFunction.log_apply, ←vonMangoldt_mul_zeta, mul_comm, ArithmeticFunction.mul_apply]
      apply sum_congr rfl
      intro x hx
      rw [ArithmeticFunction.natCoe_apply,
        zeta_apply_ne (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)).ne',
        Nat.cast_one,one_mul]

theorem vaughan_mu_div_abs_le (V m : ℕ) : |vaughanMuDiv V m|≤(m.divisors.card:ℝ) := by
  rw [vaughanMuDiv,ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ x ∈ m.divisorsAntidiagonal, |vaughanMu V x.1 * (zeta : ArithmeticFunction ℝ) x.2| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le m.divisorsAntidiagonal (fun x => vaughanMu V x.1*(zeta : ArithmeticFunction ℝ) x.2))
    _ ≤ ∑ _x ∈ m.divisorsAntidiagonal, (1:ℝ) := by
      apply sum_le_sum
      intro x hx
      rw [ArithmeticFunction.natCoe_apply,
        zeta_apply_ne (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).ne',
        Nat.cast_one,mul_one]
      exact vaughan_mu_abs_le _ _
    _ = _ := by rw [←Nat.map_div_right_divisors]; simp

theorem vaughan_twisted_identity {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X U : ℕ) (hU : 1≤U) :
    vaughanTwist χ X vonMangoldt =
      vaughanTwist χ X (vaughanCut U vonMangoldt) -
      vaughanBilinear χ X 1 U 1 (fun m => (vaughanAlpha U U m:ℂ)) (fun _ => 1) +
      vaughanBilinear χ X 1 U 1 (fun m => (vaughanMu U m:ℂ)) (fun w => (Real.log (w:ℝ):ℂ)) -
      vaughanBilinear χ X (U+1) (U*U) 1 (fun m => (vaughanAlpha U U m:ℂ)) (fun _ => 1) -
      vaughanBilinear χ X (U+1) (X/(U+1)) (U+1)
        (fun m => (vaughanMuDiv U m:ℂ)) (fun w => (vonMangoldt w:ℂ)) := by
  have h := congrArg (vaughanTwist χ X) (vaughan_identity U U hU)
  simp only [vaughanTwist_sub,vaughanTwist_add,vaughanTwist_mul] at h
  have hα := vaughanBilinear_restrict χ X 1 (U*U) 1 le_rfl le_rfl
    (fun m => (vaughanAlpha U U m:ℂ)) (fun w => ((zeta : ArithmeticFunction ℝ) w:ℂ))
    (by intro m hm; simp [show m=0 by omega])
    (fun m hm => Or.inl (by rw [vaughanAlpha_eq_zero_of_lt hm,Complex.ofReal_zero]))
    (by intro w hw; simp [show w=0 by omega])
  have hμ := vaughanBilinear_restrict χ X 1 U 1 le_rfl le_rfl
    (fun m => (vaughanMu U m:ℂ)) (fun w => (ArithmeticFunction.log w:ℂ))
    (by intro m hm; simp [show m=0 by omega])
    (fun m hm => Or.inl (by simp [vaughanMu,vaughanCut_apply,not_le_of_gt hm]))
    (by intro w hw; simp [show w=0 by omega])
  have htail := vaughanBilinear_restrict χ X (U+1) (X/(U+1)) (U+1)
    (Nat.succ_pos U) (Nat.succ_pos U)
    (fun m => (vaughanTail U (vaughanMuDiv U) m:ℂ))
    (fun w => (vaughanTail U vonMangoldt w:ℂ))
    (by intro m hm; simp [vaughanTail_apply,show ¬U<m by omega])
    (by
      intro m hm
      right
      have hm₀ : 0<m := (Nat.zero_le _).trans_lt hm
      have hprod : X<m*(U+1) := (Nat.div_lt_iff_lt_mul (Nat.succ_pos U)).mp hm
      rw [Nat.div_lt_iff_lt_mul hm₀,Nat.mul_comm]
      exact hprod)
    (by intro w hw; simp [vaughanTail_apply,show ¬U<w by omega])
  rw [hα,hμ,htail] at h
  have hzeta : vaughanBilinear χ X 1 (U*U) 1
        (fun m => (vaughanAlpha U U m:ℂ)) (fun w => ((zeta : ArithmeticFunction ℝ) w:ℂ)) =
      vaughanBilinear χ X 1 (U*U) 1 (fun m => (vaughanAlpha U U m:ℂ)) (fun _ => 1) := by
    unfold vaughanBilinear
    apply sum_congr rfl
    intro m _
    congr 1
    apply sum_congr rfl
    intro w hw
    dsimp only
    rw [ArithmeticFunction.natCoe_apply,zeta_apply_ne (Nat.ne_of_gt (mem_Icc.mp hw).1),
      Nat.cast_one,Complex.ofReal_one]
  have htail' : vaughanBilinear χ X (U+1) (X/(U+1)) (U+1)
      (fun m => (vaughanTail U (vaughanMuDiv U) m:ℂ))
      (fun w => (vaughanTail U vonMangoldt w:ℂ)) =
      vaughanBilinear χ X (U+1) (X/(U+1)) (U+1)
        (fun m => (vaughanMuDiv U m:ℂ)) (fun w => (vonMangoldt w:ℂ)) := by
    unfold vaughanBilinear
    apply sum_congr rfl
    intro m hm
    dsimp only
    rw [vaughanTail_apply,ite_eq_left (Nat.lt_of_succ_le (mem_Icc.mp hm).1)]
    congr 1
    apply sum_congr rfl
    intro w hw
    rw [vaughanTail_apply,ite_eq_left (Nat.lt_of_succ_le (mem_Icc.mp hw).1)]
  have hsplit : vaughanBilinear χ X 1 (U*U) 1
      (fun m => (vaughanAlpha U U m:ℂ)) (fun _ => 1) =
      vaughanBilinear χ X 1 U 1 (fun m => (vaughanAlpha U U m:ℂ)) (fun _ => 1) +
      vaughanBilinear χ X (U+1) (U*U) 1 (fun m => (vaughanAlpha U U m:ℂ)) (fun _ => 1) := by
    have hU' : U≤U*U := Nat.le_mul_of_pos_right U hU
    have hd : Disjoint (Icc 1 U) (Icc (U+1) (U*U)) := by
      rw [disjoint_left]
      intro m hm hw
      simp only [mem_Icc] at hm hw
      omega
    have hu : Icc 1 (U*U) = Icc 1 U ∪ Icc (U+1) (U*U) := by
      ext m
      simp only [mem_union,mem_Icc]
      omega
    simpa only [vaughanBilinear] using
      (show (∑ m ∈ Icc 1 (U*U), (vaughanAlpha U U m:ℂ)*χ (m:ZMod q)*
          (∑ w ∈ Icc 1 (X/m), (1:ℂ)*χ (w:ZMod q))) = _ from by
        rw [hu,sum_union hd])
  rw [hzeta,hsplit,htail'] at h
  rw [h]
  simp only [ArithmeticFunction.log_apply]
  abel

end FareyGoldbach
