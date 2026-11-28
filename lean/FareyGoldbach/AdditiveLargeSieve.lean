import FareyGoldbach.AveragedRemainder

/-! # The additive large sieve for reduced rational frequencies

The proof uses disjoint right-hand sampling intervals of length
`(8N + Q²)⁻¹`. Their union lies in one period.
-/

open MeasureTheory Set
open scoped Classical

namespace FareyGoldbach

private lemma integral_sq_le_length_mul {f : ℝ → ℝ} (hf : Continuous f)
    {x y : ℝ} (hxy : x ≤ y) :
    (∫ t in x..y, f t)^2 ≤ (y-x)*(∫ t in x..y, (f t)^2) := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  let A := ∫ t in x..y, f t
  let B := ∫ t in x..y, (f t)^2
  let a := A/(y-x)
  have h := intervalIntegral.integral_nonneg (μ:=volume) hxy (fun t _ => sq_nonneg (f t-a))
  have hEq : (∫ t in x..y, (f t-a)^2) = B - (2*a)*A + (y-x)*a^2 := by
    have he : (∫ t in x..y, (f t-a)^2) =
        ∫ t in x..y, ((f t)^2-(2*a)*f t)+a^2 :=
      intervalIntegral.integral_congr fun t _ => by ring
    have hf₂ : IntervalIntegrable (fun t => f t^2) volume x y := (hf.pow 2).intervalIntegrable ..
    have hfa : IntervalIntegrable (fun t => (2*a)*f t) volume x y :=
      (hf.intervalIntegrable ..).const_mul _
    have hfs : IntervalIntegrable (fun t => f t^2-(2*a)*f t) volume x y := hf₂.sub hfa
    have hconst : IntervalIntegrable (fun _ : ℝ => a^2) volume x y :=
      continuous_const.intervalIntegrable ..
    rw [he, intervalIntegral.integral_add hfs hconst, intervalIntegral.integral_sub hf₂ hfa,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  rw [hEq] at h
  have hd : 0<y-x := sub_pos.mpr hlt
  have he : (y-x)*(B-(2*a)*A+(y-x)*a^2) = (y-x)*B-A^2 := by
    dsimp only [a]
    field_simp; ring
  have h' := mul_nonneg hd.le h
  rw [he] at h'
  exact sub_nonneg.mp h'

private lemma trig_sample {F D : ℝ → ℂ} (hF : Continuous F) (hD : Continuous D)
    (hder : ∀ x, HasDerivAt F (D x) x) {h : ℝ} (hh : 0<h) (x : ℝ) :
    ‖F x‖^2 ≤ (2/h)*(∫ t in x..x+h, ‖F t‖^2) +
      (2*h)*(∫ t in x..x+h, ‖D t‖^2) := by
  have hx : x≤x+h := le_add_of_nonneg_right hh.le
  let K := ∫ t in x..x+h, ‖D t‖^2
  have hK : 0≤K := intervalIntegral.integral_nonneg hx fun _ _ => sq_nonneg _
  have hp (t : ℝ) (ht : t∈Icc x (x+h)) : ‖F x‖^2 ≤ 2*‖F t‖^2+2*h*K := by
    have hdiff : (∫ u in x..t, D u) = F t-F x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hder u) (hD.intervalIntegrable ..)
    have hi : ‖F t-F x‖≤∫ u in x..t, ‖D u‖ := by
      rw [←hdiff]
      exact intervalIntegral.norm_integral_le_integral_norm ht.1
    have hsq := (pow_le_pow_left₀ (norm_nonneg _) hi 2).trans
      (integral_sq_le_length_mul hD.norm ht.1)
    have hsub : (∫ u in x..t, ‖D u‖^2) ≤ K :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) ((hD.norm.pow 2).intervalIntegrable ..)
    have hdt : t-x≤h := by linarith only [ht.2]
    have hdist : ‖F t-F x‖^2 ≤ h*K :=
      hsq.trans (mul_le_mul hdt hsub (intervalIntegral.integral_nonneg ht.1 (fun _ _ => sq_nonneg _)) hh.le)
    have hadd := norm_add_le (F t) (F x-F t)
    rw [show F t+(F x-F t)=F x by abel, norm_sub_rev] at hadd
    have habs := pow_le_pow_left₀ (norm_nonneg _) hadd 2
    nlinarith only [hdist,habs,sq_nonneg (‖F t‖-‖F t-F x‖)]
  have hfc : IntervalIntegrable (fun _ : ℝ => ‖F x‖^2) volume x (x+h) :=
    continuous_const.intervalIntegrable ..
  have hpc : IntervalIntegrable (fun t => 2*‖F t‖^2) volume x (x+h) :=
    ((hF.norm.pow 2).intervalIntegrable ..).const_mul _
  have hkc : IntervalIntegrable (fun _ : ℝ => 2*h*K) volume x (x+h) :=
    continuous_const.intervalIntegrable ..
  have hineq := intervalIntegral.integral_mono_on hx hfc (hpc.add hkc) hp
  rw [intervalIntegral.integral_add hpc hkc,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,intervalIntegral.integral_const,smul_eq_mul,smul_eq_mul] at hineq
  have he : x+h-x=h := by ring
  rw [he] at hineq
  apply (le_of_mul_le_mul_left ?_ hh)
  calc h*‖F x‖^2 ≤ 2*(∫ t in x..x+h, ‖F t‖^2)+h*(2*h*K) := by
         simpa only [mul_comm] using hineq
       _ = h*((2/h)*(∫ t in x..x+h, ‖F t‖^2)+(2*h)*K) := by field_simp

private lemma hasDerivAt_trig {N : ℕ} (b : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun t => ∑ j ∈ Finset.range N, b j*e (t*(j:ℝ)))
      (∑ j ∈ Finset.range N, (b j*(2*(Real.pi:ℂ)*(j:ℂ)*Complex.I))*e (t*(j:ℝ))) t := by
  apply HasDerivAt.fun_sum
  intro j _
  let c : ℂ := 2*(Real.pi:ℂ)*(j:ℂ)*Complex.I
  have hc : HasDerivAt (fun u : ℝ => c*(u:ℂ)) c t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x:=t)).const_mul c
  have he : (fun u : ℝ => Complex.exp (c*(u:ℂ))) = fun u => e (u*(j:ℝ)) := by
    funext u
    unfold e
    congr 1
    dsimp only [c]
    push_cast
    ring
  have hd := hc.cexp.const_mul (b j)
  simp_rw [congrFun he] at hd
  convert hd using 1
  ring

private lemma sum_disjoint_interval_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {h : ℝ} (hh : 0<h)
    (h0 : ∀ i∈s, 0≤x i) (h1 : ∀ i∈s, x i+h≤1)
    (hsep : ∀ i∈s, ∀ j∈s, i≠j → h≤|x i-x j|)
    {f : ℝ → ℝ} (hf : Continuous f) (hn : ∀ t, 0≤f t) :
    (∑ i ∈ s, ∫ t in x i..x i+h, f t) ≤ ∫ t in (0:ℝ)..1, f t := by
  let T (i : ι) := Ioc (x i) (x i+h)
  have hd : Set.Pairwise (↑s) (Function.onFun Disjoint T) := by
    intro i hi j hj hij
    have hs := hsep i hi j hj hij
    rcases le_total (x i) (x j) with hl | hl
    · rw [abs_of_nonpos (sub_nonpos.mpr hl)] at hs
      exact Ioc_disjoint_Ioc_of_le (by linarith only [hs])
    · rw [abs_of_nonneg (sub_nonneg.mpr hl)] at hs
      exact (Ioc_disjoint_Ioc_of_le (by linarith only [hs])).symm
  have hsub : ∀ i∈s, T i⊆Ioc (0:ℝ) 1 :=
    fun i hi => Ioc_subset_Ioc (h0 i hi) (h1 i hi)
  have hint : IntegrableOn f (Ioc (0:ℝ) 1) :=
    (hf.intervalIntegrable (μ:=volume) (0:ℝ) 1).1
  have hu : (⋃ i∈s, T i)⊆Ioc (0:ℝ) 1 := by
    simp only [iUnion_subset_iff]
    exact hsub
  have he (i : ι) : (∫ t in x i..x i+h, f t) = ∫ t in T i, f t :=
    intervalIntegral.integral_of_le (le_add_of_nonneg_right hh.le)
  simp_rw [he, intervalIntegral.integral_of_le zero_le_one]
  rw [← integral_biUnion_finset s (fun _ _ => measurableSet_Ioc) hd
    (fun i hi => hint.mono_set (hsub i hi))]
  exact setIntegral_mono_set hint (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall fun _ ht => hu ht)

private lemma reduced_center_bound {Q : ℕ} {c : RatCenter} (hc : c∈centers Q) :
    0≤c.val ∧ c.val+1/(Q:ℝ)^2≤1 := by
  have hq : (0:ℝ)<c.q := Nat.cast_pos.mpr c.q_pos
  have hq1 : (1:ℝ)≤c.q := Nat.one_le_cast.mpr c.q_pos
  have hqQ : (c.q:ℝ)≤Q := Nat.cast_le.mpr (mem_centers_iff.mp hc)
  have hp : (c.q:ℝ)≤(Q:ℝ)^2 := by nlinarith only [hq1,hqQ,mul_nonneg (show 0≤(Q:ℝ)-1 by linarith) (Nat.cast_nonneg Q)]
  have hfrac := one_div_le_one_div_of_le hq hp
  have ha : (c.a:ℝ)+1≤c.q := by exact_mod_cast c.a_lt
  refine ⟨div_nonneg (Nat.cast_nonneg _) hq.le,?_⟩
  calc c.val+1/(Q:ℝ)^2 ≤ c.val+1/(c.q:ℝ) := add_le_add_right hfrac _
       _ = ((c.a:ℝ)+1)/(c.q:ℝ) := by rw [RatCenter.val,add_div]
       _ ≤ 1 := (div_le_one hq).mpr ha

private lemma reduced_center_sep {Q : ℕ} {c d : RatCenter} (hc : c∈centers Q)
    (hd : d∈centers Q) (hne : c≠d) :
    1/(Q:ℝ)^2≤|c.val-d.val| := by
  have hq : (0:ℝ)<c.q := Nat.cast_pos.mpr c.q_pos
  have hr : (0:ℝ)<d.q := Nat.cast_pos.mpr d.q_pos
  have hmul : (c.q:ℝ)*(d.q:ℝ)≤(Q:ℝ)^2 := by
    rw [pow_two]
    exact mul_le_mul (Nat.cast_le.mpr (mem_centers_iff.mp hc))
      (Nat.cast_le.mpr (mem_centers_iff.mp hd)) hr.le (Nat.cast_nonneg _)
  exact (one_div_le_one_div_of_le (mul_pos hq hr) hmul).trans
    ((ratCenter_separation hne).trans (by simpa using abs_wrap_le_abs_sub_int (c.val-d.val) 0))

private theorem separated_range_large_sieve {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {P : ℝ} (hP : 0 < P) (h0 : ∀ i∈S, 0≤x i)
    (h1 : ∀ i∈S, x i+1/P≤1)
    (hsep : ∀ i∈S, ∀ j∈S, i≠j → 1/P≤|x i-x j|)
    (N : ℕ) (b : ℕ→ℂ) :
    (∑ c ∈ S, ‖∑ j ∈ Finset.range N,b j*e (x c*(j:ℝ))‖^2) ≤
      50*((N:ℝ)+P)*(∑ j ∈ Finset.range N, ‖b j‖^2) := by
  let h := 1/(8*(N:ℝ)+P)
  have hh : 0<h := by dsimp [h]; positivity
  have hδ : h≤1/P := one_div_le_one_div_of_le hP (le_add_of_nonneg_left (by positivity))
  let F (t : ℝ) := ∑ j ∈ Finset.range N,b j*e (t*(j:ℝ))
  let f (j : ℕ) := b j*(2*(Real.pi:ℂ)*(j:ℂ)*Complex.I)
  let D (t : ℝ) := ∑ j ∈ Finset.range N,f j*e (t*(j:ℝ))
  have hcF : Continuous F :=
    continuous_sum_finset _ fun j _ => continuous_const.mul (by simpa only [mul_comm] using continuous_e_mul (j:ℝ))
  have hcD : Continuous D :=
    continuous_sum_finset _ fun j _ => continuous_const.mul (by simpa only [mul_comm] using continuous_e_mul (j:ℝ))
  have h1' (i) (hi : i∈S) : x i+h≤1 := (add_le_add_right hδ _).trans (h1 i hi)
  have hsep' (i) (hi : i∈S) (j) (hj : j∈S) (hne : i≠j) :
      h≤|x i-x j| := hδ.trans (hsep i hi j hj hne)
  have hF := sum_disjoint_interval_le S x hh h0 h1' hsep' (hcF.norm.pow 2)
    (fun t => sq_nonneg ‖F t‖)
  have hD := sum_disjoint_interval_le S x hh h0 h1' hsep' (hcD.norm.pow 2)
    (fun t => sq_nonneg ‖D t‖)
  let A := ∑ j ∈ Finset.range N, ‖b j‖^2
  have hA : 0≤A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : (∑ j ∈ Finset.range N, ‖f j‖^2)≤64*(N:ℝ)^2*A := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjN : (j:ℝ)≤N := Nat.cast_le.mpr (Finset.mem_range.mp hj).le
    have hnorm : ‖2*(Real.pi:ℂ)*(j:ℂ)*Complex.I‖≤8*(N:ℝ) := by
      simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_natCast]
      norm_num
      exact (mul_le_mul (show 2*Real.pi≤8 by linarith [Real.pi_lt_four]) hjN
        (Nat.cast_nonneg _) (by positivity))
    dsimp only [f]
    rw [norm_mul,mul_pow]
    have hn := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith only [mul_le_mul_of_nonneg_left hn (sq_nonneg ‖b j‖)]
  have hd : ∀ t, HasDerivAt F (D t) t := hasDerivAt_trig b
  change ∑ c ∈ S, ‖F (x c)‖^2 ≤ _
  calc
    _ ≤ ∑ c ∈ S, ((2/h)*(∫ t in x c..x c+h,‖F t‖^2)+
        (2*h)*(∫ t in x c..x c+h,‖D t‖^2)) := Finset.sum_le_sum fun c _ =>
          trig_sample hcF hcD hd hh (x c)
    _ ≤ (2/h)*A+(2*h)*(64*(N:ℝ)^2*A) := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left (hF.trans_eq (integral_norm_sq_trigPoly N b)) (by positivity))
        (mul_le_mul_of_nonneg_left ((hD.trans_eq (integral_norm_sq_trigPoly N f)).trans hE) (by positivity))
    _ ≤ _ := by
      have hmul : (8*(N:ℝ))*h≤1 := by
        dsimp only [h]; rw [mul_one_div]; exact (div_le_one (by positivity)).mpr
          (le_add_of_nonneg_right hP.le)
      have he : 2/h=2*(8*(N:ℝ)+P) := by dsimp [h]; field_simp
      rw [he]
      have hmul' := mul_le_mul_of_nonneg_right hmul (show 0≤(N:ℝ)*A by positivity)
      have hQ' : 0≤P*A := by positivity
      have hN' : 0≤(N:ℝ)*A := by positivity
      nlinarith only [hmul',hN',hQ']

private lemma sum_over_centers (Q : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ c ∈ centers Q, f c.q c.a) = ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ coprimeClasses q, f q a := by
  rw [Finset.sum_sigma' (Finset.Icc 1 Q) coprimeClasses f]
  apply Finset.sum_bij (fun c _ => ⟨c.q,c.a⟩)
  · intro c hc
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨c.q_pos,mem_centers_iff.mp hc⟩,
      mem_coprimeClasses.mpr ⟨c.a_lt,c.coprime⟩⟩
  · intro c _ d _ hd
    exact RatCenter.ext (congrArg Sigma.snd hd) (congrArg Sigma.fst hd)
  · rintro ⟨q,a⟩ ha
    obtain ⟨hq,ha⟩ := Finset.mem_sigma.mp ha
    obtain ⟨h1,hQ⟩ := Finset.mem_Icc.mp hq
    obtain ⟨hal,hac⟩ := mem_coprimeClasses.mp ha
    exact ⟨⟨a,q,h1,hal,hac⟩,mem_centers_iff.mpr hQ,rfl⟩
  · intro c _
    rfl

private lemma sum_range_shift {G : Type*} [AddCommMonoid G] (M N : ℕ) (f : ℕ → G) :
    (∑ j ∈ Finset.range N, f (M+1+j)) = ∑ n ∈ Finset.Ioc M (M+N), f n := by
  apply Finset.sum_bij (fun j _ => M+1+j)
  · intro j hj
    have h := Finset.mem_range.mp hj
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  · intro x _ y _ he
    omega
  · intro n hn
    obtain ⟨h1,h2⟩ := Finset.mem_Ioc.mp hn
    refine ⟨n-(M+1),Finset.mem_range.mpr (by omega),by omega⟩
  · intro j _
    rfl

/-- The additive large sieve on a finite separated set. Each sampling interval starts
at its frequency, so the endpoint hypothesis is the right-hand margin within one period. -/
theorem separated_large_sieve {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    {P : ℝ} (hP : 0 < P) (h0 : ∀ i∈S, 0≤x i)
    (h1 : ∀ i∈S, x i+1/P≤1)
    (hsep : ∀ i∈S, ∀ j∈S, i≠j → 1/P≤|x i-x j|)
    (M N : ℕ) (a : ℕ→ℂ) :
    (∑ c ∈ S, ‖∑ n ∈ Finset.Ioc M (M+N), a n * e ((n:ℝ)*x c)‖^2) ≤
      50*((N:ℝ)+P)*(∑ n ∈ Finset.Ioc M (M+N), ‖a n‖^2) := by
  have hn (c : ι) :
      ‖∑ j ∈ Finset.range N, a (M+1+j) * e (x c*(j:ℝ))‖^2 =
      ‖∑ n ∈ Finset.Ioc M (M+N), a n * e ((n:ℝ)*x c)‖^2 := by
    have hs : (∑ n ∈ Finset.Ioc M (M+N), a n*e ((n:ℝ)*x c)) =
        e (x c*((M+1:ℕ):ℝ))*(∑ j ∈ Finset.range N,a (M+1+j)*e (x c*(j:ℝ))) := by
      rw [←sum_range_shift,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have he : ((M+1+j:ℕ):ℝ)*x c = x c*((M+1:ℕ):ℝ) + x c*(j:ℝ) := by
        push_cast
        ring
      rw [he,e_add]
      ring
    rw [hs,norm_mul,norm_e,one_mul]
  have hmass : (∑ j ∈ Finset.range N, ‖a (M+1+j)‖^2) =
      ∑ n ∈ Finset.Ioc M (M+N), ‖a n‖^2 := by
    exact sum_range_shift M N (fun n => ‖a n‖^2)
  have hb := separated_range_large_sieve S x hP h0 h1 hsep N (fun j => a (M+1+j))
  simp_rw [hn,hmass] at hb
  exact hb

/-- An effective additive large sieve, uniform in the left endpoint (M). -/
theorem additive_large_sieve (M N Q : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ coprimeClasses q,
      ‖∑ n ∈ Finset.Ioc M (M+N), a n * e ((n:ℝ)*b/q)‖^2) ≤
    50*((N:ℝ)+(Q:ℝ)^2)*(∑ n ∈ Finset.Ioc M (M+N), ‖a n‖^2) := by
  by_cases hQ : Q=0
  · subst Q; simp; positivity
  have hqp : 0<(Q:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ)
  have hb := separated_large_sieve (centers Q) RatCenter.val (sq_pos_of_pos hqp)
    (fun _ hc => (reduced_center_bound hc).1) (fun _ hc => (reduced_center_bound hc).2)
    (fun _ hc _ hd hne => reduced_center_sep hc hd hne) M N a
  simp only [RatCenter.val, ←mul_div_assoc] at hb
  rwa [sum_over_centers Q (fun q b => ‖∑ n ∈ Finset.Ioc M (M+N), a n*e ((n:ℝ)*b/q)‖^2)] at hb

end FareyGoldbach
