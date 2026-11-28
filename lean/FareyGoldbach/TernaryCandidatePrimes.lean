import FareyGoldbach.TernaryDefinitions
import FareyGoldbach.SmoothedTwistOfGRH
import FareyGoldbach.AveragedRemainder
import FareyGoldbach.SharpRankin

/-! # Prime candidates for the reflected ternary problem -/

open Real Complex Set MeasureTheory
open scoped BigOperators Classical

namespace FareyGoldbach

private noncomputable def candidateWeight (Y n : ℕ) : ℝ :=
  quarticBump ((n:ℝ)/Y)*primeWeight n

private noncomputable def candidateMass (Y r b : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ n%r=b), candidateWeight Y n

private noncomputable def candidateWindowMass (Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, quarticBump ((n:ℝ)/Y)

private lemma candidateWindowMass_lower {Y : ℕ} (hY : 1≤Y) :
    8*(Y:ℝ)/15-8 ≤ candidateWindowMass Y := by
  have h := principal_integral_sub_sum_le hY 0
  rw [mellin_scaledTiltedBump_eq hY,zero_mul,quarticKernel_zero_one,Complex.cpow_one] at h
  have he : e 0 = 1 := by simp [e]
  simp only [scaledTiltedBump,zero_mul,he,mul_one,abs_zero,add_zero] at h
  have hreal := (Complex.abs_re_le_norm _).trans h
  simp only [Complex.sub_re, Complex.re_sum, Complex.ofReal_re] at hreal
  have hv : (((Y:ℝ):ℂ)*(8/15:ℂ)).re = 8*(Y:ℝ)/15 := by norm_num; ring
  rw [hv] at hreal
  dsimp [candidateWindowMass]
  linarith [(abs_le.mp hreal).2]

private lemma norm_unitClassDiscrepancy_zero {r Y b : ℕ} (hb : b<r) [NeZero (r*1)] :
    ‖unitClassDiscrepancy r 1 Y 0 (b : ZMod (r*1))‖ =
      |candidateMass Y r b-candidateWindowMass Y/(r.totient:ℝ)| := by
  have he : e 0 = 1 := by simp [e]
  have hfilter : (Finset.Icc 1 Y).filter (fun n : ℕ ↦ (n:ZMod (r*1))=(b:ZMod (r*1))) =
      (Finset.Icc 1 Y).filter (fun n ↦ n%r=b) := by
    apply Finset.filter_congr; intro n _
    rw [ZMod.natCast_eq_natCast_iff',Nat.mul_one,Nat.mod_eq_of_lt hb]
  unfold unitClassDiscrepancy
  rw [hfilter]
  simp only [zero_div,zero_mul,he,mul_one]
  have hid : ((∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ n%r=b),
        (quarticBump ((n:ℝ)/Y):ℂ)*(primeWeight n:ℂ)) -
      1/(r.totient:ℂ) * ∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n:ℝ)/Y):ℂ)) =
      ((candidateMass Y r b-candidateWindowMass Y/(r.totient:ℝ):ℝ):ℂ) := by
    unfold candidateMass candidateWindowMass candidateWeight
    push_cast; ring
  rw [hid,Complex.norm_real,Real.norm_eq_abs]

private lemma primeCandidate_mass_upper {X r b : ℕ} (hX : 16≤X) :
    candidateMass (X/4) r b ≤ ((ternaryCandidatePrimes X r b).card:ℝ)*Real.log (2*(X:ℝ))+1 := by
  let Y := X/4
  let A := (Finset.Icc 1 Y).filter (fun n ↦ n%r=b)
  let P := ternaryCandidatePrimes X r b
  have hcut : candidateMass Y r b = ∑ n ∈ A.filter Nat.Prime, candidateWeight Y n := by
    change (∑ n∈A, candidateWeight Y n) = _
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    by_cases hp : n.Prime
    · simp [hp]
    · simp [hp,candidateWeight,primeWeight]
  have hsub : A.filter Nat.Prime ⊆ insert 2 P := by
    intro n hn
    obtain ⟨ha,hp⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn,hrb⟩ := Finset.mem_filter.mp ha
    by_cases h2 : n=2
    · simp [h2]
    · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨?_,(Finset.mem_Icc.mp hn).2⟩,hp,hrb⟩)
      have h := hp.two_le; omega
  have hn (n : ℕ) : 0≤candidateWeight Y n := mul_nonneg (quarticBump_nonneg _) (primeWeight_nonneg _)
  have hf (n : ℕ) : candidateWeight Y n ≤ primeWeight n :=
    mul_le_of_le_one_left (primeWeight_nonneg _) (quarticBump_le_one _)
  have h2 : 2∉P := by
    intro h
    have h' := (Finset.mem_filter.mp h).1
    have := (Finset.mem_Icc.mp h').1
    omega
  have hx : 0<(X:ℝ) := Nat.cast_pos.mpr (by omega)
  calc
    _ = _ := hcut
    _ ≤ ∑ n ∈ insert 2 P,candidateWeight Y n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ ↦ hn n
    _ = candidateWeight Y 2+∑ n∈P,candidateWeight Y n := Finset.sum_insert h2
    _ ≤ 1+∑ _n ∈ P, Real.log (2*(X:ℝ)) := by
      apply add_le_add
      · refine (hf 2).trans ?_
        simp only [primeWeight,ite_eq_left Nat.prime_two,Nat.cast_ofNat]
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
      · apply Finset.sum_le_sum; intro n h
        exact ((hf n).trans (primeWeight_le_log (show n≤X from
          (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).2.trans (Nat.div_le_self _ _)))).trans
          (Real.log_le_log hx (by linarith))
    _ = _ := by simp [P,nsmul_eq_mul]; ring

private lemma candidate_discrepancy_subset {r Y : ℕ} [NeZero (r*1)] (B : Finset ℕ)
    (hB : B ⊆ coprimeClasses r) :
    (∑ b∈B, |candidateMass Y r b-candidateWindowMass Y/(r.totient:ℝ)|^2) ≤
    ∑ u∈zmodUnitsFinset (r*1), ‖unitClassDiscrepancy r 1 Y 0 u‖^2 := by
  let f (b : ℕ) := (b:ZMod (r*1))
  have hi : Set.InjOn f B := by
    intro a ha b hb hab
    have h := (ZMod.natCast_eq_natCast_iff' a b (r*1)).1 hab
    simpa [Nat.mul_one,Nat.mod_eq_of_lt (mem_coprimeClasses.mp (hB ha)).1,
      Nat.mod_eq_of_lt (mem_coprimeClasses.mp (hB hb)).1] using h
  have hsub : B.image f ⊆ zmodUnitsFinset (r*1) := by
    intro u hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ZMod.isUnit_iff_coprime b _).2 ?_⟩
    simpa only [Nat.mul_one] using (mem_coprimeClasses.mp (hB hb)).2
  calc
    _ = ∑ b∈B, ‖unitClassDiscrepancy r 1 Y 0 (f b)‖^2 := Finset.sum_congr rfl fun b hb ↦ by
      rw [norm_unitClassDiscrepancy_zero (mem_coprimeClasses.mp (hB hb)).1]
    _ = ∑ u∈B.image f, ‖unitClassDiscrepancy r 1 Y 0 u‖^2 := by rw [Finset.sum_image hi]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ sq_nonneg _

/-- Among the reduced classes, only a bounded number have fewer candidate primes than
`X/(64 φ(r) log(2X))`. Each prime is odd and at most `⌊X/4⌋`. -/
theorem ternary_candidate_prime_variance_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {X r : ℕ}, 16≤X → 0<r → r≤X →
      (((coprimeClasses r).filter (fun b ↦ ((ternaryCandidatePrimes X r b).card:ℝ) <
        (X:ℝ)/(64*(r.totient:ℝ)*Real.log (2*(X:ℝ))))).card:ℝ) ≤
        C*(r.totient:ℝ)^2*Real.log (2*(X:ℝ))^2/(X:ℝ) := by
  obtain ⟨C,hC,hTw⟩ := smoothedTwistEstimate_of_dirichletGRH hGRH
  let P := (3*C+1)^2
  let A := 4096*(2*P+162)
  have hP : 0≤P := sq_nonneg _
  have hA : 8≤A := by dsimp [A]; linarith
  refine ⟨A,by linarith,?_⟩
  intro X r hX hr hrX
  let Y := X/4
  let L := Real.log (2*(X:ℝ))
  let φ := (r.totient:ℝ)
  let D := (X:ℝ)/(64*φ)
  let B := (coprimeClasses r).filter (fun b ↦ ((ternaryCandidatePrimes X r b).card:ℝ) <
    (X:ℝ)/(64*φ*L))
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hφ : 0<φ := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hφ1 : 1≤φ := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hr)
  have hY : 2≤Y := by dsimp [Y]; omega
  have hYp : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hYXn : Y≤X := Nat.div_le_self _ _
  have hYX : (Y:ℝ)≤X := Nat.cast_le.mpr hYXn
  have hL : 1≤L := one_le_log_two_mul (by omega)
  have hLp : 0<L := by linarith
  have hD : 0<D := by dsimp [D]; positivity
  have hBφ : (B.card:ℝ) ≤ φ := by
    have h := Finset.card_le_card (Finset.filter_subset (fun b ↦
      ((ternaryCandidatePrimes X r b).card:ℝ)<(X:ℝ)/(64*φ*L)) (coprimeClasses r))
    rw [card_coprimeClasses] at h; exact Nat.cast_le.mpr h
  change (B.card:ℝ)≤A*φ^2*L^2/(X:ℝ)
  by_cases hrY : r≤Y
  · let _ : NeZero (r*1) := ⟨by simpa using hr.ne'⟩
    have hdelta := sum_norm_sq_unitClassDiscrepancy_le hC hTw hr (by decide : 0<1) hrY
      (by omega : 1≤Y) hY (β:=0) (by norm_num)
    simp only [abs_zero,mul_zero,add_zero,mul_one] at hdelta
    have hsub := candidate_discrepancy_subset (Y:=Y) B (Finset.filter_subset _ _)
    have hlY : 0≤Real.log (2*(Y:ℝ)) := by linarith [one_le_log_two_mul hY]
    have hlog : Real.log (2*(Y:ℝ))≤L := Real.log_le_log (by positivity) (by linarith)
    have hsum : (∑ b∈B, |candidateMass Y r b-candidateWindowMass Y/φ|^2) ≤
        P*(X:ℝ)*L^2 := hsub.trans (hdelta.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hYX hP) (pow_le_pow_left₀ hlY hlog 2)
        (sq_nonneg _) (by positivity)))
    have hm : (X:ℝ)/32 ≤ candidateWindowMass Y+8 := by
      have hxy : X≤8*Y := by dsimp [Y]; omega
      have hh : (X:ℝ)≤8*(Y:ℝ) := by exact_mod_cast hxy
      linarith [candidateWindowMass_lower (by omega : 1≤Y)]
    have hm' : 2*D ≤ candidateWindowMass Y/φ+8 := by
      calc 2*D = ((X:ℝ)/32)/φ := by dsimp [D]; ring
           _ ≤ (candidateWindowMass Y+8)/φ := div_le_div_of_nonneg_right hm hφ.le
           _ ≤ _ := by rw [add_div]; linarith [(div_le_iff₀ hφ).2 (by linarith : 8≤8*φ)]
    have hbad b (hb : b∈B) :
        D^2 ≤ 2*|candidateMass Y r b-candidateWindowMass Y/φ|^2+162 := by
      have h := (Finset.mem_filter.mp hb).2
      change ((ternaryCandidatePrimes X r b).card:ℝ)<(X:ℝ)/(64*φ*L) at h
      rw [show (X:ℝ)/(64*φ*L)=D/L by dsimp [D]; ring] at h
      have h' := (lt_div_iff₀ hLp).1 h
      have hbnd := primeCandidate_mass_upper (r:=r) (b:=b) hX
      change candidateMass Y r b ≤ _ * L + 1 at hbnd
      let v := |candidateMass Y r b-candidateWindowMass Y/φ|
      have hDv : D≤v+9 := by
        dsimp [v]; linarith [neg_abs_le (candidateMass Y r b-candidateWindowMass Y/φ)]
      have hh := pow_le_pow_left₀ hD.le hDv 2
      change D^2 ≤ 2*v^2+162
      nlinarith [sq_nonneg (v-9)]
    have hcardX : (B.card:ℝ)≤X := hBφ.trans (Nat.cast_le.mpr ((Nat.totient_le r).trans hrX))
    have hlarge : 1≤L^2 := by nlinarith [sq_nonneg (L-1)]
    have hbgt : (B.card:ℝ)*D^2 ≤ (2*P+162)*(X:ℝ)*L^2 := by
      have hh := Finset.sum_le_sum hbad
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum] at hh
      have hxL := mul_le_mul_of_nonneg_left hlarge hx.le
      linarith
    refine ((le_div_iff₀ (sq_pos_of_pos hD)).2 hbgt).trans_eq ?_
    dsimp [D,A]; field_simp [hx.ne',hφ.ne']; ring
  · have hxr : X≤4*r := by dsimp [Y] at hrY; omega
    have hr' := (div_le_iff₀ hφ).1 (div_totient_le_two_log hr)
    have hrp : (0:ℝ)<r := Nat.cast_pos.mpr hr
    have hlr : Real.log (2*(r:ℝ))≤L :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hrX) (by norm_num))
    have hxr' : (X:ℝ)≤4*(r:ℝ) := by exact_mod_cast hxr
    have hxφ : (X:ℝ)≤8*φ*L := by
      have hh := mul_le_mul_of_nonneg_right hlr hφ.le
      linarith
    apply hBφ.trans
    apply (le_div_iff₀ hx).2
    have hh := mul_le_mul_of_nonneg_left hxφ hφ.le
    have h1 := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (L-1)] : L≤L^2) (sq_nonneg φ)
    have h2 := mul_le_mul_of_nonneg_right hA (mul_nonneg (sq_nonneg φ) (sq_nonneg L))
    nlinarith only [hh,h1,h2]

/-- Below the square-root modulus threshold, every reduced residual class contains
the required number of prime candidates. -/
theorem ternary_candidate_prime_lower_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ c : ℝ, 0<c ∧ ∀ {X r : ℕ}, 16≤X → 0<r → r≤X →
      (r.totient:ℝ) ≤ c*Real.sqrt (X:ℝ)/Real.log (2*(X:ℝ)) →
      ∀ b∈coprimeClasses r, (X:ℝ)/(64*(r.totient:ℝ)*Real.log (2*(X:ℝ))) ≤
        ((ternaryCandidatePrimes X r b).card:ℝ) := by
  obtain ⟨C,hC,hvar⟩ := ternary_candidate_prime_variance_of_dirichletGRH hGRH
  let c := 1/(C+1)
  have hc : 0<c := by dsimp [c]; positivity
  have hCc : C*c^2<1 := by
    dsimp [c]; rw [div_pow,one_pow,← div_eq_mul_one_div,div_lt_one (by positivity)]
    nlinarith [sq_nonneg C]
  refine ⟨c,hc,?_⟩
  intro X r hX hr hrX hφ b hb
  let L := Real.log (2*(X:ℝ))
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hL : 0<L := by have := one_le_log_two_mul (show 2≤X by omega); dsimp [L]; linarith
  have hφL := (le_div_iff₀ hL).1 hφ
  have hsq := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hL.le) hφL 2
  rw [mul_pow,mul_pow,Real.sq_sqrt hx.le] at hsq
  have hbudget : C*(r.totient:ℝ)^2*L^2/(X:ℝ)<1 := by
    refine lt_of_le_of_lt ((div_le_iff₀ hx).2 ?_) hCc
    have hh := mul_le_mul_of_nonneg_left hsq hC.le
    linarith
  by_contra! hbad
  let B := (coprimeClasses r).filter (fun b ↦ ((ternaryCandidatePrimes X r b).card:ℝ) <
    (X:ℝ)/(64*(r.totient:ℝ)*L))
  have hmem : b∈B := Finset.mem_filter.mpr ⟨hb,hbad⟩
  have hone : (1:ℝ)≤B.card := Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨b,hmem⟩)
  have hv := hvar hX hr hrX
  change (B.card:ℝ) ≤ C*(r.totient:ℝ)^2*L^2/(X:ℝ) at hv
  linarith

end FareyGoldbach
