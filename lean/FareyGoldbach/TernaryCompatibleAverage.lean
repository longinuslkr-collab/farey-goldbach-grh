import FareyGoldbach.TernaryCompatibleTriples
import FareyGoldbach.TernaryCandidatePrimes
import FareyGoldbach.TernaryProgressions

/-! # Failures at an odd target among all compatible triples of reduced classes -/

open Filter
open scoped BigOperators Classical Topology

namespace FareyGoldbach

/-- The failed compatible triples at a single target, with ordered residue classes. -/
noncomputable def ternaryBadTriples (r n : ℕ) :=
  (ternaryCompatibleTriples r n).filter (fun t =>
    ¬(ternaryRepresentations r t.1.1 t.2.1.1 t.2.2.1 n).Nonempty)

noncomputable def ternaryCompatibleAverageBudget (X r : ℕ) : ℝ :=
  let H := (X:ℝ)/r
  let κ := (r:ℝ)/r.totient
  let L := Real.log (2*(X:ℝ))
  L^2/H + L^4/(κ^2*Real.sqrt H)

private theorem reduced_eq_of_modEq {r : ℕ} {a b : ReducedClass r}
    (h : a.val ≡ b.val [MOD r]) : a=b := by
  apply Subtype.ext
  simpa [Nat.ModEq,Nat.mod_eq_of_lt (mem_coprimeClasses.mp a.2).1,
    Nat.mod_eq_of_lt (mem_coprimeClasses.mp b.2).1] using h
private theorem compatible_two_injections {r n : ℕ} :
    Set.InjOn (fun t : ReducedClass r × ReducedClass r × ReducedClass r => (t.1.1,t.2.1))
        (ternaryCompatibleTriples r n : Set _) ∧
      Set.InjOn (fun t : ReducedClass r × ReducedClass r × ReducedClass r => t.2)
        (ternaryCompatibleTriples r n : Set _) := by
  constructor
  · rintro ⟨a,b,c⟩ h ⟨d,e,f⟩ h' he
    obtain ⟨ha,hb⟩ := Prod.mk.inj he
    obtain rfl := Subtype.ext ha
    obtain rfl := hb
    have hmod := (Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp h').2
    have hh := Nat.ModEq.add_left_cancel' (a.val+b.val) (a:=c.val) (b:=f.val) (n:=r) hmod
    exact congrArg (fun z => (a,b,z)) (reduced_eq_of_modEq hh)
  · rintro ⟨a,b,c⟩ h ⟨d,e,f⟩ h' he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    have hmod := (Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp h').2
    have hh := Nat.ModEq.add_right_cancel' (b.val+c.val) (a:=a.val) (b:=d.val) (n:=r)
      (by simpa only [Nat.ModEq,Nat.add_assoc] using hmod)
    exact congrArg (fun z => (z,b,c)) (reduced_eq_of_modEq hh)

private theorem compatible_count_split {X r n : ℕ} (hr : 0<r)
    (hn : n∈Finset.Ioc (X/2) X) (hodd : Odd n) {T : ℝ} (hT : 0<T) :
    ((ternaryBadTriples r n).card:ℝ) ≤
      (((coprimeClasses r).filter fun b => ((ternaryCandidatePrimes X r b).card:ℝ)<T).card:ℝ)*(r.totient:ℝ) +
      (r.totient:ℝ)^2*doubleAvgExceptions X r hr/T := by
  let S := ternaryBadTriples r n
  let C := (coprimeClasses r).attach
  let D := (coprimeClasses r).filter fun b => ((ternaryCandidatePrimes X r b).card:ℝ)<T
  let P := fun t : ReducedClass r × ReducedClass r × ReducedClass r => t.1.val ∈ D
  let U := S.filter P
  let V := S.filter (fun t => ¬ P t)
  let f := fun t : ReducedClass r × ReducedClass r × ReducedClass r => t.2
  let E := fun v : ReducedClass r × ReducedClass r => ((exceptions (shortProgressions hr v.1 v.2) X).card:ℝ)
  have hS : S ⊆ ternaryCompatibleTriples r n := Finset.filter_subset _ _
  have hU : U.card ≤ D.card*r.totient := by
    have hi := compatible_two_injections (r:=r) (n:=n) |>.1
    have h := Finset.card_le_card_of_injOn (s:=U) (t:=D ×ˢ C) (fun t => (t.1.val,t.2.1))
      (fun t ht => Finset.mem_product.mpr ⟨(Finset.mem_filter.mp ht).2,Finset.mem_attach ..⟩)
      (fun _ hx _ hy hxy => hi (hS (Finset.mem_filter.mp hx).1) (hS (Finset.mem_filter.mp hy).1) hxy)
    simpa only [C,Finset.card_product,Finset.card_attach,card_coprimeClasses] using h
  have hV : (V.card:ℝ)*T ≤ (r.totient:ℝ)^2*doubleAvgExceptions X r hr := by
    have hg (t) (ht : t∈V) : T ≤ E (f t) := by
      obtain ⟨hb,hd⟩ := Finset.mem_filter.mp ht
      have hd' : T≤(ternaryCandidatePrimes X r t.1.val).card :=
        le_of_not_gt (fun hh => hd (Finset.mem_filter.mpr ⟨t.1.property,hh⟩))
      obtain ⟨hcomp,hbad⟩ := Finset.mem_filter.mp hb
      have ha : ternaryAdmissible r t.1.val t.2.1.val t.2.2.val n :=
        ⟨hodd,(Finset.mem_filter.mp hcomp).2⟩
      exact hd'.trans (Nat.cast_le.mpr (ternaryCandidate_card_le_exceptions hr t.1 t.2.1 t.2.2 hn ha hbad))
    have hi := compatible_two_injections (r:=r) (n:=n) |>.2
    have ht : V.image f ⊆ C ×ˢ C := by
      intro t ht
      exact Finset.mem_product.mpr ⟨Finset.mem_attach ..,Finset.mem_attach ..⟩
    calc _ = ∑ _t ∈ V,T := by simp
         _ ≤ ∑ t ∈ V,E (f t) := Finset.sum_le_sum hg
         _ = ∑ v ∈ V.image f,E v := (Finset.sum_image (fun _ hx _ hy hxy =>
           hi (hS (Finset.mem_filter.mp hx).1) (hS (Finset.mem_filter.mp hy).1) hxy)).symm
         _ ≤ ∑ v ∈ C ×ˢ C,E v := Finset.sum_le_sum_of_subset_of_nonneg ht (fun v _ _ => Nat.cast_nonneg _)
         _ = _ := by
           rw [Finset.sum_product]
           change _ = (r.totient:ℝ)^2*((1/(r.totient:ℝ)^2)*_)
           have hp : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
           field_simp
           rfl
  have hc : U.card+V.card=S.card := Finset.card_filter_add_card_filter_not P
  have hu : (U.card:ℝ)≤(D.card:ℝ)*(r.totient:ℝ) := by exact_mod_cast hU
  have hv := (le_div_iff₀ hT).mpr hV
  rw [show (ternaryBadTriples r n).card = U.card + V.card from hc.symm,Nat.cast_add]
  exact add_le_add hu hv

/-- Uniformity is in the individual odd target; only its compatible residue triples are averaged. -/
theorem ternary_compatible_bad_fraction_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {X r n : ℕ}, 16≤X → 0<r → r≤X → n∈Finset.Ioc (X/2) X → Odd n →
      ((ternaryBadTriples r n).card:ℝ)/((ternaryCompatibleTriples r n).card:ℝ) ≤
        C*ternaryCompatibleAverageBudget X r := by
  obtain ⟨A,hA,hvar⟩ := ternary_candidate_prime_variance_of_dirichletGRH hGRH
  obtain ⟨B,hB,hbin⟩ := double_average_of_dirichletGRH hGRH
  refine ⟨2*A+128*B,by positivity,?_⟩
  intro X r n hX hr hrX hn hodd
  let L := Real.log (2*(X:ℝ))
  let H := (X:ℝ)/r
  let φ := (r.totient:ℝ)
  let κ := (r:ℝ)/φ
  let T := (X:ℝ)/(64*φ*L)
  have hx : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have hφ : 0<φ := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hL : 0<L := zero_lt_one.trans_le (one_le_log_two_mul (by omega : 2≤X))
  have hH : 0<H := div_pos hx hr'
  have hκ : 0<κ := div_pos hr' hφ
  have hT : 0<T := by dsimp [T]; positivity
  have hJ : 0<Real.sqrt H := Real.sqrt_pos.mpr hH
  have N := ternaryCompatibleTriples_card_lower hr hodd
  let N₀ := (1/2:ℝ)*φ^3/r
  change N₀ ≤ _ at N
  have hN₀ : 0<N₀ := by dsimp [N₀]; positivity
  have cnt := compatible_count_split hr hn hodd hT
  have hd := mul_le_mul_of_nonneg_right (hvar hX hr hrX) hφ.le
  have hb := (hbin X r hr (by omega) hrX).trans (mul_le_mul_of_nonneg_left (min_le_right ..) hB.le)
  have hb' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (sq_nonneg φ)) hT.le
  have htotal := cnt.trans (add_le_add hd hb')
  let J₁ := L^2/H
  let J₂ := L^4/(κ^2*Real.sqrt H)
  have h₁ : 0≤J₁ := by dsimp [J₁]; positivity
  have h₂ : 0≤J₂ := by dsimp [J₂]; positivity
  apply (div_le_iff₀ (hN₀.trans_le N)).2
  change _ ≤ (2*A+128*B)*(J₁+J₂)*_
  refine htotal.trans <| le_trans ?_ (mul_le_mul_of_nonneg_left N (by positivity : 0≤(2*A+128*B)*(J₁+J₂)))
  have he₁ : (A*φ^2*L^2/(X:ℝ))*φ = 2*A*J₁*N₀ := by
    dsimp [J₁,N₀,H]; field_simp
  have he₂ : φ^2*(B*((φ/(r:ℝ))^2*Real.sqrt H*L^3))/T = 128*B*J₂*N₀ := by
    dsimp only [J₂,N₀,T,κ]
    field_simp
    have hrH : (r:ℝ)*H=(X:ℝ) := by dsimp [H]; field_simp
    rw [Real.sq_sqrt hH.le,hrH]; ring
  change (A*φ^2*L^2/(X:ℝ))*φ + φ^2*(B*((φ/(r:ℝ))^2*Real.sqrt H*L^3))/T ≤ _
  rw [he₁,he₂]
  nlinarith only [mul_nonneg (mul_nonneg hA.le h₂) hN₀.le,
    mul_nonneg (mul_nonneg hB.le h₁) hN₀.le]

theorem ternary_compatible_bad_density_zero_of_dirichletGRH (hGRH : DirichletGRH)
    (X r n : ℕ→ℕ) (hX : ∀ j,16≤X j) (hr : ∀ j,0<r j) (hrX : ∀ j,r j≤X j)
    (hn : ∀ j,n j∈Finset.Ioc (X j/2) (X j)) (hodd : ∀ j,Odd (n j))
    (hP : Tendsto (fun j => ternaryCompatibleAverageBudget (X j) (r j)) atTop (𝓝 0)) :
    Tendsto (fun j => ((ternaryBadTriples (r j) (n j)).card:ℝ)/
      ((ternaryCompatibleTriples (r j) (n j)).card:ℝ)) atTop (𝓝 0) := by
  obtain ⟨C,_,hb⟩ := ternary_compatible_bad_fraction_of_dirichletGRH hGRH
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hP.const_mul C)
  · exact Filter.Eventually.of_forall fun j => by positivity
  · exact Filter.Eventually.of_forall fun j => hb (hX j) (hr j) (hrX j) (hn j) (hodd j)

end FareyGoldbach
