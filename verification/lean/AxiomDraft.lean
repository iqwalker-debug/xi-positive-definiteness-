import Mathlib

/-! Candidate finite-sum interchange lemma (AXIOM-003, component 4).
The full divisor-inversion theorem is NOT claimed here. -/
open scoped BigOperators

variable {K D R : Type*} [CommSemiring R]

theorem axiom_finite_sum_swap
    (ks : Finset K) (ds : Finset D)
    (w : K → R) (g : D → R) (indicator : K → D → R) :
    (∑ k ∈ ks, w k * (∑ d ∈ ds, g d * indicator k d)) =
      ∑ d ∈ ds, g d * (∑ k ∈ ks, w k * indicator k d) := by
  classical
  calc
    _ = ∑ k ∈ ks, ∑ d ∈ ds, w k * (g d * indicator k d) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ = ∑ d ∈ ds, ∑ k ∈ ks, w k * (g d * indicator k d) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

#print axioms axiom_finite_sum_swap


/-! The algebraic core below assumes the divisor expansion rather than
proving Möbius inversion. No prime valuation or reindexing result is
assumed to have been formalized. -/

theorem axiom_weighted_expansion
    (ks : Finset K) (ds : Finset D)
    (w : K → R) (g : D → R) (f : K → R)
    (indicator : K → D → R)
    (hexpand : ∀ k ∈ ks, f k = ∑ d ∈ ds, g d * indicator k d) :
    (∑ k ∈ ks, w k * f k) =
      ∑ d ∈ ds, g d * (∑ k ∈ ks, w k * indicator k d) := by
  classical
  calc
    _ = ∑ k ∈ ks, w k * (∑ d ∈ ds, g d * indicator k d) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hexpand k hk]
    _ = _ := axiom_finite_sum_swap ks ds w g indicator

theorem axiom_dvd_gcd_iff (d n k s : ℕ) :
    d ∣ Nat.gcd n (k ^ s) ↔ d ∣ n ∧ d ∣ k ^ s := by
  constructor
  · intro h
    exact ⟨dvd_trans h (Nat.gcd_dvd_left _ _),
      dvd_trans h (Nat.gcd_dvd_right _ _)⟩
  · rintro ⟨hn, hk⟩
    exact Nat.dvd_gcd hn hk

theorem axiom_weighted_divisibility
    (ks : Finset ℕ) (ds : Finset D)
    (w : ℕ → R) (g : D → R) (f : ℕ → R) (q : D → ℕ)
    (hexpand : ∀ k ∈ ks, f k = ∑ d ∈ ds, if q d ∣ k then g d else 0) :
    (∑ k ∈ ks, w k * f k) =
      ∑ d ∈ ds, g d * (∑ k ∈ ks, if q d ∣ k then w k else 0) := by
  classical
  let indicator : ℕ → D → R := fun k d => if q d ∣ k then 1 else 0
  have he : ∀ k ∈ ks, f k = ∑ d ∈ ds, g d * indicator k d := by
    intro k hk
    rw [hexpand k hk]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : q d ∣ k <;> simp [indicator, h]
  calc
    _ = ∑ d ∈ ds, g d * (∑ k ∈ ks, w k * indicator k d) :=
      axiom_weighted_expansion ks ds w g f indicator he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      apply congrArg (fun z : R => g d * z)
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : q d ∣ k <;> simp [indicator, h]

#print axioms axiom_weighted_expansion
#print axioms axiom_dvd_gcd_iff
#print axioms axiom_weighted_divisibility


namespace GenesisFormalV2

section Mobius
variable {A : Type*} [AddCommGroup A]

/-- Möbius transform via the divisor antidiagonal. Mathlib supplies
the one-dimensional inversion theorem. -/
noncomputable def mobiusTransform (f : ℕ → A) (n : ℕ) : A :=
  ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 • f x.2

theorem mobius_expand (f : ℕ → A) (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, mobiusTransform f d) = f n := by
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (f := mobiusTransform f) (g := f)).2
  · intro k hk
    rfl
  · exact hn

/-- Iterated transform, allowing nonseparable functions. -/
noncomputable def mobiusTransform₂ (f : ℕ → ℕ → A) (a b : ℕ) : A :=
  mobiusTransform (fun y => mobiusTransform (fun x => f x y) a) b

theorem mobius_expand₂ (f : ℕ → ℕ → A) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    (∑ d ∈ a.divisors, ∑ e ∈ b.divisors, mobiusTransform₂ f d e) = f a b := by
  calc
    _ = ∑ d ∈ a.divisors, mobiusTransform (fun x => f x b) d := by
      apply Finset.sum_congr rfl
      intro d hd
      exact mobius_expand (fun y => mobiusTransform (fun x => f x y) d) b hb
    _ = _ := mobius_expand (fun x => f x b) a ha
end Mobius

def ceilExp (s a : ℕ) : ℕ := (a + s - 1) / s

theorem ceilExp_zero (s : ℕ) : ceilExp s 0 = 0 := by
  unfold ceilExp
  simp only [zero_add]
  by_cases h : s = 0
  · simp [h]
  · apply Nat.div_eq_of_lt
    omega

theorem ceilExp_le_iff (s a b : ℕ) (hs : 0 < s) :
    ceilExp s a ≤ b ↔ a ≤ s * b := by
  exact (Nat.le_mul_iff_le_right hs).symm

noncomputable def rootFactors (s d : ℕ) : ℕ →₀ ℕ :=
  d.factorization.mapRange (ceilExp s) (ceilExp_zero s)

theorem rootFactors_prime (s d : ℕ) :
    ∀ p ∈ (rootFactors s d).support, Nat.Prime p := by
  intro p hp
  have hsub : (rootFactors s d).support ⊆ d.factorization.support :=
    Finsupp.support_mapRange
  exact Nat.prime_of_mem_primeFactors (by simpa using hsub hp)

/-- The positive integer with prime valuations ceil(v_p(d)/s). -/
noncomputable def powerRoot (s d : ℕ) : ℕ :=
  ↑(Nat.factorizationEquiv.symm ⟨rootFactors s d, rootFactors_prime s d⟩)

theorem powerRoot_ne_zero (s d : ℕ) : powerRoot s d ≠ 0 := by
  exact PNat.ne_zero _

theorem powerRoot_factorization (s d : ℕ) :
    (powerRoot s d).factorization = rootFactors s d := by
  let a : { f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p } :=
    ⟨rootFactors s d, rootFactors_prime s d⟩
  change (↑(Nat.factorizationEquiv.symm a) : ℕ).factorization = a.val
  exact congrArg Subtype.val (Nat.factorizationEquiv.apply_symm_apply a)

theorem powerRoot_dvd_iff (s d k : ℕ) (hs : 0 < s) (hd : d ≠ 0)
    (hk : k ≠ 0) : powerRoot s d ∣ k ↔ d ∣ k ^ s := by
  rw [← Nat.factorization_prime_le_iff_dvd (powerRoot_ne_zero s d) hk,
    ← Nat.factorization_prime_le_iff_dvd hd (pow_ne_zero s hk)]
  simp only [powerRoot_factorization, rootFactors, Finsupp.mapRange_apply,
    Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul]
  exact forall_congr' (fun p => forall_congr' (fun _ =>
    ceilExp_le_iff s (d.factorization p) (k.factorization p) hs))

/-- Joint prime-power constraints collapse into a single LCM. -/
noncomputable def jointRoot {I : Type*} [Fintype I] (s d : I → ℕ) : ℕ :=
  Finset.univ.lcm (fun i => powerRoot (s i) (d i))

theorem jointRoot_dvd_iff {I : Type*} [Fintype I]
    (s d : I → ℕ) (k : ℕ) (hs : ∀ i, 0 < s i)
    (hd : ∀ i, d i ≠ 0) (hk : k ≠ 0) :
    jointRoot s d ∣ k ↔ ∀ i, d i ∣ k ^ s i := by
  classical
  simp only [jointRoot, Finset.lcm_dvd_iff, Finset.mem_univ, true_implies]
  exact forall_congr' (fun i => powerRoot_dvd_iff (s i) (d i) k (hs i) (hd i) hk)

section Weighted
variable {A : Type*} [CommRing A]

/-- The divisor expansion at a power-GCD. -/
theorem gcd_expansion (f : ℕ → A) (n s k : ℕ)
    (hn : n ≠ 0) (hs : 0 < s) (hk : k ≠ 0) :
    f (Nat.gcd n (k^s)) =
      ∑ d ∈ n.divisors, if powerRoot s d ∣ k then mobiusTransform f d else 0 := by
  classical
  have hg : Nat.gcd n (k^s) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hn (Nat.gcd_dvd_left _ _)
  have hf : (n.divisors.filter (fun d => powerRoot s d ∣ k)) =
      (Nat.gcd n (k^s)).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, hroot⟩
      have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
      exact ⟨Nat.dvd_gcd hd ((powerRoot_dvd_iff s d k hs hd0 hk).mp hroot), hg⟩
    · rintro ⟨hd, _⟩
      have hdn := dvd_trans hd (Nat.gcd_dvd_left n (k^s))
      have hdk := dvd_trans hd (Nat.gcd_dvd_right n (k^s))
      exact ⟨⟨hdn, hn⟩,
        (powerRoot_dvd_iff s d k hs (ne_zero_of_dvd_ne_zero hn hdn) hk).mpr hdk⟩
  rw [← Finset.sum_filter, hf]
  exact (mobius_expand f _ (Nat.pos_of_ne_zero hg)).symm

/-- Complete one-coordinate weighted transform, with arbitrary finite
positive index set and arbitrary ring-valued weights. The inner sum
is over divisibility indicators rather than reindexed multiples. -/
theorem weighted_power_gcd (ks : Finset ℕ) (w f : ℕ → A)
    (n s : ℕ) (hn : n ≠ 0) (hs : 0 < s)
    (hk : ∀ k ∈ ks, k ≠ 0) :
    (∑ k ∈ ks, w k * f (Nat.gcd n (k^s))) =
      ∑ d ∈ n.divisors, mobiusTransform f d *
        (∑ k ∈ ks, if powerRoot s d ∣ k then w k else 0) := by
  classical
  exact axiom_weighted_divisibility ks n.divisors w (mobiusTransform f)
    (fun k => f (Nat.gcd n (k^s))) (powerRoot s)
    (fun k h => gcd_expansion f n s k hn hs (hk k h))
end Weighted

#print axioms mobius_expand
#print axioms mobius_expand₂
#print axioms ceilExp_zero
#print axioms ceilExp_le_iff
#print axioms rootFactors_prime
#print axioms powerRoot_ne_zero
#print axioms powerRoot_factorization
#print axioms powerRoot_dvd_iff
#print axioms jointRoot_dvd_iff
#print axioms gcd_expansion
#print axioms weighted_power_gcd
end GenesisFormalV2


/-! FORMAL v3: arbitrary finite coordinate count and bounded multiples.
The proof candidate must pass the Lean kernel before being classified as verified. -/
namespace GenesisFormalV3
open GenesisFormalV2
open scoped BigOperators

section Cartesian
variable {A : Type*} [AddCommMonoid A]

theorem sum_pi_cons {m : ℕ} (S : Fin (m+1) → Finset ℕ)
    (f : (Fin (m+1) → ℕ) → A) :
    (∑ d ∈ Fintype.piFinset S, f d) =
      ∑ a ∈ S 0, ∑ t ∈ Fintype.piFinset (Fin.tail S), f (Fin.cons a t) := by
  classical
  have h : Fintype.piFinset S =
      ((S 0).product (Fintype.piFinset (Fin.tail S))).map
        (Fin.consEquiv (fun _ : Fin (m+1) => ℕ)).toEmbedding := by
    simpa using (Finset.filter_piFinset_eq_map_consEquiv S
      (fun _ : Fin m → ℕ => True))
  rw [h, Finset.sum_map, Finset.product_eq_sprod]
  exact Finset.sum_product' (S 0) (Fintype.piFinset (Fin.tail S))
    (fun a t => f (Fin.cons a t))
end Cartesian

section Mobius
variable {A : Type*} [AddCommGroup A]

/-- Iterated coordinatewise Möbius inversion; zero coordinates are the identity. -/
noncomputable def mobiusN : (m : ℕ) → ((Fin m → ℕ) → A) → (Fin m → ℕ) → A
  | 0, f, d => f d
  | m+1, f, d =>
    mobiusTransform (fun a => mobiusN m (fun t => f (Fin.cons a t)) (Fin.tail d)) (d 0)

theorem mobiusN_expand (m : ℕ) (f : (Fin m → ℕ) → A)
    (n : Fin m → ℕ) (hn : ∀ i, 0 < n i) :
    (∑ d ∈ Fintype.piFinset (fun i => (n i).divisors), mobiusN m f d) = f n := by
  classical
  induction m with
  | zero =>
    have h : Fintype.piFinset (fun i => (n i).divisors) = {n} := by
      ext d
      have hd : d = n := Subsingleton.elim _ _
      subst d
      simp <;> exact Subsingleton.elim _ _
    rw [h, Finset.sum_singleton]
    rfl
  | succ m ih =>
    rw [sum_pi_cons]
    simp only [mobiusN, Fin.cons_zero, Fin.tail_def]
    rw [Finset.sum_comm]
    calc
      _ = ∑ t ∈ Fintype.piFinset (fun i => (n i.succ).divisors),
          mobiusN m (fun u => f (Fin.cons (n 0) u)) t := by
        apply Finset.sum_congr rfl
        intro t ht
        exact mobius_expand (fun a => mobiusN m (fun u => f (Fin.cons a u)) t)
          (n 0) (hn 0)
      _ = f n := by
        rw [ih (fun u => f (Fin.cons (n 0) u)) (fun i => n i.succ)
          (fun i => hn i.succ)]
        change f (Fin.cons (n 0) (Fin.tail n)) = f n
        rw [Fin.cons_self_tail]
end Mobius

theorem jointRoot_ne_zero {I : Type*} [Fintype I] (s d : I → ℕ) :
    jointRoot s d ≠ 0 := by
  classical
  have hp : (∏ i, powerRoot (s i) (d i)) ≠ 0 := by
    simp [Finset.prod_ne_zero_iff, powerRoot_ne_zero]
  have hd : jointRoot s d ∣ ∏ i, powerRoot (s i) (d i) := by
    unfold jointRoot
    rw [Finset.lcm_dvd_iff]
    intro i hi
    exact Finset.dvd_prod_of_mem (fun j => powerRoot (s j) (d j)) hi
  exact ne_zero_of_dvd_ne_zero hp hd

section Weighted
variable {A : Type*} [CommRing A]

theorem gcdN_expansion (m : ℕ) (f : (Fin m → ℕ) → A)
    (n s : Fin m → ℕ) (k : ℕ)
    (hn : ∀ i, n i ≠ 0) (hs : ∀ i, 0 < s i) (hk : k ≠ 0) :
    f (fun i => Nat.gcd (n i) (k ^ s i)) =
      ∑ d ∈ Fintype.piFinset (fun i => (n i).divisors),
        if jointRoot s d ∣ k then mobiusN m f d else 0 := by
  classical
  let G : Fin m → ℕ := fun i => Nat.gcd (n i) (k ^ s i)
  have hg : ∀ i, G i ≠ 0 := fun i =>
    ne_zero_of_dvd_ne_zero (hn i) (Nat.gcd_dvd_left _ _)
  have hf : (Fintype.piFinset (fun i => (n i).divisors)).filter
      (fun d => jointRoot s d ∣ k) =
        Fintype.piFinset (fun i => (G i).divisors) := by
    ext d
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, hq⟩
      have hd0 : ∀ i, d i ≠ 0 := fun i =>
        ne_zero_of_dvd_ne_zero (hn i) (hd i).1
      have hpow := (jointRoot_dvd_iff s d k hs hd0 hk).mp hq
      intro i
      exact ⟨Nat.dvd_gcd (hd i).1 (hpow i), hg i⟩
    · intro hd
      have hdn : ∀ i, d i ∣ n i := fun i =>
        dvd_trans (hd i).1 (Nat.gcd_dvd_left _ _)
      have hdk : ∀ i, d i ∣ k ^ s i := fun i =>
        dvd_trans (hd i).1 (Nat.gcd_dvd_right _ _)
      have hd0 : ∀ i, d i ≠ 0 := fun i =>
        ne_zero_of_dvd_ne_zero (hn i) (hdn i)
      exact ⟨fun i => ⟨hdn i, hn i⟩,
        (jointRoot_dvd_iff s d k hs hd0 hk).mpr hdk⟩
  rw [← Finset.sum_filter, hf]
  exact (mobiusN_expand m f G (fun i => Nat.pos_of_ne_zero (hg i))).symm

/-- Weighted joint transformation for any finite set of positive indices. -/
theorem weighted_joint_gcd (m : ℕ) (ks : Finset ℕ)
    (w : ℕ → A) (f : (Fin m → ℕ) → A) (n s : Fin m → ℕ)
    (hn : ∀ i, n i ≠ 0) (hs : ∀ i, 0 < s i)
    (hk : ∀ k ∈ ks, k ≠ 0) :
    (∑ k ∈ ks, w k * f (fun i => Nat.gcd (n i) (k ^ s i))) =
      ∑ d ∈ Fintype.piFinset (fun i => (n i).divisors), mobiusN m f d *
        (∑ k ∈ ks, if jointRoot s d ∣ k then w k else 0) := by
  classical
  exact axiom_weighted_divisibility ks _ w (mobiusN m f)
    (fun k => f (fun i => Nat.gcd (n i) (k ^ s i))) (jointRoot s)
    (fun k h => gcdN_expansion m f n s k hn hs (hk k h))

/-- Explicit reindexing of positive multiples, including empty ranges. -/
theorem sum_multiples (w : ℕ → A) (N q : ℕ) (hq : 0 < q) :
    (∑ k ∈ Finset.Icc 1 N, if q ∣ k then w k else 0) =
      ∑ j ∈ Finset.Icc 1 (N / q), w (j*q) := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun j _ => j*q) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hpos : 0 < j*q := Nat.mul_pos (by omega) hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, (Nat.le_div_iff_mul_le hq).mp hj'.2⟩,
        ⟨j, Nat.mul_comm j q⟩⟩
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_right hq hab
  · intro k hk
    obtain ⟨hk', hd⟩ := Finset.mem_filter.mp hk
    have hk'' := Finset.mem_Icc.mp hk'
    obtain ⟨j, hj⟩ := hd
    have hj0 : j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hj
      omega
    have hjle : j*q ≤ N := by
      rw [Nat.mul_comm j q, ← hj]
      exact hk''.2
    exact ⟨j, Finset.mem_Icc.mpr
      ⟨by omega, (Nat.le_div_iff_mul_le hq).mpr hjle⟩, by rw [Nat.mul_comm j q, ← hj]⟩
  · intro j hj
    rfl

/-- Full bounded joint weighted GCD identity with iterated Möbius coefficients. -/
theorem weighted_joint_gcd_bounded (m N : ℕ) (w : ℕ → A)
    (f : (Fin m → ℕ) → A) (n s : Fin m → ℕ)
    (hn : ∀ i, n i ≠ 0) (hs : ∀ i, 0 < s i) :
    (∑ k ∈ Finset.Icc 1 N, w k * f (fun i => Nat.gcd (n i) (k ^ s i))) =
      ∑ d ∈ Fintype.piFinset (fun i => (n i).divisors), mobiusN m f d *
        (∑ j ∈ Finset.Icc 1 (N / jointRoot s d), w (j * jointRoot s d)) := by
  classical
  rw [weighted_joint_gcd m (Finset.Icc 1 N) w f n s hn hs
    (fun k hk => by have h := Finset.mem_Icc.mp hk; omega)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_multiples w N (jointRoot s d) (Nat.pos_of_ne_zero (jointRoot_ne_zero s d))]
end Weighted

#print axioms sum_pi_cons
#print axioms mobiusN_expand
#print axioms jointRoot_ne_zero
#print axioms gcdN_expansion
#print axioms weighted_joint_gcd
#print axioms sum_multiples
#print axioms weighted_joint_gcd_bounded
end GenesisFormalV3


/-! FORMAL v4 — closed AXIOM coefficients and the algebraic foundations of
radial positive definiteness and Stieltjes moment obstructions.

These declarations are proof candidates until the hosted Lean run succeeds.
The xi-specific Fourier recurrence, measure representation and certificate
integration are deliberately not assumed or claimed as proved here. -/
namespace GenesisFormalV4
open GenesisFormalV2 GenesisFormalV3
open scoped BigOperators

section ClosedMobius
variable {A : Type*} [AddCommGroup A]

theorem mobiusTransform_closed (f : ℕ → A) (n : ℕ) :
    mobiusTransform f n =
      ∑ e ∈ n.divisors, ArithmeticFunction.moebius (n / e) • f e := by
  classical
  unfold mobiusTransform
  rw [← Nat.map_div_left_divisors, Finset.sum_map]
  rfl

/-- Product-of-Möbius-coefficients representation, including zero coordinates. -/
theorem mobiusN_closed (m : ℕ) (f : (Fin m → ℕ) → A)
    (d : Fin m → ℕ) :
    mobiusN m f d =
      ∑ e ∈ Fintype.piFinset (fun i => (d i).divisors),
        (∏ i, ArithmeticFunction.moebius (d i / e i)) • f e := by
  classical
  induction m with
  | zero =>
    have h : Fintype.piFinset (fun i => (d i).divisors) = {d} := by
      ext e
      have he : e = d := Subsingleton.elim _ _
      subst e
      simp <;> exact Subsingleton.elim _ _
    rw [h, Finset.sum_singleton]
    simp [mobiusN]
  | succ m ih =>
    rw [mobiusN, mobiusTransform_closed, sum_pi_cons]
    apply Finset.sum_congr rfl
    intro e he
    rw [ih (fun t => f (Fin.cons e t)) (Fin.tail d)]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail_def]
    rw [mul_smul]
end ClosedMobius

section ClosedWeighted
variable {A : Type*} [CommRing A]

/-- The bounded AXIOM identity with explicit, rather than recursive, coefficients. -/
theorem weighted_joint_gcd_closed (m N : ℕ) (w : ℕ → A)
    (f : (Fin m → ℕ) → A) (n s : Fin m → ℕ)
    (hn : ∀ i, n i ≠ 0) (hs : ∀ i, 0 < s i) :
    (∑ k ∈ Finset.Icc 1 N, w k * f (fun i => Nat.gcd (n i) (k ^ s i))) =
      ∑ d ∈ Fintype.piFinset (fun i => (n i).divisors),
        (∑ e ∈ Fintype.piFinset (fun i => (d i).divisors),
          (∏ i, ArithmeticFunction.moebius (d i / e i)) • f e) *
        (∑ j ∈ Finset.Icc 1 (N / jointRoot s d), w (j * jointRoot s d)) := by
  classical
  rw [weighted_joint_gcd_bounded m N w f n s hn hs]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mobiusN_closed]
end ClosedWeighted

section Kernels
/-- Real positive semidefiniteness of every finite kernel Gram matrix. -/
def KernelPSD {X : Type*} (K : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (xs : Fin n → X) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * K (xs i) (xs j)

theorem kernelPSD_pullback {X Y : Type*} (K : Y → Y → ℝ)
    (hK : KernelPSD K) (e : X → Y) :
    KernelPSD (fun x y => K (e x) (e y)) := by
  intro n xs c
  exact hK n (fun i => e (xs i)) c

theorem kernelPSD_negative_witness {X : Type*} (K : X → X → ℝ)
    (n : ℕ) (xs : Fin n → X) (c : Fin n → ℝ)
    (h : (∑ i, ∑ j, c i * c j * K (xs i) (xs j)) < 0) :
    ¬ KernelPSD K := by
  intro hp
  exact (not_lt_of_ge (hp n xs c)) h

def RadialPSD (X : Type*) [PseudoMetricSpace X] (F : ℝ → ℝ) : Prop :=
  KernelPSD (fun x y : X => F (dist x y))

/-- Restriction along a distance-preserving map. -/
theorem radialPSD_restrict {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℝ → ℝ) (e : X → Y)
    (he : ∀ x y, dist (e x) (e y) = dist x y)
    (h : RadialPSD Y F) : RadialPSD X F := by
  intro n xs c
  have h' := h n (fun i => e (xs i)) c
  simpa only [he] using h'

/-- An obstruction in a subspace obstructs every distance-preserving extension. -/
theorem radialPSD_obstruction_extend {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℝ → ℝ) (e : X → Y)
    (he : ∀ x y, dist (e x) (e y) = dist x y)
    (h : ¬ RadialPSD X F) : ¬ RadialPSD Y F := by
  intro hy
  exact h (radialPSD_restrict F e he hy)
end Kernels

section Hankel
/-- Algebraic expansion of a polynomial square with an arbitrary moment shift. -/
theorem hankel_square {R : Type*} [CommRing R] {n : ℕ}
    (c : Fin n → R) (x : R) (shift : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n, c i * c j * x ^ (i.val + j.val + shift)) =
      x ^ shift * (∑ i : Fin n, c i * x ^ i.val)^2 := by
  classical
  let a : Fin n → R := fun i => c i * x ^ i.val
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, x ^ shift * (a i * a j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [a, pow_add]
      ring
    _ = ∑ i : Fin n, x ^ shift * (a i * ∑ j : Fin n, a j) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mul_sum]
    _ = _ := by
      change (∑ i : Fin n, x ^ shift * (a i * ∑ j : Fin n, a j)) =
        x ^ shift * (∑ i : Fin n, a i)^2
      rw [← Finset.mul_sum, ← Finset.sum_mul, pow_two]

noncomputable def MomentSequence (L : Polynomial ℝ →ₗ[ℝ] ℝ) (k : ℕ) : ℝ :=
  L (Polynomial.X ^ k)

/-- Positive on polynomials nonnegative on the nonnegative half-line.
This is an abstract hypothesis, not an assumed construction of the xi measure. -/
def StieltjesPositive (L : Polynomial ℝ →ₗ[ℝ] ℝ) : Prop :=
  ∀ p : Polynomial ℝ, (∀ x : ℝ, 0 ≤ x → 0 ≤ p.eval x) → 0 ≤ L p

def HankelForm {n : ℕ} (b : ℕ → ℝ) (shift : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, c i * c j * b (i.val + j.val + shift)

theorem hankel_form_eq {n : ℕ} (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (shift : ℕ) (c : Fin n → ℝ) :
    HankelForm (MomentSequence L) shift c =
      L (Polynomial.X ^ shift *
        (∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ i.val)^2) := by
  classical
  unfold HankelForm MomentSequence
  rw [← hankel_square (fun i : Fin n => Polynomial.C (c i))
    (Polynomial.X : Polynomial ℝ) shift]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Polynomial.C_mul, Polynomial.C_mul', map_smul, smul_eq_mul]

/-- Every shifted Hankel form is nonnegative under a positive Stieltjes functional. -/
theorem hankel_nonneg {n : ℕ} (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hL : StieltjesPositive L) (shift : ℕ) (c : Fin n → ℝ) :
    0 ≤ HankelForm (MomentSequence L) shift c := by
  rw [hankel_form_eq]
  apply hL
  intro x hx
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_nonneg (pow_nonneg hx _) (sq_nonneg _)

/-- A strict negative Hankel witness rules out a positive Stieltjes functional
having the specified moments. -/
theorem hankel_negative_witness {n : ℕ} (b : ℕ → ℝ)
    (shift : ℕ) (c : Fin n → ℝ) (h : HankelForm b shift c < 0) :
    ¬ ∃ L : Polynomial ℝ →ₗ[ℝ] ℝ,
        StieltjesPositive L ∧ MomentSequence L = b := by
  rintro ⟨L, hL, hb⟩
  have hn := hankel_nonneg L hL shift c
  rw [hb] at hn
  exact (not_lt_of_ge hn) h
end Hankel

#print axioms mobiusTransform_closed
#print axioms mobiusN_closed
#print axioms weighted_joint_gcd_closed
#print axioms kernelPSD_pullback
#print axioms kernelPSD_negative_witness
#print axioms radialPSD_restrict
#print axioms radialPSD_obstruction_extend
#print axioms hankel_square
#print axioms hankel_form_eq
#print axioms hankel_nonneg
#print axioms hankel_negative_witness
end GenesisFormalV4


/-! FORMAL v5: measure-to-moment bridge, positive mixtures, Euclidean
dimension restriction, and the algebra of spherical moments.
The spherical recurrence and xi-specific measure representation remain
explicit proof obligations; they are not asserted as axioms. -/
namespace GenesisFormalV5
open GenesisFormalV4
open MeasureTheory
open scoped BigOperators

section Measures

/-- Integration of polynomials gives a linear functional whenever all
polynomial evaluations are integrable. -/
noncomputable def integralFunctional (μ : Measure ℝ)
    (hint : ∀ p : Polynomial ℝ, Integrable (fun x => p.eval x) μ) :
    Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x ∂μ
  map_add' p q := by
    simp only [Polynomial.eval_add]
    exact integral_add (hint p) (hint q)
  map_smul' a p := by
    simp only [RingHom.id_apply, Polynomial.eval_smul, smul_eq_mul]
    exact integral_const_mul a (fun x => p.eval x)

theorem integralFunctional_positive (μ : Measure ℝ)
    (hint : ∀ p : Polynomial ℝ, Integrable (fun x => p.eval x) μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) :
    StieltjesPositive (integralFunctional μ hint) := by
  intro p hp
  change 0 ≤ ∫ x, p.eval x ∂μ
  apply integral_nonneg_of_ae
  filter_upwards [hpos] with x hx
  exact hp x hx

theorem integralFunctional_moment (μ : Measure ℝ)
    (hint : ∀ p : Polynomial ℝ, Integrable (fun x => p.eval x) μ)
    (k : ℕ) :
    MomentSequence (integralFunctional μ hint) k = ∫ x, x ^ k ∂μ := by
  change (∫ x, (Polynomial.X ^ k : Polynomial ℝ).eval x ∂μ) = _
  simp only [Polynomial.eval_pow, Polynomial.eval_X]

/-- Genuine measure representation implies every shifted Hankel inequality. -/
theorem measure_hankel_nonneg (μ : Measure ℝ)
    (hint : ∀ p : Polynomial ℝ, Integrable (fun x => p.eval x) μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) {n : ℕ} (shift : ℕ) (c : Fin n → ℝ) :
    0 ≤ HankelForm (fun k => ∫ x, x ^ k ∂μ) shift c := by
  have h := hankel_nonneg (integralFunctional μ hint)
    (integralFunctional_positive μ hint hpos) shift c
  have he : MomentSequence (integralFunctional μ hint) =
      (fun k => ∫ x, x ^ k ∂μ) := funext (integralFunctional_moment μ hint)
  rw [he] at h
  exact h

theorem measure_hankel_obstruction (b : ℕ → ℝ) {n : ℕ}
    (shift : ℕ) (c : Fin n → ℝ) (hneg : HankelForm b shift c < 0) :
    ¬ ∃ μ : Measure ℝ,
      (∀ p : Polynomial ℝ, Integrable (fun x => p.eval x) μ) ∧
      (∀ᵐ x ∂μ, 0 ≤ x) ∧ (∀ k, b k = ∫ x, x ^ k ∂μ) := by
  rintro ⟨μ, hint, hpos, hb⟩
  have he : b = fun k => ∫ x, x ^ k ∂μ := funext hb
  rw [he] at hneg
  exact (not_lt_of_ge (measure_hankel_nonneg μ hint hpos shift c)) hneg

/-- Integration preserves positivity of kernels, provided each entry is
integrable. No claim of the converse direction of Bochner is made here. -/
theorem kernelPSD_integral {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : T → X → X → ℝ)
    (hK : ∀ᵐ t ∂μ, KernelPSD (K t))
    (hint : ∀ x y, Integrable (fun t => K t x y) μ) :
    KernelPSD (fun x y => ∫ t, K t x y ∂μ) := by
  classical
  intro n xs c
  let g : Fin n → Fin n → T → ℝ :=
    fun i j t => (c i * c j) * K t (xs i) (xs j)
  have hg : ∀ i j, Integrable (g i j) μ := fun i j =>
    (hint (xs i) (xs j)).const_mul (c i * c j)
  have hi : ∀ i, Integrable (fun t => ∑ j : Fin n, g i j t) μ := by
    intro i
    exact integrable_finsetSum Finset.univ (fun j _ => hg i j)
  have he :
      (∫ t, ∑ i : Fin n, ∑ j : Fin n, g i j t ∂μ) =
        ∑ i : Fin n, ∑ j : Fin n, c i * c j *
          (∫ t, K t (xs i) (xs j) ∂μ) := by
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i hi'
    rw [integral_finsetSum Finset.univ (fun j _ => hg i j)]
    apply Finset.sum_congr rfl
    intro j hj
    exact integral_const_mul _ _
  rw [← he]
  apply integral_nonneg_of_ae
  filter_upwards [hK] with t ht
  exact ht n xs c

end Measures

section FourierKernels

theorem rankOne_quadratic {n : ℕ} (a c : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, c i * c j * (a i * a j)) =
      (∑ i : Fin n, c i * a i)^2 := by
  classical
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, (c i * a i) * (c j * a j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, pow_two]

/-- A cosine of a difference is PSD, independently of the space of phases. -/
theorem cosine_kernelPSD {X : Type*} (phase : X → ℝ) :
    KernelPSD (fun x y => Real.cos (phase x - phase y)) := by
  classical
  intro n xs c
  have h :
      (∑ i : Fin n, ∑ j : Fin n, c i * c j *
        Real.cos (phase (xs i) - phase (xs j))) =
      (∑ i : Fin n, c i * Real.cos (phase (xs i)))^2 +
      (∑ i : Fin n, c i * Real.sin (phase (xs i)))^2 := by
    simp only [Real.cos_sub, mul_add, Finset.sum_add_distrib,
      rankOne_quadratic]
  rw [h]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The sufficient Fourier/Bochner direction: a real cosine mixture
with positive measure is a PSD kernel when its entries are integrable. -/
theorem cosine_mixturePSD {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (phase : T → X → ℝ)
    (hint : ∀ x y,
      Integrable (fun t => Real.cos (phase t x - phase t y)) μ) :
    KernelPSD (fun x y => ∫ t, Real.cos (phase t x - phase t y) ∂μ) := by
  apply kernelPSD_integral μ _ _ hint
  exact Filter.Eventually.of_forall (fun t => cosine_kernelPSD (phase t))

end FourierKernels

section Dimensions

noncomputable def euclideanPad (d : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (d+1)) :=
  WithLp.toLp 2 (Fin.cons 0 x.ofLp)

theorem euclideanPad_dist (d : ℕ) (x y : EuclideanSpace ℝ (Fin d)) :
    dist (euclideanPad d x) (euclideanPad d y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  simp [euclideanPad, Fin.sum_univ_succ]

theorem euclideanPSD_step (F : ℝ → ℝ) (d : ℕ)
    (h : RadialPSD (EuclideanSpace ℝ (Fin (d+1))) F) :
    RadialPSD (EuclideanSpace ℝ (Fin d)) F :=
  radialPSD_restrict F (euclideanPad d) (euclideanPad_dist d) h

theorem euclideanPSD_lower (F : ℝ → ℝ) {d e : ℕ} (hde : d ≤ e)
    (h : RadialPSD (EuclideanSpace ℝ (Fin e)) F) :
    RadialPSD (EuclideanSpace ℝ (Fin d)) F := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hde
  induction k with
  | zero => simpa using h
  | succ k ih => exact ih (by omega) (euclideanPSD_step F (d+k) h)

theorem euclideanPSD_higher_failure (F : ℝ → ℝ) {d e : ℕ}
    (hde : d ≤ e) (h : ¬ RadialPSD (EuclideanSpace ℝ (Fin d)) F) :
    ¬ RadialPSD (EuclideanSpace ℝ (Fin e)) F :=
  fun he => h (euclideanPSD_lower F hde he)

/-- Abstract cutoff theorem; its two boundary hypotheses must be
established independently for any concrete radial function. -/
theorem euclideanPSD_cutoff (F : ℝ → ℝ) (D : ℕ)
    (hD : RadialPSD (EuclideanSpace ℝ (Fin D)) F)
    (hNext : ¬ RadialPSD (EuclideanSpace ℝ (Fin (D+1))) F)
    (d : ℕ) : RadialPSD (EuclideanSpace ℝ (Fin d)) F ↔ d ≤ D := by
  constructor
  · intro hd
    by_contra hn
    exact hNext (euclideanPSD_lower F (by omega) hd)
  · intro hd
    exact euclideanPSD_lower F hd hD

end Dimensions

section Spherical

/-- Inverse angular moment factor, equal to (d/2)_k/(1/2)_k.
The probabilistic spherical integration giving this factor is a separate
analytic obligation. -/
noncomputable def angularScale (d : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (d + 2 * (i : ℝ)) / (1 + 2 * (i : ℝ))

noncomputable def liftedMoment (d : ℝ) (m : ℕ → ℝ) (k : ℕ) : ℝ :=
  angularScale d k * m k

theorem angularScale_zero (d : ℝ) : angularScale d 0 = 1 := by
  simp [angularScale]

theorem angularScale_succ (d : ℝ) (k : ℕ) :
    angularScale d (k+1) = angularScale d k *
      ((d + 2 * (k : ℝ)) / (1 + 2 * (k : ℝ))) := by
  unfold angularScale
  rw [Finset.prod_range_succ]

theorem angularScale_pos (d : ℝ) (hd : 0 < d) (k : ℕ) :
    0 < angularScale d k := by
  unfold angularScale
  apply Finset.prod_pos
  intro i hi
  have h : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  exact div_pos (by linarith) (by linarith)

theorem liftedMoment_one (d : ℝ) (m : ℕ → ℝ) :
    liftedMoment d m 1 = d * m 1 := by
  simp [liftedMoment, angularScale]

theorem liftedMoment_two (d : ℝ) (m : ℕ → ℝ) :
    liftedMoment d m 2 = d * (d+2) / 3 * m 2 := by
  unfold liftedMoment
  rw [angularScale_succ d 1, angularScale_succ d 0, angularScale_zero]
  norm_num <;> ring <;> simp

/-- Necessary dimension bound from nonnegative variance of the lifted
radial squared norm. The moment-lift representation is not assumed true
of Xi here. -/
theorem lifted_kurtosis_bound (d : ℝ) (m : ℕ → ℝ)
    (hd : 0 < d) (hvar : (liftedMoment d m 1)^2 ≤ liftedMoment d m 2) :
    3 * d * (m 1)^2 ≤ (d+2) * m 2 := by
  rw [liftedMoment_one, liftedMoment_two] at hvar
  by_contra hn
  have hh : 0 < d * (3 * d * (m 1)^2 - (d+2) * m 2) :=
    mul_pos hd (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith [mul_le_mul_of_nonneg_left hvar (show (0:ℝ) ≤ 3 by norm_num)]

/-- If the fourth moment is strictly below the Gaussian threshold,
the variance inequality yields an upper bound on the dimension. -/
theorem lifted_dimension_bound (d : ℝ) (m : ℕ → ℝ)
    (hd : 0 < d) (hvar : (liftedMoment d m 1)^2 ≤ liftedMoment d m 2)
    (hgap : 0 < 3 * (m 1)^2 - m 2) :
    d ≤ 2 * m 2 / (3 * (m 1)^2 - m 2) := by
  apply (le_div_iff₀ hgap).2
  have h := lifted_kurtosis_bound d m hd hvar
  nlinarith

end Spherical

#print axioms integralFunctional_positive
#print axioms integralFunctional_moment
#print axioms measure_hankel_nonneg
#print axioms measure_hankel_obstruction
#print axioms kernelPSD_integral
#print axioms rankOne_quadratic
#print axioms cosine_kernelPSD
#print axioms cosine_mixturePSD
#print axioms euclideanPad_dist
#print axioms euclideanPSD_step
#print axioms euclideanPSD_lower
#print axioms euclideanPSD_higher_failure
#print axioms euclideanPSD_cutoff
#print axioms angularScale_zero
#print axioms angularScale_succ
#print axioms angularScale_pos
#print axioms liftedMoment_one
#print axioms liftedMoment_two
#print axioms lifted_kurtosis_bound
#print axioms lifted_dimension_bound
end GenesisFormalV5



/-!
# GENESIS–TIDAL D9–D10 analytic bridge

These are analytic lemmas, not a formalization of the concrete xi Fourier
representation or of the Arb sign certificates.
-/

open Set Filter MeasureTheory
open scoped Topology Interval

namespace GenesisTidal

/-- The D10 integration-by-parts identity on finite positive intervals. -/
theorem d10_integral_bridge_interval
    {g g' : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hg' : ContinuousOn g' (Icc a b)) :
    (∫ x in a..b, g' x / x) =
      g b / b - g a / a + ∫ x in a..b, g x / x ^ 2 := by
  have hpos : ∀ x ∈ Icc a b, x ≠ 0 :=
    fun x hx => ne_of_gt (ha.trans_le hx.1)
  have hc : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have h₁ : IntervalIntegrable (fun x => g' x / x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hg'.div continuous_id.continuousOn hpos
  have h₂ : IntervalIntegrable (fun x => g x / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hc.div (continuous_id.pow 2).continuousOn (fun x hx => pow_ne_zero _ (hpos x hx))
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun x => g x / x) (g' x / x - g x / x ^ 2) x := by
    rw [uIcc_of_le hab]
    intro x hx
    convert (hg x hx).div (hasDerivAt_id x) (hpos x hx) using 1
    · rfl
    · simp only [id_eq, mul_one]
      field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (h₁.sub h₂)
  rw [intervalIntegral.integral_sub h₁ h₂] at h
  linarith

/-- An even differentiable radial profile has zero derivative at the origin. -/
theorem d10_even_derivative_zero {U : ℝ → ℝ} {D : ℝ}
    (he : Function.Even U) (h : HasDerivAt U D 0) : D = 0 := by
  have hneg : HasDerivAt (fun x : ℝ => U (-x)) (-D) 0 := by
    change HasDerivAt (U ∘ Neg.neg) (-D) 0
    simpa using (show HasDerivAt U D (- (0 : ℝ)) by simpa using h).comp 0
      (hasDerivAt_neg (x := (0 : ℝ)))
  have heq : (fun x : ℝ => U (-x)) = U := funext he
  rw [heq] at hneg
  have hd := hneg.deriv.symm.trans h.deriv
  linarith

/-- The boundary expression vanishes at zero when U has zero derivative there. -/
theorem d10_boundary_zero {U : ℝ → ℝ} (h : HasDerivAt U 0 0) :
    Tendsto (fun x : ℝ => (U 0 - U x) / x) (𝓝[>] 0) (𝓝 0) := by
  simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, ← mul_neg, neg_sub] using
    h.tendsto_slope_zero_right.neg

/-- The same boundary expression vanishes at infinity when U decays. -/
theorem d10_boundary_infty {U : ℝ → ℝ} (h : Tendsto U atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => (U 0 - U x) / x) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.sub h).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))

/-- Equality of the integrals used by the historical mpmath and Arb D10 checks.
The profile's derivative, decay and integrability must be supplied by the
specific radial Fourier analysis. The boundary limits are derived here. -/
theorem d10_integral_bridge_Ioi {U U' : ℝ → ℝ}
    (hU : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt U (U' x) x)
    (he : Function.Even U) (hU0 : HasDerivAt U (U' 0) 0)
    (hInf : Tendsto U atTop (𝓝 0))
    (h₁ : IntegrableOn (fun x : ℝ => -U' x / x) (Ioi (0 : ℝ)))
    (h₂ : IntegrableOn (fun x : ℝ => (U 0 - U x) / x ^ 2) (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ), -U' x / x) = ∫ x in Ioi (0 : ℝ), (U 0 - U x) / x ^ 2 := by
  have hzero : Tendsto (fun x : ℝ => (U 0 - U x) / x) (𝓝[>] 0) (𝓝 0) := by
    apply d10_boundary_zero
    simpa [d10_even_derivative_zero he hU0] using hU0
  have hc : ContinuousWithinAt (fun x : ℝ => (U 0 - U x) / x) (Ici 0) 0 := by
    change Tendsto _ (𝓝[Ici (0 : ℝ)] 0) (𝓝 ((U 0 - U 0) / 0))
    have hs : Ici (0 : ℝ) = insert 0 (Ioi 0) := by
      ext x
      simp only [mem_Ici, mem_insert_iff, mem_Ioi]
      exact le_iff_eq_or_lt.trans (or_congr eq_comm Iff.rfl)
    rw [hs, nhdsWithin_insert, tendsto_sup]
    exact ⟨tendsto_pure_nhds _ _, by simpa using hzero⟩
  have hd : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun x => (U 0 - U x) / x)
        (-U' x / x - (U 0 - U x) / x ^ 2) x := by
    intro x hx
    have hn : x ≠ 0 := ne_of_gt hx
    convert ((hU x hx).const_sub (U 0)).div (hasDerivAt_id x) hn using 1
    · rfl
    · simp only [id_eq, mul_one]
      field_simp
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto hc hd (h₁.sub h₂) (d10_boundary_infty hInf)
  rw [integral_sub h₁ h₂] at hi
  simpa using sub_eq_zero.mp (show (∫ x in Ioi (0 : ℝ), -U' x / x) -
      (∫ x in Ioi (0 : ℝ), (U 0 - U x) / x ^ 2) = 0 by simpa using hi)

/-- The positive eighth derivative gives a positive weighted radial average.
The analytical identity identifying this average with U₄ is separate. -/
theorem d9_near_weighted_positive {P : ℝ → ℝ} {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (1 / 5))
    (hP : ∀ x ∈ Icc (0 : ℝ) (1 / 5), 0 < P x)
    (hc : Continuous P) :
    0 < (1 / 48 : ℝ) * (∫ t in (0 : ℝ)..1, (1 - t ^ 2) ^ 3 * P (r * t)) := by
  apply mul_pos (by norm_num)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact ((continuous_const.sub (continuous_id.pow 2)).pow 3 |>.mul
      (hc.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · intro t ht
    have hr₀ : 0 ≤ r := hr.1
    have hrt : r * t ∈ Icc (0 : ℝ) (1 / 5) :=
      ⟨mul_nonneg hr₀ ht.1.le, (mul_le_of_le_one_right hr₀ ht.2.le).trans hr.2⟩
    have ht2 : t * t < 1 * 1 := mul_lt_mul ht.2 ht.2.le ht.1 (by norm_num)
    exact mul_pos (pow_pos (by nlinarith [ht2]) _) (hP _ hrt)
  · norm_num

/-- The three domains checked in the D9 sign argument cover every nonnegative radius.
The factor r⁷ is removed only on the interval bounded away from zero. -/
theorem d9_positive_of_region_signs
    {U N : ℝ → ℝ}
    (hnear : ∀ r ∈ Icc (0 : ℝ) (1 / 5), 0 < U r)
    (hmid : ∀ r ∈ Icc (1 / 5 : ℝ) 1, 0 < N r)
    (hfactor : ∀ r ∈ Icc (1 / 5 : ℝ) 1, N r = r ^ 7 * U r)
    (hfar : ∀ r ∈ Ici (1 : ℝ), 0 < U r) :
    ∀ r ∈ Ici (0 : ℝ), 0 < U r := by
  intro r hr
  by_cases h₁ : r ≤ 1 / 5
  · exact hnear r ⟨hr, h₁⟩
  by_cases h₂ : r ≤ 1
  · have hm : r ∈ Icc (1 / 5 : ℝ) 1 := ⟨le_of_lt (lt_of_not_ge h₁), h₂⟩
    have hp : 0 < r ^ 7 := pow_pos (by linarith [hm.1]) _
    have hh := hmid r hm
    rw [hfactor r hm] at hh
    exact (mul_pos_iff_of_pos_left hp).mp hh
  · exact hfar r (le_of_lt (lt_of_not_ge h₂))

/-- Sign transfer once the D10 Fourier marginal identity is proved. -/
theorem d10_negative_of_marginal {J Z f₀ : ℝ}
    (hZ : 0 < Z) (hJ : J < 0) (hf : f₀ = 2 * J / ((2 * Real.pi) ^ 5 * Z)) :
    f₀ < 0 := by
  rw [hf]
  exact div_neg_of_neg_of_pos (by linarith)
    (mul_pos (pow_pos (mul_pos (by norm_num) Real.pi_pos) _) hZ)


/-- Signed derivative-polynomial evaluations used to establish the D9 tail.
The four polynomials are Q₁ to Q₄ in the Arb implementation. The proof
checks the shifted expansions by exact algebra and uses x - 20 ≥ 0. -/
theorem d9_shifted_polynomial_signs {x : ℝ} (hx : 20 ≤ x) :
    (-4*x^3 + 15*x^2 - (15/2)*x < 0) ∧
    (0 < 8*x^4 - 56*x^3 + (165/2)*x^2 - (75/4)*x) ∧
    (-16*x^5 + 180*x^4 - 529*x^3 + (1635/4)*x^2 - (375/8)*x < 0) ∧
    (0 < 32*x^6 - 528*x^5 + 2588*x^4 - 4256*x^3 + (15465/8)*x^2 - (1875/16)*x) := by
  let y := x - 20
  have hy : 0 ≤ y := sub_nonneg.mpr hx
  have he : x = y + 20 := by dsimp [y]; ring
  rw [he]
  have h1 : -(-4*(y+20)^3 + 15*(y+20)^2 - (15/2)*(y+20)) =
      4*y^3 + 225*y^2 + (8415/2)*y + 26150 := by ring
  have h2 : 8*(y+20)^4 - 56*(y+20)^3 + (165/2)*(y+20)^2 - (75/4)*(y+20) =
      8*y^4 + 584*y^3 + (31845/2)*y^2 + (768325/4)*y + 864625 := by ring
  have h3 : -(-16*(y+20)^5 + 180*(y+20)^4 - 529*(y+20)^3 + (1635/4)*(y+20)^2 -
      (375/8)*(y+20)) =
      16*y^5 + 1420*y^4 + 50129*y^3 + (3517325/4)*y^2 + (61267975/8)*y + 52938875/2 := by ring
  have h4 : 32*(y+20)^6 - 528*(y+20)^5 + 2588*(y+20)^4 - 4256*(y+20)^3 +
      (15465/8)*(y+20)^2 - (1875/16)*(y+20) =
      32*y^6 + 3312*y^5 + 141788*y^4 + 3210784*y^3 + (324142185/8)*y^2 +
      (4316576125/16)*y + 2956811625/4 := by ring
  refine ⟨neg_pos.mp ?_, ?_, neg_pos.mp ?_, ?_⟩
  · rw [h1]; positivity
  · rw [h2]; positivity
  · rw [h3]; positivity
  · rw [h4]; positivity


/-- Every positive-index theta summand is in the shifted sign range for r ≥ 1. -/
theorem d9_theta_argument_gt_twenty {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    20 < Real.pi * ((n : ℝ) + 1)^2 * Real.exp (2*r) := by
  have h₁ : (27 / 10 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have h₂ : (729 / 100 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [mul_pos (sub_pos.mpr h₁) (add_pos (Real.exp_pos 1) (show (0 : ℝ) < 27 / 10 by norm_num))]
  have h₃ : 1 ≤ ((n : ℝ) + 1)^2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    20 < 3 * (729 / 100 : ℝ) := by norm_num
    _ ≤ Real.pi * ((n : ℝ) + 1)^2 * Real.exp (2*r) := by
      gcongr
      · exact Real.pi_gt_three.le.trans (by simpa using mul_le_mul_of_nonneg_left h₃ Real.pi_pos.le)
      · exact h₂.le.trans (Real.exp_le_exp.mpr (by linarith))

/-- Remove the positive r⁷ factor in the far tail once the signed derivative
series have been identified and their signs established. -/
theorem d9_far_of_alternating {r u p₁ p₂ p₃ p₄ : ℝ}
    (hr : 0 < r) (h₁ : p₁ < 0) (h₂ : 0 < p₂) (h₃ : p₃ < 0) (h₄ : 0 < p₄)
    (hu : r^7 * u = r^3*p₄ - 6*r^2*p₃ + 15*r*p₂ - 15*p₁) :
    0 < u := by
  apply (mul_pos_iff_of_pos_left (pow_pos hr 7)).mp
  rw [hu]
  have ha : 0 < r^3 * p₄ := mul_pos (pow_pos hr 3) h₄
  have hb : 0 < (6*r^2) * (-p₃) := mul_pos (mul_pos (by norm_num) (pow_pos hr 2)) (neg_pos.mpr h₃)
  have hc : 0 < (15*r) * p₂ := mul_pos (mul_pos (by norm_num) hr) h₂
  linarith

end GenesisTidal

#print axioms GenesisTidal.d10_integral_bridge_interval
#print axioms GenesisTidal.d9_positive_of_region_signs
#print axioms GenesisTidal.d10_negative_of_marginal

#print axioms GenesisTidal.d10_even_derivative_zero
#print axioms GenesisTidal.d10_boundary_zero
#print axioms GenesisTidal.d10_boundary_infty
#print axioms GenesisTidal.d10_integral_bridge_Ioi
#print axioms GenesisTidal.d9_near_weighted_positive

#print axioms GenesisTidal.d9_shifted_polynomial_signs
#print axioms GenesisTidal.d9_far_of_alternating

#print axioms GenesisTidal.d9_theta_argument_gt_twenty

namespace GenesisTidal

/-- The entire completed xi, expressed using Mathlib's pole-subtracted zeta. -/
noncomputable def completedXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- This pole-free definition agrees with the usual xi formula away from the poles. -/
theorem completedXi_eq (s : ℂ) (h₀ : s ≠ 0) (h₁ : s ≠ 1) :
    completedXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have h₁' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁)
  rw [completedXi, completedRiemannZeta_eq]
  field_simp
  ring

/-- The even symmetry of xi follows from Mathlib's functional equation. -/
theorem completedXi_one_sub (s : ℂ) : completedXi (1 - s) = completedXi s := by
  simp only [completedXi, completedRiemannZeta₀_one_sub]
  ring

/-- The actual normalized real xi profile to be used by the cutoff theorem. -/
noncomputable def criticalXiProfile (t : ℝ) : ℝ :=
  (completedXi (1 / 2 + (t : ℂ) * Complex.I) / completedXi (1 / 2)).re

theorem criticalXiProfile_even : Function.Even criticalXiProfile := by
  intro t
  rw [criticalXiProfile, criticalXiProfile]
  have h : (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I =
      1 - (1 / 2 + (t : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, completedXi_one_sub]

/-- The concrete target with both xi-specific premises explicit.
These hypotheses are not established by this module or supplied as axioms. -/
theorem criticalXi_cutoff_of_boundary_dimensions
    (h9 : GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin 9)) criticalXiProfile)
    (h10 : ¬ GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin 10)) criticalXiProfile)
    (d : ℕ) :
    GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin d)) criticalXiProfile ↔ d ≤ 9 :=
  GenesisFormalV5.euclideanPSD_cutoff criticalXiProfile 9 h9 h10 d

end GenesisTidal

#print axioms GenesisTidal.completedXi_eq
#print axioms GenesisTidal.completedXi_one_sub
#print axioms GenesisTidal.criticalXiProfile_even
#print axioms GenesisTidal.criticalXi_cutoff_of_boundary_dimensions

open scoped BigOperators
open Polynomial

namespace GenesisD10Witness

/-- A product of coordinate monomials adds their degrees and multiplies weights. -/
theorem prod_coordinate_monomial {ι : Type*} (s : Finset ι)
    (q w : ι → ℕ) :
    (∏ i ∈ s, monomial (q i) (w i) : ℕ[X]) =
      monomial (∑ i ∈ s, q i) (∏ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, ih,
      monomial_mul_monomial]

/-- The single-coordinate distance histogram as a polynomial. -/
noncomputable def histogram {α : Type*} [Fintype α] (q : α → ℕ) (w : α → ℕ) : ℕ[X] :=
  ∑ a, monomial (q a) (w a)

/-- The product-grid histogram is the power of the one-coordinate histogram. -/
theorem histogram_power {α : Type*} [Fintype α] (q w : α → ℕ) (n : ℕ) :
    histogram q w ^ n =
      ∑ p : Fin n → α, monomial (∑ i, q (p i)) (∏ i, w (p i)) := by
  classical
  calc
    histogram q w ^ n = ∏ _i : Fin n, ∑ a : α, monomial (q a) (w a) := by
      simp [histogram]
    _ = ∑ p : Fin n → α, ∏ i, monomial (q (p i)) (w (p i)) :=
      Fintype.prod_sum (fun _ : Fin n => fun a : α => monomial (q a) (w a))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      exact prod_coordinate_monomial Finset.univ (fun i => q (p i)) (fun i => w (p i))

/-- Compressed sum over the support of the histogram. -/
noncomputable def compressed (P : ℕ[X]) (F : ℕ → ℝ) : ℝ :=
  ∑ k ∈ P.support, (P.coeff k : ℝ) * F k

theorem compressed_eq_on {P : ℕ[X]} (F : ℕ → ℝ) {s : Finset ℕ}
    (hs : P.support ⊆ s) :
    compressed P F = ∑ k ∈ s, (P.coeff k : ℝ) * F k := by
  classical
  apply Finset.sum_subset hs
  intro k _ hk
  simp [Polynomial.notMem_support_iff.mp hk]

/-- Exact compression for any sampled radial profile and any grid dimension. -/
theorem compressed_power {α : Type*} [Fintype α] (q w : α → ℕ)
    (n : ℕ) (F : ℕ → ℝ) :
    compressed (histogram q w ^ n) F =
      ∑ p : Fin n → α, ((∏ i, w (p i) : ℕ) : ℝ) * F (∑ i, q (p i)) := by
  classical
  let s := Finset.univ.image (fun p : Fin n → α => ∑ i, q (p i))
  have hs : (histogram q w ^ n).support ⊆ s := by
    intro k hk
    by_contra h
    apply (Polynomial.mem_support_iff.mp hk)
    rw [histogram_power, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun p _ => ?_
    apply Polynomial.coeff_monomial_of_ne
    intro he
    exact h (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, he.symm⟩)
  rw [compressed_eq_on F hs, histogram_power]
  simp only [Polynomial.finsetSum_coeff, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hm : (∑ i, q (p i)) ∈ s := Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  simp [Polynomial.coeff_monomial, apply_ite, ite_mul, eq_comm, hm]

/-- The ten one-dimensional weights from the recovered finite certificate. -/
def weights (a : Fin 10) : ℕ := ![282, 541, 756, 910, 990, 990, 910, 756, 541, 282] a

def distanceIndex (p : Fin 10 × Fin 10) : ℕ := Nat.dist p.1.val p.2.val ^ 2

def pairWeight (p : Fin 10 × Fin 10) : ℕ := weights p.1 * weights p.2

noncomputable def witnessPolynomial : ℕ[X] := histogram distanceIndex pairWeight ^ 10

/-- The spacing-7 lattice point associated to a grid tuple. -/
noncomputable def point (x : Fin 10 → Fin 10) : EuclideanSpace ℝ (Fin 10) :=
  WithLp.toLp 2 (fun i => (7 : ℝ) * (x i).val)

noncomputable def sample (F : ℝ → ℝ) (k : ℕ) : ℝ := F (7 * Real.sqrt k)

theorem euclidean_distance (x y : Fin 10 → Fin 10) :
    dist (point x) (point y) = 7 * Real.sqrt (∑ i, distanceIndex (x i, y i) : ℕ) := by
  rw [EuclideanSpace.dist_eq, ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7),
    ← Real.sqrt_mul (sq_nonneg (7 : ℝ))]
  congr 1
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change dist (7 * ((x i).val : ℝ)) (7 * ((y i).val : ℝ)) ^ 2 =
    7 ^ 2 * ((Nat.dist (x i).val (y i).val ^ 2 : ℕ) : ℝ)
  rw [Nat.cast_pow, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7), mul_pow]
  congr 2
  unfold Nat.dist
  rcases le_total (x i).val (y i).val with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_sub_comm, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)

/-- The exact link between the lattice Gram form and the compressed coefficients.
This identity does not depend on any numerical approximation to F. -/
theorem witness_gram_compression (F : ℝ → ℝ) :
    compressed witnessPolynomial (sample F) =
      ∑ x : Fin 10 → Fin 10, ∑ y : Fin 10 → Fin 10,
        ((∏ i, (weights (x i) : ℝ)) * (∏ i, (weights (y i) : ℝ))) *
          F (dist (point x) (point y)) := by
  classical
  rw [witnessPolynomial, compressed_power]
  let G : ((Fin 10 → Fin 10) × (Fin 10 → Fin 10)) → ℝ := fun p =>
    ((∏ i, (weights (p.1 i) : ℝ)) * (∏ i, (weights (p.2 i) : ℝ))) *
      F (dist (point p.1) (point p.2))
  trans ∑ p, G p
  · refine Fintype.sum_equiv
      (Equiv.arrowProdEquivProdArrow (Fin 10) (fun _ => Fin 10) (fun _ => Fin 10)) _ G ?_
    intro p
    dsimp [G]
    rw [euclidean_distance]
    simp [sample, distanceIndex, pairWeight, Nat.cast_prod, Nat.cast_mul, Finset.prod_mul_distrib]
  · exact Fintype.sum_prod_type G

/-- Exact coefficient normalization used by the numerical certificate. -/
def normalization : ℕ := ((List.sum ([282,541,756,910,990,990,910,756,541,282].map
    (fun a : ℕ => a * a)))) ^ 10

theorem normalization_pos : 0 < normalization := by decide

/-- The outward-rounded aggregate bounds suffice, with explicit rational slack.
The two inequalities are inputs, not claims that Lean has computed xi values. -/
theorem negative_of_enclosures {retained omitted : ℝ}
    (h₁ : retained ≤ -(125963671 : ℝ) / 10000000000)
    (h₂ : omitted ≤ (1 : ℝ) / 1000000000) :
    retained + omitted < 0 := by linarith

end GenesisD10Witness

namespace GenesisD10Witness

/-- Retained or omitted normalized contribution, split at floor(120²/7²) = 293. -/
noncomputable def retained (F : ℝ → ℝ) : ℝ :=
  (∑ k ∈ witnessPolynomial.support.filter (fun k => k ≤ 293),
    (witnessPolynomial.coeff k : ℝ) * sample F k) / (normalization : ℝ)

noncomputable def omitted (F : ℝ → ℝ) : ℝ :=
  (∑ k ∈ witnessPolynomial.support.filter (fun k => ¬ k ≤ 293),
    (witnessPolynomial.coeff k : ℝ) * sample F k) / (normalization : ℝ)

theorem retained_add_omitted (F : ℝ → ℝ) :
    retained F + omitted F = compressed witnessPolynomial (sample F) / (normalization : ℝ) := by
  classical
  rw [retained, omitted, ← add_div, Finset.sum_filter_add_sum_filter_not, compressed]

/-- PSD is independent of the choice of finite index type. -/
theorem kernelPSD_for_fintype {X α : Type*} [Fintype α]
    {K : X → X → ℝ} (hK : GenesisFormalV4.KernelPSD K)
    (xs : α → X) (c : α → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * K (xs i) (xs j) := by
  classical
  let e := Fintype.equivFin α
  have hnon := hK _ (fun i => xs (e.symm i)) (fun i => c (e.symm i))
  have hsum :
      (∑ x, ∑ y, c x * c y * K (xs x) (xs y)) =
      ∑ i, ∑ j, c (e.symm i) * c (e.symm j) * K (xs (e.symm i)) (xs (e.symm j)) := by
    refine Fintype.sum_equiv e _ _ (fun x => ?_)
    refine Fintype.sum_equiv e _ _ (fun y => ?_)
    simp
  rwa [hsum]

/-- A negative compressed sum is a finite Euclidean PSD counterexample. -/
theorem not_radialPSD_of_negative (F : ℝ → ℝ)
    (h : compressed witnessPolynomial (sample F) < 0) :
    ¬ GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin 10)) F := by
  intro hp
  have hn := kernelPSD_for_fintype hp point (fun x => ∏ i, (weights (x i) : ℝ))
  rw [witness_gram_compression F] at h
  exact (not_lt_of_ge hn) h

/-- The complex normalization in FORMAL v6 equals the normalization by real
parts used in the certificate, because the central completed xi is real. -/
theorem criticalXiProfile_eq_re_ratio (t : ℝ) :
    GenesisTidal.criticalXiProfile t =
      (GenesisTidal.completedXi (1 / 2 + (t : ℂ) * Complex.I)).re /
      (GenesisTidal.completedXi (1 / 2)).re := by
  have hm : (completedRiemannZeta (1 / 2 : ℂ)).im = 0 := by
    simpa using completedRiemannZeta_half_add_mul_I_im (0 : ℝ)
  have hx : (GenesisTidal.completedXi (1 / 2 : ℂ)).im = 0 := by
    rw [GenesisTidal.completedXi_eq _ (by norm_num) (by norm_num)]
    norm_num [Complex.mul_im, Complex.mul_re, Complex.sub_im, hm]
  have hr : ((GenesisTidal.completedXi (1 / 2 : ℂ)).re : ℂ) =
      GenesisTidal.completedXi (1 / 2) := by
    apply Complex.ext
    · exact Complex.ofReal_re _
    · exact (Complex.ofReal_im _).trans hx.symm
  unfold GenesisTidal.criticalXiProfile
  nth_rw 1 [← hr]
  exact Complex.div_ofReal_re _ _

/-- Conditional interface between the exact finite witness and the external
interval certificate. Neither enclosure is postulated as a Lean axiom. -/
theorem xi_not_radialPSD_d10_of_enclosures
    (hret : retained GenesisTidal.criticalXiProfile ≤ -(125963671 : ℝ) / 10000000000)
    (hom : omitted GenesisTidal.criticalXiProfile ≤ (1 : ℝ) / 1000000000) :
    ¬ GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin 10)) GenesisTidal.criticalXiProfile := by
  have h := negative_of_enclosures hret hom
  rw [retained_add_omitted] at h
  apply not_radialPSD_of_negative
  by_contra! hn
  have hp : 0 ≤ (normalization : ℝ) := Nat.cast_nonneg _
  exact (not_lt_of_ge (div_nonneg hn hp)) h

end GenesisD10Witness

#print axioms GenesisD10Witness.prod_coordinate_monomial
#print axioms GenesisD10Witness.histogram_power
#print axioms GenesisD10Witness.compressed_eq_on
#print axioms GenesisD10Witness.compressed_power
#print axioms GenesisD10Witness.euclidean_distance
#print axioms GenesisD10Witness.witness_gram_compression
#print axioms GenesisD10Witness.normalization_pos
#print axioms GenesisD10Witness.negative_of_enclosures
#print axioms GenesisD10Witness.retained_add_omitted
#print axioms GenesisD10Witness.not_radialPSD_of_negative
#print axioms GenesisD10Witness.xi_not_radialPSD_d10_of_enclosures

#print axioms GenesisD10Witness.criticalXiProfile_eq_re_ratio

#print axioms GenesisD10Witness.kernelPSD_for_fintype

namespace GenesisTidal

open MeasureTheory Set
open scoped InnerProductSpace

/-- A real integrable nonnegative spectral density gives a PSD radial kernel
when its cosine inversion is the specified profile. -/
theorem radialPSD_of_cosine_density {d : ℕ} {F : ℝ → ℝ}
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Integrable f) (hn : ∀ k, 0 ≤ f k)
    (hinv : ∀ x : EuclideanSpace ℝ (Fin d),
      F ‖x‖ = ∫ k, f k * Real.cos ⟪k, x⟫_ℝ) :
    GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin d)) F := by
  change GenesisFormalV4.KernelPSD (fun x y : EuclideanSpace ℝ (Fin d) => F (dist x y))
  have hK : GenesisFormalV4.KernelPSD
      (fun x y : EuclideanSpace ℝ (Fin d) => ∫ k, f k *
        Real.cos (⟪k, x⟫_ℝ - ⟪k, y⟫_ℝ)) := by
    apply GenesisFormalV5.kernelPSD_integral volume
    · apply Filter.Eventually.of_forall
      intro k n xs c
      have h := GenesisFormalV5.cosine_kernelPSD
        (fun x : EuclideanSpace ℝ (Fin d) => ⟪k, x⟫_ℝ) n xs c
      dsimp at h ⊢
      have he :
          (∑ i, ∑ j, c i * c j * (f k * Real.cos (⟪k, xs i⟫_ℝ - ⟪k, xs j⟫_ℝ))) =
          f k * (∑ i, ∑ j, c i * c j * Real.cos (⟪k, xs i⟫_ℝ - ⟪k, xs j⟫_ℝ)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [he]
      exact mul_nonneg (hn k) h
    · intro x y
      have hc : Continuous (fun k : EuclideanSpace ℝ (Fin d) =>
          Real.cos (⟪k, x⟫_ℝ - ⟪k, y⟫_ℝ)) := by fun_prop
      apply hf.norm.mono' (hf.aestronglyMeasurable.mul hc.aestronglyMeasurable)
      apply Filter.Eventually.of_forall
      intro k
      change ‖f k * Real.cos (⟪k, x⟫_ℝ - ⟪k, y⟫_ℝ)‖ ≤ ‖f k‖
      rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
  have he :
      (fun x y : EuclideanSpace ℝ (Fin d) => F (dist x y)) =
      (fun x y : EuclideanSpace ℝ (Fin d) => ∫ k, f k *
        Real.cos (⟪k, x⟫_ℝ - ⟪k, y⟫_ℝ)) := by
    funext x y
    rw [dist_eq_norm, hinv (x - y)]
    simp only [inner_sub_right]
  rwa [he]

/-- Discharges the D9 PSD premise from the actual target's cosine inversion,
the density normalization, and the three sign regions. -/
theorem criticalXi_d9_of_radial_signs
    {U N : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hnear : ∀ r ∈ Icc (0 : ℝ) (1 / 5), 0 < U r)
    (hmid : ∀ r ∈ Icc (1 / 5 : ℝ) 1, 0 < N r)
    (hfactor : ∀ r ∈ Icc (1 / 5 : ℝ) 1, N r = r ^ 7 * U r)
    (hfar : ∀ r ∈ Ici (1 : ℝ), 0 < U r)
    (hint : Integrable (fun k : EuclideanSpace ℝ (Fin 9) => U ‖k‖ / C))
    (hinv : ∀ x : EuclideanSpace ℝ (Fin 9),
      criticalXiProfile ‖x‖ = ∫ k : EuclideanSpace ℝ (Fin 9),
        (U ‖k‖ / C) * Real.cos ⟪k, x⟫_ℝ) :
    GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin 9)) criticalXiProfile := by
  apply radialPSD_of_cosine_density _ hint _ hinv
  intro k
  exact (div_pos (d9_positive_of_region_signs hnear hmid hfactor hfar ‖k‖
    (norm_nonneg k)) hC).le

/-- Direct Xi D10 finite witness replaces the negative-density/Bochner route.
D9 is provided as cosine inversion with nonnegative integrable density;
D10 is provided as rigorous numeric enclosures on finite witness terms. -/
theorem criticalXi_cutoff_of_density_and_finite_certificate
    (f : EuclideanSpace ℝ (Fin 9) → ℝ)
    (hf : Integrable f) (hn : ∀ k, 0 ≤ f k)
    (hinv : ∀ x : EuclideanSpace ℝ (Fin 9),
      criticalXiProfile ‖x‖ = ∫ k, f k * Real.cos ⟪k, x⟫_ℝ)
    (hret : GenesisD10Witness.retained criticalXiProfile ≤ -(125963671 : ℝ) / 10000000000)
    (hom : GenesisD10Witness.omitted criticalXiProfile ≤ (1 : ℝ) / 1000000000)
    (d : ℕ) :
    GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin d)) criticalXiProfile ↔ d ≤ 9 :=
  criticalXi_cutoff_of_boundary_dimensions (radialPSD_of_cosine_density f hf hn hinv)
    (GenesisD10Witness.xi_not_radialPSD_d10_of_enclosures hret hom) d

end GenesisTidal

#print axioms GenesisTidal.radialPSD_of_cosine_density
#print axioms GenesisTidal.criticalXi_d9_of_radial_signs
#print axioms GenesisTidal.criticalXi_cutoff_of_density_and_finite_certificate

namespace GenesisTidal

/-- The completed-zeta expression used by the finite Arb replay, now tied
to the pole-free Mathlib definition at every sampled critical-line point. -/
theorem completedXi_critical_eq_gamma_zeta (t : ℝ) :
    let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
    completedXi s = s * (s - 1) / 2 * Complex.Gamma (s / 2) *
      (Real.pi : ℂ) ^ (-s / 2) * riemannZeta s := by
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  change completedXi s = s * (s - 1) / 2 * Complex.Gamma (s / 2) *
    (Real.pi : ℂ) ^ (-s / 2) * riemannZeta s
  have hs : s.re = 1 / 2 := by
    simp [s, Complex.mul_re]
  have h0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    norm_num at hs
  have h1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    norm_num at hs
  have hg : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hz : riemannZeta s * Complex.Gammaℝ s = completedRiemannZeta s := by
    rw [riemannZeta_def_of_ne_zero h0, div_mul_cancel₀ _ hg]
  rw [completedXi_eq s h0 h1, ← hz, Complex.Gammaℝ]
  ring

end GenesisTidal

#print axioms GenesisTidal.completedXi_critical_eq_gamma_zeta

namespace GenesisTidal

open MeasureTheory Set Filter
open scoped Topology

/-- Polar integration for profiles indexed by squared radius, avoiding
a square-root substitution at zero. -/
theorem planar_sq_profile_integral (a : ℝ) (G : ℝ → ℝ) :
    (∫ p : ℝ × ℝ, G (a + (p.1 ^ 2 + p.2 ^ 2))) =
      (2 * Real.pi) * ∫ r in Ioi (0 : ℝ), r * G (a + r ^ 2) := by
  calc
    _ = ∫ p in polarCoord.target, p.1 * G (a + p.1 ^ 2) := by
      rw [← integral_comp_polarCoord_symm]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [polarCoord_symm_apply, smul_eq_mul]
        have h : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
          calc
            _ = p.1 ^ 2 * (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) := by ring
            _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]
        rw [h]
    _ = (∫ r in Ioi (0 : ℝ), r * G (a + r ^ 2)) *
          ∫ θ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul]
      simp only [polarCoord_target, mul_one, Measure.volume_eq_prod]
    _ = _ := by
      rw [mul_comm]
      congr 1
      simp only [setIntegral_const, smul_eq_mul, mul_one]
      rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_nonneg])]
      ring

/-- Two extra Euclidean coordinates have the claimed marginal when the
dimension-walk density is constructed by differentiating in squared radius. -/
theorem planar_marginal_of_sq_derivative (a : ℝ) (G D : ℝ → ℝ)
    (hG : ∀ s ≥ a, HasDerivAt G (D s) s)
    (hdecay : Tendsto (fun r : ℝ => G (a + r ^ 2)) atTop (𝓝 0))
    (hI : IntegrableOn (fun r : ℝ => r * (-D (a + r ^ 2) / Real.pi)) (Ioi 0)) :
    (∫ p : ℝ × ℝ, -D (a + (p.1 ^ 2 + p.2 ^ 2)) / Real.pi) = G a := by
  rw [planar_sq_profile_integral a (fun s => -D s / Real.pi)]
  have hd : ∀ r ∈ Ici (0 : ℝ),
      HasDerivAt (fun r : ℝ => -G (a + r ^ 2))
        ((2 * Real.pi) * (r * (-D (a + r ^ 2) / Real.pi))) r := by
    intro r _
    have ha : a ≤ a + r ^ 2 := le_add_of_nonneg_right (sq_nonneg r)
    have hq : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r := by
      simpa using ((hasDerivAt_id r).pow 2).const_add a
    convert ((hG _ ha).comp r hq).neg using 1
    · rfl
    · field_simp [Real.pi_ne_zero] <;> ring
  have hl : Tendsto (fun r : ℝ => -G (a + r ^ 2)) atTop (𝓝 0) := by
    simpa using hdecay.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (hI.const_mul (2 * Real.pi)) hl
  simpa [integral_const_mul] using h

end GenesisTidal

#print axioms GenesisTidal.planar_sq_profile_integral
#print axioms GenesisTidal.planar_marginal_of_sq_derivative
