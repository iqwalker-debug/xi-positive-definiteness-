import analysis.special_functions.trigonometric.inverse
import tactic

namespace paper_v_field
abbreviation point := ℝ × ℝ
abbreviation sample := ℝ × (point → ℝ)

-- Each listed trajectory f with weight w represents the two outcomes ±f,
-- of probability w/2 each. This makes the ensemble centered.
def mass (l : list sample) := (l.map prod.fst).sum
def second (l : list sample) (p q : point) :=
  (l.map (λ e : sample, e.1 * e.2 p * e.2 q)).sum

structure field (C : point → ℝ) (m : ℝ) : Prop :=
(cont : continuous C)
(even_space : ∀ h t, C (-h,t) = C (h,t))
(ensemble : ∃ l : list sample, (∀ e ∈ l, 0 ≤ (e : sample).1) ∧ mass l = m ∧
  ∀ p q : point, second l p q = C (p.1-q.1,p.2-q.2))

noncomputable def paired : list sample → list sample
| [] := []
| ((w,f)::rest) := (w/2,f)::(w/2,λ p, -f p)::paired rest

def mean (l : list sample) (p : point) := (l.map (λ e : sample, e.1*e.2 p)).sum

lemma paired_mass : ∀ l, mass (paired l) = mass l
| [] := rfl
| ((w,f)::rest) := by have h := paired_mass rest; unfold mass at *;
  simp [paired,list.sum_cons,h]; ring

lemma paired_mean (p : point) : ∀ l, mean (paired l) p = 0
| [] := rfl
| ((w,f)::rest) := by have h := paired_mean rest; unfold mean at *;
  simp [paired,list.sum_cons,h]; ring

lemma paired_second (p q : point) : ∀ l, second (paired l) p q = second l p q
| [] := rfl
| ((w,f)::rest) := by have h := paired_second rest; unfold second at *;
  simp [paired,list.sum_cons,h]; ring

lemma paired_positive : ∀ l : list sample, (∀ e ∈ l, 0 ≤ (e:sample).1) →
  ∀ e ∈ paired l, 0 ≤ (e:sample).1
| [] h e he := false.elim (list.not_mem_nil _ he)
| ((w,f)::rest) h e he := begin
  have hw := h (w,f) (list.mem_cons_self _ _),
  change 0 ≤ w at hw,
  simp only [paired,list.mem_cons_iff] at he,
  rcases he with h1 | h2 | hr,
  { subst e, dsimp, linarith },
  { subst e, dsimp, linarith },
  { exact paired_positive rest (λ z hz, h z (list.mem_cons_of_mem _ hz)) e hr },
end

theorem finite_centered_field {C : point → ℝ} (hc : field C 1) :
  ∃ outcomes : list sample, (∀ e ∈ outcomes, 0 ≤ (e:sample).1) ∧
    mass outcomes = 1 ∧ (∀ p, mean outcomes p = 0) ∧
    ∀ p q : point, second outcomes p q = C (p.1-q.1,p.2-q.2) :=
begin
  rcases hc.ensemble with ⟨l,hpos,hm,hs⟩,
  exact ⟨paired l, paired_positive l hpos, (paired_mass l).trans hm,
    λ p, paired_mean p l, λ p q, (paired_second p q l).trans (hs p q)⟩,
end

lemma add_field {C D : point → ℝ} {m n : ℝ} (hc : field C m) (hd : field D n) :
  field (λ p, C p + D p) (m+n) :=
begin
  refine ⟨hc.cont.add hd.cont, λ h t, congr_arg2 (+) (hc.even_space h t) (hd.even_space h t), _⟩,
  rcases hc.ensemble with ⟨l,hl,ml,vl⟩,
  rcases hd.ensemble with ⟨r,hr,mr,vr⟩,
  refine ⟨l++r, _, _, _⟩,
  { intros e he, rcases list.mem_append.mp he with h | h, exact hl e h, exact hr e h },
  { unfold mass at *, simp [ml,mr] },
  { intros p q, unfold second at *, simp [vl,vr] },
end

noncomputable def kernel (k v : ℝ) (p : point) := real.cos (k*p.1) * real.cos (v*p.2)

lemma atom_field (k v w : ℝ) (hw : 0 ≤ w) :
  field (λ p, w*kernel k v p) w :=
begin
  refine ⟨continuous_const.mul ((real.continuous_cos.comp (continuous_const.mul continuous_fst)).mul
    (real.continuous_cos.comp (continuous_const.mul continuous_snd))), _, _⟩,
  { intros, simp [kernel] },
  let f := λ (a b : ℝ → ℝ) (p : point), 2*a (k*p.1)*b (v*p.2),
  let l : list sample := [(w/4,f real.cos real.cos),(w/4,f real.cos real.sin),
    (w/4,f real.sin real.cos),(w/4,f real.sin real.sin)],
  refine ⟨l, _, _, _⟩,
  { intros e he, simp only [l,list.mem_cons_iff,list.not_mem_nil,or_false] at he,
    rcases he with h | h | h | h; subst e; dsimp; linarith },
  { dsimp [mass,l,list.sum]; ring },
  { intros p q, dsimp [second,l,f,kernel,list.sum], simp only [mul_sub,real.cos_sub], ring },
end

noncomputable def atom (x : ℝ) (positive : bool) (b : ℝ) :=
  kernel (real.arccos x / 8) (if positive then 0 else real.pi / b)

def T (x : ℝ) : ℕ → ℝ
| 0 := 1
| 1 := x
| (n+2) := 2*x*T (n+1)-T n

lemma cosine_moment (x : ℝ) (lo : -1 ≤ x) (hi : x ≤ 1) :
  ∀ n : ℕ, real.cos ((n:ℝ)*real.arccos x) = T x n
| 0 := by simp [T]
| 1 := by simp [T,real.cos_arccos lo hi]
| (n+2) := begin
  have h := real.cos_add_cos (((n:ℝ)+2)*real.arccos x) ((n:ℝ)*real.arccos x),
  rw [show ((((n:ℝ)+2)*real.arccos x + (n:ℝ)*real.arccos x)/2) =
    ((n:ℝ)+1)*real.arccos x, by ring,
    show ((((n:ℝ)+2)*real.arccos x - (n:ℝ)*real.arccos x)/2) = real.arccos x, by ring,
    real.cos_arccos lo hi, cosine_moment n] at h,
  have prev := cosine_moment (n+1),
  simp only [nat.cast_add,nat.cast_one,nat.cast_bit0] at *,
  change real.cos _ = 2*x*T x (n+1)-T x n,
  rw [←prev], linarith,
end

lemma at_zero (x b : ℝ) (s : bool) (n : ℕ) (lo : -1 ≤ x) (hi : x ≤ 1) :
  atom x s b (8*(n:ℝ),0) = T x n :=
by simp [atom,kernel,show real.arccos x / 8 * (8*(n:ℝ)) = (n:ℝ)*real.arccos x, by ring,
  cosine_moment x lo hi]

lemma at_lag (x b : ℝ) (s : bool) (n : ℕ) (hb : b ≠ 0) (lo : -1 ≤ x) (hi : x ≤ 1) :
  atom x s b (8*(n:ℝ),b) = (if s then (1:ℝ) else -1) * T x n :=
begin
  cases s; simp [atom,kernel,div_mul_cancel _ hb,real.cos_pi,
    show real.arccos x / 8 * (8*(n:ℝ)) = (n:ℝ)*real.arccos x, by ring,
    cosine_moment x lo hi],
end

-- A finite model at an arbitrary common nonzero lag.
def model (b : ℝ) (m d : ℕ → ℝ) : Prop :=
  ∃ C : point → ℝ, field C (m 0) ∧
    (∀ j : ℕ, C (8*(j:ℝ),0) = m j) ∧ (∀ j : ℕ, C (8*(j:ℝ),b) = d j)

lemma model_atom (x w b : ℝ) (s : bool) (lo : -1 ≤ x) (hi : x ≤ 1)
  (hw : 0 ≤ w) (hb : b ≠ 0) :
  model b (λ n, w*T x n) (λ n, w*((if s then (1:ℝ) else -1)*T x n)) :=
begin
  refine ⟨λ p, w*atom x s b p, _, _, _⟩,
  { simp only [T,mul_one], apply atom_field, exact hw },
  { intro n, rw [at_zero x b s n lo hi] },
  { intro n, rw [at_lag x b s n hb lo hi] },
end

lemma model_add {b : ℝ} {m d m' d' : ℕ → ℝ} (u : model b m d) (v : model b m' d') :
  model b (λ n, m n + m' n) (λ n, d n + d' n) :=
begin
  rcases u with ⟨C,hc,h0,hb⟩, rcases v with ⟨D,hd,k0,kb⟩,
  exact ⟨_, add_field hc hd, λ n, congr_arg2 (+) (h0 n) (k0 n),
    λ n, congr_arg2 (+) (hb n) (kb n)⟩,
end
#print axioms finite_centered_field
end paper_v_field
