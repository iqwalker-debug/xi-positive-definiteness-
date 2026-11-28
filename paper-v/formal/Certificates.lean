import data.real.basic
import tactic
namespace paper_v

def T (x : ℝ) : ℕ → ℝ
| 0 := 1
| 1 := x
| (n+2) := 2*x*T (n+1) - T n

def row1_minus (x : ℝ) := (89734:ℝ)*T x 0 + (-53117:ℝ)*T x 1 + (-92033:ℝ)*T x 2 + (53117:ℝ)*T x 3 + (11076:ℝ)*T x 4 + (-8757:ℝ)*T x 6

lemma row1_minus_nonnegl (x : ℝ)
  (hl : (-1:ℝ) ≤ 1*x) (hr : 1*x ≤ (0:ℝ)) :
  0 ≤ row1_minus x :=
begin
  let s := 1*x - (-1:ℝ),
  let t := (0:ℝ) - 1*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 20*s^0*t^6 + 931224*s^1*t^5 + 2438420*s^2*t^4 + 4223012*s^3*t^3 + 3656040*s^4*t^2 + 1422068*s^5*t^1 + 201600*s^6*t^0 := by positivity,
  have e : 20*s^0*t^6 + 931224*s^1*t^5 + 2438420*s^2*t^4 + 4223012*s^3*t^3 + 3656040*s^4*t^2 + 1422068*s^5*t^1 + 201600*s^6*t^0 = 1 * row1_minus x := by dsimp [s,t,row1_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_minus_nonnegrl (x : ℝ)
  (hl : (0:ℝ) ≤ 2*x) (hr : 2*x ≤ (1:ℝ)) :
  0 ≤ row1_minus x :=
begin
  let s := 2*x - (0:ℝ),
  let t := (1:ℝ) - 2*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 12902400*s^0*t^6 + 70615424*s^1*t^5 + 152656320*s^2*t^4 + 164218784*s^3*t^3 + 91372448*s^4*t^2 + 25051104*s^5*t^1 + 2673920*s^6*t^0 := by positivity,
  have e : 12902400*s^0*t^6 + 70615424*s^1*t^5 + 152656320*s^2*t^4 + 164218784*s^3*t^3 + 91372448*s^4*t^2 + 25051104*s^5*t^1 + 2673920*s^6*t^0 = 64 * row1_minus x := by dsimp [s,t,row1_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_minus_nonnegrrl (x : ℝ)
  (hl : (2:ℝ) ≤ 4*x) (hr : 4*x ≤ (3:ℝ)) :
  0 ≤ row1_minus x :=
begin
  let s := 4*x - (2:ℝ),
  let t := (3:ℝ) - 4*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 171130880*s^0*t^6 + 738542592*s^1*t^5 + 1225361408*s^2*t^4 + 972544256*s^3*t^3 + 375256704*s^4*t^2 + 65035904*s^5*t^1 + 4093536*s^6*t^0 := by positivity,
  have e : 171130880*s^0*t^6 + 738542592*s^1*t^5 + 1225361408*s^2*t^4 + 972544256*s^3*t^3 + 375256704*s^4*t^2 + 65035904*s^5*t^1 + 4093536*s^6*t^0 = 4096 * row1_minus x := by dsimp [s,t,row1_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_minus_nonnegrrrlll (x : ℝ)
  (hl : (24:ℝ) ≤ 32*x) (hr : 32*x ≤ (25:ℝ)) :
  0 ≤ row1_minus x :=
begin
  let s := 32*x - (24:ℝ),
  let t := (25:ℝ) - 32*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 1073095901184*s^0*t^6 + 5112300830720*s^1*t^5 + 9921688633344*s^2*t^4 + 10005181300736*s^3*t^3 + 5510081914880*s^4*t^2 + 1568405362176*s^5*t^1 + 181020764000*s^6*t^0 := by positivity,
  have e : 1073095901184*s^0*t^6 + 5112300830720*s^1*t^5 + 9921688633344*s^2*t^4 + 10005181300736*s^3*t^3 + 5510081914880*s^4*t^2 + 1568405362176*s^5*t^1 + 181020764000*s^6*t^0 = 1073741824 * row1_minus x := by dsimp [s,t,row1_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_minus_nonnegrrrllr (x : ℝ)
  (hl : (25:ℝ) ≤ 32*x) (hr : 32*x ≤ (26:ℝ)) :
  0 ≤ row1_minus x :=
begin
  let s := 32*x - (25:ℝ),
  let t := (26:ℝ) - 32*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 181020764000*s^0*t^6 + 603843805824*s^1*t^5 + 687274133120*s^2*t^4 + 302581771264*s^3*t^3 + 105121171968*s^4*t^2 + 118457083904*s^5*t^1 + 51466311680*s^6*t^0 := by positivity,
  have e : 181020764000*s^0*t^6 + 603843805824*s^1*t^5 + 687274133120*s^2*t^4 + 302581771264*s^3*t^3 + 105121171968*s^4*t^2 + 118457083904*s^5*t^1 + 51466311680*s^6*t^0 = 1073741824 * row1_minus x := by dsimp [s,t,row1_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_minus_nonnegrrrll (x : ℝ)
  (hl : (12:ℝ) ≤ 16*x) (hr : 16*x ≤ (13:ℝ)) :
  0 ≤ row1_minus x :=
begin
  by_cases h : 32*x ≤ (25:ℝ),
  { apply row1_minus_nonnegrrrlll x; linarith },
  { apply row1_minus_nonnegrrrllr x; linarith },
end

lemma row1_minus_nonnegrrrlr (x : ℝ)
  (hl : (13:ℝ) ≤ 16*x) (hr : 16*x ≤ (14:ℝ)) :
  0 ≤ row1_minus x :=
begin
  let s := 16*x - (13:ℝ),
  let t := (14:ℝ) - 16*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 804161120*s^0*t^6 + 10773116288*s^1*t^5 + 59605066368*s^2*t^4 + 142104613888*s^3*t^3 + 163772111360*s^4*t^2 + 90588174336*s^5*t^1 + 19284285440*s^6*t^0 := by positivity,
  have e : 804161120*s^0*t^6 + 10773116288*s^1*t^5 + 59605066368*s^2*t^4 + 142104613888*s^3*t^3 + 163772111360*s^4*t^2 + 90588174336*s^5*t^1 + 19284285440*s^6*t^0 = 16777216 * row1_minus x := by dsimp [s,t,row1_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_minus_nonnegrrrl (x : ℝ)
  (hl : (6:ℝ) ≤ 8*x) (hr : 8*x ≤ (7:ℝ)) :
  0 ≤ row1_minus x :=
begin
  by_cases h : 16*x ≤ (13:ℝ),
  { apply row1_minus_nonnegrrrll x; linarith },
  { apply row1_minus_nonnegrrrlr x; linarith },
end

lemma row1_minus_nonnegrrrr (x : ℝ)
  (hl : (7:ℝ) ≤ 8*x) (hr : 8*x ≤ (8:ℝ)) :
  0 ≤ row1_minus x :=
begin
  let s := 8*x - (7:ℝ),
  let t := (8:ℝ) - 8*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 301316960*s^0*t^6 + 2592824832*s^1*t^5 + 8450339840*s^2*t^4 + 12997924864*s^3*t^3 + 9526837248*s^4*t^2 + 2693267456*s^5*t^1 + 5242880*s^6*t^0 := by positivity,
  have e : 301316960*s^0*t^6 + 2592824832*s^1*t^5 + 8450339840*s^2*t^4 + 12997924864*s^3*t^3 + 9526837248*s^4*t^2 + 2693267456*s^5*t^1 + 5242880*s^6*t^0 = 262144 * row1_minus x := by dsimp [s,t,row1_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_minus_nonnegrrr (x : ℝ)
  (hl : (3:ℝ) ≤ 4*x) (hr : 4*x ≤ (4:ℝ)) :
  0 ≤ row1_minus x :=
begin
  by_cases h : 8*x ≤ (7:ℝ),
  { apply row1_minus_nonnegrrrl x; linarith },
  { apply row1_minus_nonnegrrrr x; linarith },
end

lemma row1_minus_nonnegrr (x : ℝ)
  (hl : (1:ℝ) ≤ 2*x) (hr : 2*x ≤ (2:ℝ)) :
  0 ≤ row1_minus x :=
begin
  by_cases h : 4*x ≤ (3:ℝ),
  { apply row1_minus_nonnegrrl x; linarith },
  { apply row1_minus_nonnegrrr x; linarith },
end

lemma row1_minus_nonnegr (x : ℝ)
  (hl : (0:ℝ) ≤ 1*x) (hr : 1*x ≤ (1:ℝ)) :
  0 ≤ row1_minus x :=
begin
  by_cases h : 2*x ≤ (1:ℝ),
  { apply row1_minus_nonnegrl x; linarith },
  { apply row1_minus_nonnegrr x; linarith },
end

lemma row1_minus_nonneg (x : ℝ)
  (hl : (-1:ℝ) ≤ 1*x) (hr : 1*x ≤ (1:ℝ)) :
  0 ≤ row1_minus x :=
begin
  by_cases h : 1*x ≤ (0:ℝ),
  { apply row1_minus_nonnegl x; linarith },
  { apply row1_minus_nonnegr x; linarith },
end

#print axioms row1_minus_nonneg
def row1_plus (x : ℝ) := (89734:ℝ)*T x 0 + (146883:ℝ)*T x 1 + (107967:ℝ)*T x 2 + (53117:ℝ)*T x 3 + (11076:ℝ)*T x 4 + (-8757:ℝ)*T x 6

lemma row1_plus_nonnegll (x : ℝ)
  (hl : (-2:ℝ) ≤ 2*x) (hr : 2*x ≤ (-1:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 2*x - (-2:ℝ),
  let t := (-1:ℝ) - 2*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 1280*s^0*t^6 + 10603008*s^1*t^5 + 23917440*s^2*t^4 + 19914656*s^3*t^3 + 7472544*s^4*t^2 + 1226208*s^5*t^1 + 72384*s^6*t^0 := by positivity,
  have e : 1280*s^0*t^6 + 10603008*s^1*t^5 + 23917440*s^2*t^4 + 19914656*s^3*t^3 + 7472544*s^4*t^2 + 1226208*s^5*t^1 + 72384*s^6*t^0 = 64 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonneglrlll (x : ℝ)
  (hl : (-8:ℝ) ≤ 16*x) (hr : 16*x ≤ (-7:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 16*x - (-8:ℝ),
  let t := (-7:ℝ) - 16*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 18975031296*s^0*t^6 + 87901077504*s^1*t^5 + 164821991424*s^2*t^4 + 159348310016*s^3*t^3 + 83359561728*s^4*t^2 + 22320410112*s^5*t^1 + 2412932960*s^6*t^0 := by positivity,
  have e : 18975031296*s^0*t^6 + 87901077504*s^1*t^5 + 164821991424*s^2*t^4 + 159348310016*s^3*t^3 + 83359561728*s^4*t^2 + 22320410112*s^5*t^1 + 2412932960*s^6*t^0 = 16777216 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonneglrllr (x : ℝ)
  (hl : (-7:ℝ) ≤ 16*x) (hr : 16*x ≤ (-6:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 16*x - (-7:ℝ),
  let t := (-6:ℝ) - 16*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 2412932960*s^0*t^6 + 6634785408*s^1*t^5 + 4931438208*s^2*t^4 + 781052928*s^3*t^3 + 2832714240*s^4*t^2 + 4363462656*s^5*t^1 + 1601935360*s^6*t^0 := by positivity,
  have e : 2412932960*s^0*t^6 + 6634785408*s^1*t^5 + 4931438208*s^2*t^4 + 781052928*s^3*t^3 + 2832714240*s^4*t^2 + 4363462656*s^5*t^1 + 1601935360*s^6*t^0 = 16777216 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonneglrll (x : ℝ)
  (hl : (-4:ℝ) ≤ 8*x) (hr : 8*x ≤ (-3:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 16*x ≤ (-7:ℝ),
  { apply row1_plus_nonneglrlll x; linarith },
  { apply row1_plus_nonneglrllr x; linarith },
end

lemma row1_plus_nonneglrlr (x : ℝ)
  (hl : (-3:ℝ) ≤ 8*x) (hr : 8*x ≤ (-2:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 8*x - (-3:ℝ),
  let t := (-2:ℝ) - 8*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 25030240*s^0*t^6 + 314186112*s^1*t^5 + 1510753920*s^2*t^4 + 3270994944*s^3*t^3 + 3509611008*s^4*t^2 + 1833547776*s^5*t^1 + 373053440*s^6*t^0 := by positivity,
  have e : 25030240*s^0*t^6 + 314186112*s^1*t^5 + 1510753920*s^2*t^4 + 3270994944*s^3*t^3 + 3509611008*s^4*t^2 + 1833547776*s^5*t^1 + 373053440*s^6*t^0 = 262144 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonneglrl (x : ℝ)
  (hl : (-2:ℝ) ≤ 4*x) (hr : 4*x ≤ (-1:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 8*x ≤ (-3:ℝ),
  { apply row1_plus_nonneglrll x; linarith },
  { apply row1_plus_nonneglrlr x; linarith },
end

lemma row1_plus_nonneglrr (x : ℝ)
  (hl : (-1:ℝ) ≤ 4*x) (hr : 4*x ≤ (0:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 4*x - (-1:ℝ),
  let t := (0:ℝ) - 4*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 5828960*s^0*t^6 + 47622912*s^1*t^5 + 146784768*s^2*t^4 + 214119168*s^3*t^3 + 154383360*s^4*t^2 + 52088832*s^5*t^1 + 6553600*s^6*t^0 := by positivity,
  have e : 5828960*s^0*t^6 + 47622912*s^1*t^5 + 146784768*s^2*t^4 + 214119168*s^3*t^3 + 154383360*s^4*t^2 + 52088832*s^5*t^1 + 6553600*s^6*t^0 = 4096 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonneglr (x : ℝ)
  (hl : (-1:ℝ) ≤ 2*x) (hr : 2*x ≤ (0:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 4*x ≤ (-1:ℝ),
  { apply row1_plus_nonneglrl x; linarith },
  { apply row1_plus_nonneglrr x; linarith },
end

lemma row1_plus_nonnegl (x : ℝ)
  (hl : (-1:ℝ) ≤ 1*x) (hr : 1*x ≤ (0:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 2*x ≤ (-1:ℝ),
  { apply row1_plus_nonnegll x; linarith },
  { apply row1_plus_nonneglr x; linarith },
end

lemma row1_plus_nonnegrlll (x : ℝ)
  (hl : (0:ℝ) ≤ 8*x) (hr : 8*x ≤ (1:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 8*x - (0:ℝ),
  let t := (1:ℝ) - 8*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 419430400*s^0*t^6 + 2108030976*s^1*t^5 + 4124590080*s^2*t^4 + 3915442176*s^3*t^3 + 1820212224*s^4*t^2 + 368885760*s^5*t^1 + 27845984*s^6*t^0 := by positivity,
  have e : 419430400*s^0*t^6 + 2108030976*s^1*t^5 + 4124590080*s^2*t^4 + 3915442176*s^3*t^3 + 1820212224*s^4*t^2 + 368885760*s^5*t^1 + 27845984*s^6*t^0 = 262144 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonnegrllrll (x : ℝ)
  (hl : (4:ℝ) ≤ 32*x) (hr : 32*x ≤ (5:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 32*x - (4:ℝ),
  let t := (5:ℝ) - 32*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 114057150464*s^0*t^6 + 477689610240*s^1*t^5 + 778319929344*s^2*t^4 + 632468627456*s^3*t^3 + 293979056640*s^4*t^2 + 99720074496*s^5*t^1 + 23521895520*s^6*t^0 := by positivity,
  have e : 114057150464*s^0*t^6 + 477689610240*s^1*t^5 + 778319929344*s^2*t^4 + 632468627456*s^3*t^3 + 293979056640*s^4*t^2 + 99720074496*s^5*t^1 + 23521895520*s^6*t^0 = 1073741824 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonnegrllrlr (x : ℝ)
  (hl : (5:ℝ) ≤ 32*x) (hr : 32*x ≤ (6:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 32*x - (5:ℝ),
  let t := (6:ℝ) - 32*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 23521895520*s^0*t^6 + 182542671744*s^1*t^5 + 708092042880*s^2*t^4 + 1494064129024*s^3*t^3 + 1706654489088*s^4*t^2 + 991894370304*s^5*t^1 + 230232463360*s^6*t^0 := by positivity,
  have e : 23521895520*s^0*t^6 + 182542671744*s^1*t^5 + 708092042880*s^2*t^4 + 1494064129024*s^3*t^3 + 1706654489088*s^4*t^2 + 991894370304*s^5*t^1 + 230232463360*s^6*t^0 = 1073741824 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonnegrllrl (x : ℝ)
  (hl : (2:ℝ) ≤ 16*x) (hr : 16*x ≤ (3:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 32*x ≤ (5:ℝ),
  { apply row1_plus_nonnegrllrll x; linarith },
  { apply row1_plus_nonnegrllrlr x; linarith },
end

lemma row1_plus_nonnegrllrr (x : ℝ)
  (hl : (3:ℝ) ≤ 16*x) (hr : 16*x ≤ (4:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 16*x - (3:ℝ),
  let t := (4:ℝ) - 16*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 3597382240*s^0*t^6 + 33756181248*s^1*t^5 + 127362021888*s^2*t^4 + 246116343808*s^3*t^3 + 257870438400*s^4*t^2 + 139638276096*s^5*t^1 + 30680678400*s^6*t^0 := by positivity,
  have e : 3597382240*s^0*t^6 + 33756181248*s^1*t^5 + 127362021888*s^2*t^4 + 246116343808*s^3*t^3 + 257870438400*s^4*t^2 + 139638276096*s^5*t^1 + 30680678400*s^6*t^0 = 16777216 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonnegrllr (x : ℝ)
  (hl : (1:ℝ) ≤ 8*x) (hr : 8*x ≤ (2:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 16*x ≤ (3:ℝ),
  { apply row1_plus_nonnegrllrl x; linarith },
  { apply row1_plus_nonnegrllrr x; linarith },
end

lemma row1_plus_nonnegrll (x : ℝ)
  (hl : (0:ℝ) ≤ 4*x) (hr : 4*x ≤ (1:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 8*x ≤ (1:ℝ),
  { apply row1_plus_nonnegrlll x; linarith },
  { apply row1_plus_nonnegrllr x; linarith },
end

lemma row1_plus_nonnegrlr (x : ℝ)
  (hl : (1:ℝ) ≤ 4*x) (hr : 4*x ≤ (2:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 4*x - (1:ℝ),
  let t := (2:ℝ) - 4*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 7490400*s^0*t^6 + 88346496*s^1*t^5 + 407068800*s^2*t^4 + 935184128*s^3*t^3 + 1138188288*s^4*t^2 + 700627968*s^5*t^1 + 171130880*s^6*t^0 := by positivity,
  have e : 7490400*s^0*t^6 + 88346496*s^1*t^5 + 407068800*s^2*t^4 + 935184128*s^3*t^3 + 1138188288*s^4*t^2 + 700627968*s^5*t^1 + 171130880*s^6*t^0 = 4096 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonnegrl (x : ℝ)
  (hl : (0:ℝ) ≤ 2*x) (hr : 2*x ≤ (1:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 4*x ≤ (1:ℝ),
  { apply row1_plus_nonnegrll x; linarith },
  { apply row1_plus_nonnegrlr x; linarith },
end

lemma row1_plus_nonnegrr (x : ℝ)
  (hl : (1:ℝ) ≤ 2*x) (hr : 2*x ≤ (2:ℝ)) :
  0 ≤ row1_plus x :=
begin
  let s := 2*x - (1:ℝ),
  let t := (2:ℝ) - 2*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 2673920*s^0*t^6 + 26235936*s^1*t^5 + 103696608*s^2*t^4 + 210143840*s^3*t^3 + 228334848*s^4*t^2 + 124207104*s^5*t^1 + 25601280*s^6*t^0 := by positivity,
  have e : 2673920*s^0*t^6 + 26235936*s^1*t^5 + 103696608*s^2*t^4 + 210143840*s^3*t^3 + 228334848*s^4*t^2 + 124207104*s^5*t^1 + 25601280*s^6*t^0 = 64 * row1_plus x := by dsimp [s,t,row1_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row1_plus_nonnegr (x : ℝ)
  (hl : (0:ℝ) ≤ 1*x) (hr : 1*x ≤ (1:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 2*x ≤ (1:ℝ),
  { apply row1_plus_nonnegrl x; linarith },
  { apply row1_plus_nonnegrr x; linarith },
end

lemma row1_plus_nonneg (x : ℝ)
  (hl : (-1:ℝ) ≤ 1*x) (hr : 1*x ≤ (1:ℝ)) :
  0 ≤ row1_plus x :=
begin
  by_cases h : 1*x ≤ (0:ℝ),
  { apply row1_plus_nonnegl x; linarith },
  { apply row1_plus_nonnegr x; linarith },
end

#print axioms row1_plus_nonneg
def row2_minus (x : ℝ) := (89470:ℝ)*T x 0 + (-48851:ℝ)*T x 1 + (-101120:ℝ)*T x 2 + (57353:ℝ)*T x 3 + (17221:ℝ)*T x 4 + (-8503:ℝ)*T x 5 + (-5551:ℝ)*T x 6

lemma row2_minus_nonnegl (x : ℝ)
  (hl : (-1:ℝ) ≤ 1*x) (hr : 1*x ≤ (0:ℝ)) :
  0 ≤ row2_minus x :=
begin
  let s := 1*x - (-1:ℝ),
  let t := (0:ℝ) - 1*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 21*s^0*t^6 + 583657*s^1*t^5 + 2400924*s^2*t^4 + 4742314*s^3*t^3 + 4077629*s^4*t^2 + 1543597*s^5*t^1 + 213362*s^6*t^0 := by positivity,
  have e : 21*s^0*t^6 + 583657*s^1*t^5 + 2400924*s^2*t^4 + 4742314*s^3*t^3 + 4077629*s^4*t^2 + 1543597*s^5*t^1 + 213362*s^6*t^0 = 1 * row2_minus x := by dsimp [s,t,row2_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_minus_nonnegrl (x : ℝ)
  (hl : (0:ℝ) ≤ 2*x) (hr : 2*x ≤ (1:ℝ)) :
  0 ≤ row2_minus x :=
begin
  let s := 2*x - (0:ℝ),
  let t := (1:ℝ) - 2*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 13655168*s^0*t^6 + 73501408*s^1*t^5 + 155640704*s^2*t^4 + 163847872*s^3*t^3 + 89502816*s^4*t^2 + 24176704*s^5*t^1 + 2549664*s^6*t^0 := by positivity,
  have e : 13655168*s^0*t^6 + 73501408*s^1*t^5 + 155640704*s^2*t^4 + 163847872*s^3*t^3 + 89502816*s^4*t^2 + 24176704*s^5*t^1 + 2549664*s^6*t^0 = 64 * row2_minus x := by dsimp [s,t,row2_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_minus_nonnegrrl (x : ℝ)
  (hl : (2:ℝ) ≤ 4*x) (hr : 4*x ≤ (3:ℝ)) :
  0 ≤ row2_minus x :=
begin
  let s := 4*x - (2:ℝ),
  let t := (3:ℝ) - 4*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 163178496*s^0*t^6 + 694951936*s^1*t^5 + 1136910336*s^2*t^4 + 888808960*s^3*t^3 + 337174400*s^4*t^2 + 57198784*s^5*t^1 + 3518816*s^6*t^0 := by positivity,
  have e : 163178496*s^0*t^6 + 694951936*s^1*t^5 + 1136910336*s^2*t^4 + 888808960*s^3*t^3 + 337174400*s^4*t^2 + 57198784*s^5*t^1 + 3518816*s^6*t^0 = 4096 * row2_minus x := by dsimp [s,t,row2_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_minus_nonnegrrrlll (x : ℝ)
  (hl : (24:ℝ) ≤ 32*x) (hr : 32*x ≤ (25:ℝ)) :
  0 ≤ row2_minus x :=
begin
  let s := 32*x - (24:ℝ),
  let t := (25:ℝ) - 32*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 922436501504*s^0*t^6 + 4352156631040*s^1*t^5 + 8350066933760*s^2*t^4 + 8306069340160*s^3*t^3 + 4501181958144*s^4*t^2 + 1258229552128*s^5*t^1 + 142769952288*s^6*t^0 := by positivity,
  have e : 922436501504*s^0*t^6 + 4352156631040*s^1*t^5 + 8350066933760*s^2*t^4 + 8306069340160*s^3*t^3 + 4501181958144*s^4*t^2 + 1258229552128*s^5*t^1 + 142769952288*s^6*t^0 = 1073741824 * row2_minus x := by dsimp [s,t,row2_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_minus_nonnegrrrllr (x : ℝ)
  (hl : (25:ℝ) ≤ 32*x) (hr : 32*x ≤ (26:ℝ)) :
  0 ≤ row2_minus x :=
begin
  let s := 32*x - (25:ℝ),
  let t := (26:ℝ) - 32*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 142769952288*s^0*t^6 + 455009875328*s^1*t^5 + 485083574144*s^2*t^4 + 217396605952*s^3*t^3 + 148442267136*s^4*t^2 + 166568351744*s^5*t^1 + 62678861824*s^6*t^0 := by positivity,
  have e : 142769952288*s^0*t^6 + 455009875328*s^1*t^5 + 485083574144*s^2*t^4 + 217396605952*s^3*t^3 + 148442267136*s^4*t^2 + 166568351744*s^5*t^1 + 62678861824*s^6*t^0 = 1073741824 * row2_minus x := by dsimp [s,t,row2_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_minus_nonnegrrrll (x : ℝ)
  (hl : (12:ℝ) ≤ 16*x) (hr : 16*x ≤ (13:ℝ)) :
  0 ≤ row2_minus x :=
begin
  by_cases h : 32*x ≤ (25:ℝ),
  { apply row2_minus_nonnegrrrlll x; linarith },
  { apply row2_minus_nonnegrrrllr x; linarith },
end

lemma row2_minus_nonnegrrrlr (x : ℝ)
  (hl : (13:ℝ) ≤ 16*x) (hr : 16*x ≤ (14:ℝ)) :
  0 ≤ row2_minus x :=
begin
  let s := 16*x - (13:ℝ),
  let t := (14:ℝ) - 16*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 979357216*s^0*t^6 + 12423168896*s^1*t^5 + 63411950976*s^2*t^4 + 144536531968*s^3*t^3 + 162190913024*s^4*t^2 + 88164300800*s^5*t^1 + 18541602816*s^6*t^0 := by positivity,
  have e : 979357216*s^0*t^6 + 12423168896*s^1*t^5 + 63411950976*s^2*t^4 + 144536531968*s^3*t^3 + 162190913024*s^4*t^2 + 88164300800*s^5*t^1 + 18541602816*s^6*t^0 = 16777216 * row2_minus x := by dsimp [s,t,row2_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_minus_nonnegrrrl (x : ℝ)
  (hl : (6:ℝ) ≤ 8*x) (hr : 8*x ≤ (7:ℝ)) :
  0 ≤ row2_minus x :=
begin
  by_cases h : 16*x ≤ (13:ℝ),
  { apply row2_minus_nonnegrrrll x; linarith },
  { apply row2_minus_nonnegrrrlr x; linarith },
end

lemma row2_minus_nonnegrrrr (x : ℝ)
  (hl : (7:ℝ) ≤ 8*x) (hr : 8*x ≤ (8:ℝ)) :
  0 ≤ row2_minus x :=
begin
  let s := 8*x - (7:ℝ),
  let t := (8:ℝ) - 8*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 289712544*s^0*t^6 + 2459691392*s^1*t^5 + 7921109504*s^2*t^4 + 12058796032*s^3*t^3 + 8758173696*s^4*t^2 + 2455666688*s^5*t^1 + 4980736*s^6*t^0 := by positivity,
  have e : 289712544*s^0*t^6 + 2459691392*s^1*t^5 + 7921109504*s^2*t^4 + 12058796032*s^3*t^3 + 8758173696*s^4*t^2 + 2455666688*s^5*t^1 + 4980736*s^6*t^0 = 262144 * row2_minus x := by dsimp [s,t,row2_minus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_minus_nonnegrrr (x : ℝ)
  (hl : (3:ℝ) ≤ 4*x) (hr : 4*x ≤ (4:ℝ)) :
  0 ≤ row2_minus x :=
begin
  by_cases h : 8*x ≤ (7:ℝ),
  { apply row2_minus_nonnegrrrl x; linarith },
  { apply row2_minus_nonnegrrrr x; linarith },
end

lemma row2_minus_nonnegrr (x : ℝ)
  (hl : (1:ℝ) ≤ 2*x) (hr : 2*x ≤ (2:ℝ)) :
  0 ≤ row2_minus x :=
begin
  by_cases h : 4*x ≤ (3:ℝ),
  { apply row2_minus_nonnegrrl x; linarith },
  { apply row2_minus_nonnegrrr x; linarith },
end

lemma row2_minus_nonnegr (x : ℝ)
  (hl : (0:ℝ) ≤ 1*x) (hr : 1*x ≤ (1:ℝ)) :
  0 ≤ row2_minus x :=
begin
  by_cases h : 2*x ≤ (1:ℝ),
  { apply row2_minus_nonnegrl x; linarith },
  { apply row2_minus_nonnegrr x; linarith },
end

lemma row2_minus_nonneg (x : ℝ)
  (hl : (-1:ℝ) ≤ 1*x) (hr : 1*x ≤ (1:ℝ)) :
  0 ≤ row2_minus x :=
begin
  by_cases h : 1*x ≤ (0:ℝ),
  { apply row2_minus_nonnegl x; linarith },
  { apply row2_minus_nonnegr x; linarith },
end

#print axioms row2_minus_nonneg
def row2_plus (x : ℝ) := (89470:ℝ)*T x 0 + (148909:ℝ)*T x 1 + (101120:ℝ)*T x 2 + (57353:ℝ)*T x 3 + (17221:ℝ)*T x 4 + (-8503:ℝ)*T x 5 + (-5551:ℝ)*T x 6

lemma row2_plus_nonnegllll (x : ℝ)
  (hl : (-8:ℝ) ≤ 8*x) (hr : 8*x ≤ (-7:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 8*x - (-8:ℝ),
  let t := (-7:ℝ) - 8*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 1179910144*s^0*t^6 + 6172803072*s^1*t^5 + 12704292864*s^2*t^4 + 13186424832*s^3*t^3 + 7261774336*s^4*t^2 + 2004329088*s^5*t^1 + 217402016*s^6*t^0 := by positivity,
  have e : 1179910144*s^0*t^6 + 6172803072*s^1*t^5 + 12704292864*s^2*t^4 + 13186424832*s^3*t^3 + 7261774336*s^4*t^2 + 2004329088*s^5*t^1 + 217402016*s^6*t^0 = 262144 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonneglllrl (x : ℝ)
  (hl : (-14:ℝ) ≤ 16*x) (hr : 16*x ≤ (-13:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 16*x - (-14:ℝ),
  let t := (-13:ℝ) - 16*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 13913729024*s^0*t^6 + 61085030400*s^1*t^5 + 104737762816*s^2*t^4 + 87698703360*s^3*t^3 + 36547516800*s^4*t^2 + 7019941248*s^5*t^1 + 604488736*s^6*t^0 := by positivity,
  have e : 13913729024*s^0*t^6 + 61085030400*s^1*t^5 + 104737762816*s^2*t^4 + 87698703360*s^3*t^3 + 36547516800*s^4*t^2 + 7019941248*s^5*t^1 + 604488736*s^6*t^0 = 16777216 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonneglllrr (x : ℝ)
  (hl : (-13:ℝ) ≤ 16*x) (hr : 16*x ≤ (-12:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 16*x - (-13:ℝ),
  let t := (-12:ℝ) - 16*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 604488736*s^0*t^6 + 233923584*s^1*t^5 + 2617428480*s^2*t^4 + 20601978880*s^3*t^3 + 39167942656*s^4*t^2 + 29468655616*s^5*t^1 + 7914520576*s^6*t^0 := by positivity,
  have e : 604488736*s^0*t^6 + 233923584*s^1*t^5 + 2617428480*s^2*t^4 + 20601978880*s^3*t^3 + 39167942656*s^4*t^2 + 29468655616*s^5*t^1 + 7914520576*s^6*t^0 = 16777216 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonneglllr (x : ℝ)
  (hl : (-7:ℝ) ≤ 8*x) (hr : 8*x ≤ (-6:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 16*x ≤ (-13:ℝ),
  { apply row2_plus_nonneglllrl x; linarith },
  { apply row2_plus_nonneglllrr x; linarith },
end

lemma row2_plus_nonneglll (x : ℝ)
  (hl : (-4:ℝ) ≤ 4*x) (hr : 4*x ≤ (-3:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 8*x ≤ (-7:ℝ),
  { apply row2_plus_nonnegllll x; linarith },
  { apply row2_plus_nonneglllr x; linarith },
end

lemma row2_plus_nonnegllr (x : ℝ)
  (hl : (-3:ℝ) ≤ 4*x) (hr : 4*x ≤ (-2:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 4*x - (-3:ℝ),
  let t := (-2:ℝ) - 4*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 1932256*s^0*t^6 + 29189696*s^1*t^5 + 158146176*s^2*t^4 + 374233600*s^3*t^3 + 427386880*s^4*t^2 + 232955904*s^5*t^1 + 48736256*s^6*t^0 := by positivity,
  have e : 1932256*s^0*t^6 + 29189696*s^1*t^5 + 158146176*s^2*t^4 + 374233600*s^3*t^3 + 427386880*s^4*t^2 + 232955904*s^5*t^1 + 48736256*s^6*t^0 = 4096 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonnegll (x : ℝ)
  (hl : (-2:ℝ) ≤ 2*x) (hr : 2*x ≤ (-1:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 4*x ≤ (-3:ℝ),
  { apply row2_plus_nonneglll x; linarith },
  { apply row2_plus_nonnegllr x; linarith },
end

lemma row2_plus_nonneglr (x : ℝ)
  (hl : (-1:ℝ) ≤ 2*x) (hr : 2*x ≤ (0:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 2*x - (-1:ℝ),
  let t := (0:ℝ) - 2*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 761504*s^0*t^6 + 6427200*s^1*t^5 + 20316640*s^2*t^4 + 29784640*s^3*t^3 + 20616384*s^4*t^2 + 6372128*s^5*t^1 + 711808*s^6*t^0 := by positivity,
  have e : 761504*s^0*t^6 + 6427200*s^1*t^5 + 20316640*s^2*t^4 + 29784640*s^3*t^3 + 20616384*s^4*t^2 + 6372128*s^5*t^1 + 711808*s^6*t^0 = 64 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonnegl (x : ℝ)
  (hl : (-1:ℝ) ≤ 1*x) (hr : 1*x ≤ (0:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 2*x ≤ (-1:ℝ),
  { apply row2_plus_nonnegll x; linarith },
  { apply row2_plus_nonneglr x; linarith },
end

lemma row2_plus_nonnegrlll (x : ℝ)
  (hl : (0:ℝ) ≤ 8*x) (hr : 8*x ≤ (1:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 8*x - (0:ℝ),
  let t := (1:ℝ) - 8*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 2915565568*s^0*t^6 + 15341682688*s^1*t^5 + 32829743104*s^2*t^4 + 36417986560*s^3*t^3 + 21984714240*s^4*t^2 + 6818332800*s^5*t^1 + 847801504*s^6*t^0 := by positivity,
  have e : 2915565568*s^0*t^6 + 15341682688*s^1*t^5 + 32829743104*s^2*t^4 + 36417986560*s^3*t^3 + 21984714240*s^4*t^2 + 6818332800*s^5*t^1 + 847801504*s^6*t^0 = 262144 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonnegrllrl (x : ℝ)
  (hl : (2:ℝ) ≤ 16*x) (hr : 16*x ≤ (3:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 16*x - (2:ℝ),
  let t := (3:ℝ) - 16*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 54259296256*s^0*t^6 + 270147016704*s^1*t^5 + 546606804480*s^2*t^4 + 572491555840*s^3*t^3 + 325485617536*s^4*t^2 + 94740171136*s^5*t^1 + 11026847776*s^6*t^0 := by positivity,
  have e : 54259296256*s^0*t^6 + 270147016704*s^1*t^5 + 546606804480*s^2*t^4 + 572491555840*s^3*t^3 + 325485617536*s^4*t^2 + 94740171136*s^5*t^1 + 11026847776*s^6*t^0 = 16777216 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonnegrllrrl (x : ℝ)
  (hl : (6:ℝ) ≤ 32*x) (hr : 32*x ≤ (7:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 32*x - (6:ℝ),
  let t := (7:ℝ) - 32*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 705718257664*s^0*t^6 + 3319778842624*s^1*t^5 + 6288120004096*s^2*t^4 + 6089746011136*s^3*t^3 + 3152719959936*s^4*t^2 + 824086487424*s^5*t^1 + 87052941856*s^6*t^0 := by positivity,
  have e : 705718257664*s^0*t^6 + 3319778842624*s^1*t^5 + 6288120004096*s^2*t^4 + 6089746011136*s^3*t^3 + 3152719959936*s^4*t^2 + 824086487424*s^5*t^1 + 87052941856*s^6*t^0 = 1073741824 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonnegrllrrr (x : ℝ)
  (hl : (7:ℝ) ≤ 32*x) (hr : 32*x ≤ (8:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 32*x - (7:ℝ),
  let t := (8:ℝ) - 32*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 87052941856*s^0*t^6 + 220548814848*s^1*t^5 + 135031597056*s^2*t^4 + 97024868352*s^3*t^3 + 380710027264*s^4*t^2 + 430033600512*s^5*t^1 + 144812539904*s^6*t^0 := by positivity,
  have e : 87052941856*s^0*t^6 + 220548814848*s^1*t^5 + 135031597056*s^2*t^4 + 97024868352*s^3*t^3 + 380710027264*s^4*t^2 + 430033600512*s^5*t^1 + 144812539904*s^6*t^0 = 1073741824 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonnegrllrr (x : ℝ)
  (hl : (3:ℝ) ≤ 16*x) (hr : 16*x ≤ (4:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 32*x ≤ (7:ℝ),
  { apply row2_plus_nonnegrllrrl x; linarith },
  { apply row2_plus_nonnegrllrrr x; linarith },
end

lemma row2_plus_nonnegrllr (x : ℝ)
  (hl : (1:ℝ) ≤ 8*x) (hr : 8*x ≤ (2:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 16*x ≤ (3:ℝ),
  { apply row2_plus_nonnegrllrl x; linarith },
  { apply row2_plus_nonnegrllrr x; linarith },
end

lemma row2_plus_nonnegrll (x : ℝ)
  (hl : (0:ℝ) ≤ 4*x) (hr : 4*x ≤ (1:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 8*x ≤ (1:ℝ),
  { apply row2_plus_nonnegrlll x; linarith },
  { apply row2_plus_nonnegrllr x; linarith },
end

lemma row2_plus_nonnegrlr (x : ℝ)
  (hl : (1:ℝ) ≤ 4*x) (hr : 4*x ≤ (2:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 4*x - (1:ℝ),
  let t := (2:ℝ) - 4*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 552416*s^0*t^6 + 16706880*s^1*t^5 + 173570944*s^2*t^4 + 580704768*s^3*t^3 + 860553216*s^4*t^2 + 591446016*s^5*t^1 + 154003456*s^6*t^0 := by positivity,
  have e : 552416*s^0*t^6 + 16706880*s^1*t^5 + 173570944*s^2*t^4 + 580704768*s^3*t^3 + 860553216*s^4*t^2 + 591446016*s^5*t^1 + 154003456*s^6*t^0 = 4096 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonnegrl (x : ℝ)
  (hl : (0:ℝ) ≤ 2*x) (hr : 2*x ≤ (1:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 4*x ≤ (1:ℝ),
  { apply row2_plus_nonnegrll x; linarith },
  { apply row2_plus_nonnegrlr x; linarith },
end

lemma row2_plus_nonnegrr (x : ℝ)
  (hl : (1:ℝ) ≤ 2*x) (hr : 2*x ≤ (2:ℝ)) :
  0 ≤ row2_plus x :=
begin
  let s := 2*x - (1:ℝ),
  let t := (2:ℝ) - 2*x,
  have hs : 0 ≤ s := sub_nonneg.mpr hl,
  have ht : 0 ≤ t := sub_nonneg.mpr hr,
  have h : 0 ≤ 2406304*s^0*t^6 + 24830784*s^1*t^5 + 101395296*s^2*t^4 + 208789056*s^3*t^3 + 227800576*s^4*t^2 + 123761184*s^5*t^1 + 25601216*s^6*t^0 := by positivity,
  have e : 2406304*s^0*t^6 + 24830784*s^1*t^5 + 101395296*s^2*t^4 + 208789056*s^3*t^3 + 227800576*s^4*t^2 + 123761184*s^5*t^1 + 25601216*s^6*t^0 = 64 * row2_plus x := by dsimp [s,t,row2_plus,T]; ring,
  rw [e] at h, linarith only [h],
end

lemma row2_plus_nonnegr (x : ℝ)
  (hl : (0:ℝ) ≤ 1*x) (hr : 1*x ≤ (1:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 2*x ≤ (1:ℝ),
  { apply row2_plus_nonnegrl x; linarith },
  { apply row2_plus_nonnegrr x; linarith },
end

lemma row2_plus_nonneg (x : ℝ)
  (hl : (-1:ℝ) ≤ 1*x) (hr : 1*x ≤ (1:ℝ)) :
  0 ≤ row2_plus x :=
begin
  by_cases h : 1*x ≤ (0:ℝ),
  { apply row2_plus_nonnegl x; linarith },
  { apply row2_plus_nonnegr x; linarith },
end

#print axioms row2_plus_nonneg

theorem covers_exactly (b1 b2 b3 b4 b5 b6 : bool) :
  ((b2 = ff ∧ b5 = ff) ∨ (b6 = ff) ∨ (b4 = ff) ∨ (b3 = ff) ∨ (b1 = ff)) ↔ ¬ ((b1 = tt ∧ b2 = tt ∧ b3 = tt ∧ b4 = tt ∧ b6 = tt) ∨ (b1 = tt ∧ b3 = tt ∧ b4 = tt ∧ b5 = tt ∧ b6 = tt)) :=
by cases b1; cases b2; cases b3; cases b4; cases b5; cases b6; dec_trivial
#print axioms covers_exactly
end paper_v
