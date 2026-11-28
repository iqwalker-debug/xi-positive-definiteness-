import .Field
namespace paper_v_field
set_option max_memory 4096

theorem design_1346 (b : ℝ) (hb : b ≠ 0)
  (m1 m3 m4 m6 : ℝ)
  (lo1 : (207801:ℝ) ≤ 1000000*m1) (hi1 : 1000000*m1 ≤ (207803:ℝ))
  (lo3 : (3:ℝ) ≤ 1000000*m3) (hi3 : 1000000*m3 ≤ (5:ℝ))
  (lo4 : (-1:ℝ) ≤ 1000000*m4) (hi4 : 1000000*m4 ≤ (1:ℝ))
  (lo6 : (-1:ℝ) ≤ 1000000*m6) (hi6 : 1000000*m6 ≤ (1:ℝ))
  : ∃ C : point → ℝ, field C 1 ∧ C (0,0) = 1 ∧
    C (8,0) = m1 ∧ C (24,0) = m3 ∧ C (32,0) = m4 ∧ C (48,0) = m6 ∧ C (8,b) = 1/2 ∧ C (16,b) = 1/2 :=
begin
  let w0 : ℝ := (-1808474*m1 - 1965796*m3 - 541456*m4 + 342528*m6 + 448303)/997500,
  have pos0 : 0 ≤ w0 := by dsimp [w0]; linarith,
  have a0 := model_atom ((-8:ℝ)/8) w0 b tt (by norm_num) (by norm_num) pos0 hb,
  let w1 : ℝ := (566*m1 + 6864*m3 + 12304*m4 - 4352*m6 + 3923)/47500,
  have pos1 : 0 ≤ w1 := by dsimp [w1]; linarith,
  have a1 := model_atom ((-8:ℝ)/8) w1 b ff (by norm_num) (by norm_num) pos1 hb,
  let w2 : ℝ := (2894*m1 + 8476*m3 - 64*m4 - 768*m6 + 832)/7125,
  have pos2 : 0 ≤ w2 := by dsimp [w2]; linarith,
  have a2 := model_atom ((-4:ℝ)/8) w2 b ff (by norm_num) (by norm_num) pos2 hb,
  let w3 : ℝ := (101888*m1 + 105352*m3 + 36272*m4 - 20736*m6 - 15536)/35625,
  have pos3 : 0 ≤ w3 := by dsimp [w3]; linarith,
  have a3 := model_atom ((2:ℝ)/8) w3 b ff (by norm_num) (by norm_num) pos3 hb,
  let w4 : ℝ := (3744*m1 - 15624*m3 - 11664*m4 + 12032*m6 - 368)/16625,
  have pos4 : 0 ≤ w4 := by dsimp [w4]; linarith,
  have a4 := model_atom ((6:ℝ)/8) w4 b tt (by norm_num) (by norm_num) pos4 hb,
  let w5 : ℝ := (-59392*m1 - 32768*m3 - 2048*m4 - 24576*m6 + 26624)/35625,
  have pos5 : 0 ≤ w5 := by dsimp [w5]; linarith,
  have a5 := model_atom ((7:ℝ)/8) w5 b tt (by norm_num) (by norm_num) pos5 hb,
  let w6 : ℝ := (-22*m1 - 438*m3 + 32*m4 + 384*m6 + 59)/950,
  have pos6 : 0 ≤ w6 := by dsimp [w6]; linarith,
  have a6 := model_atom ((8:ℝ)/8) w6 b tt (by norm_num) (by norm_num) pos6 hb,
  rcases (model_add (model_add (model_add (model_add (model_add (model_add a0 a1) a2) a3) a4) a5) a6) with ⟨C, hC, h0, hd⟩,
  have total : w0+w1+w2+w3+w4+w5+w6 = 1 := by dsimp [w0,w1,w2,w3,w4,w5,w6]; ring,
  refine ⟨C, _, _, _, _, _, _, _, _⟩,
  { simpa only [T,mul_one,total] using hC },
  { have hz := h0 0, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6]; ring },
  { have hz := h0 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6]; ring },
  { have hz := h0 3, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6]; ring },
  { have hz := h0 4, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6]; ring },
  { have hz := h0 6, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6]; ring },
  { have hz := hd 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6]; ring },
  { have hz := hd 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6]; ring },
end
#print axioms design_1346

theorem design_12345 (b : ℝ) (hb : b ≠ 0)
  (m1 m2 m3 m4 m5 : ℝ)
  (lo1 : (207801:ℝ) ≤ 1000000*m1) (hi1 : 1000000*m1 ≤ (207803:ℝ))
  (lo2 : (-1547:ℝ) ≤ 1000000*m2) (hi2 : 1000000*m2 ≤ (-1545:ℝ))
  (lo3 : (3:ℝ) ≤ 1000000*m3) (hi3 : 1000000*m3 ≤ (5:ℝ))
  (lo4 : (-1:ℝ) ≤ 1000000*m4) (hi4 : 1000000*m4 ≤ (1:ℝ))
  (lo5 : (-1:ℝ) ≤ 1000000*m5) (hi5 : 1000000*m5 ≤ (1:ℝ))
  : ∃ C : point → ℝ, field C 1 ∧ C (0,0) = 1 ∧
    C (8,0) = m1 ∧ C (16,0) = m2 ∧ C (24,0) = m3 ∧ C (32,0) = m4 ∧ C (40,0) = m5 ∧ C (8,b) = 1/2 ∧ C (16,b) = 1/2 :=
begin
  let w0 : ℝ := (-263082*m1 + 198072*m2 - 133760*m3 - 61952*m4 - 22528*m5 + 64955)/790440,
  have pos0 : 0 ≤ w0 := by dsimp [w0]; linarith,
  have a0 := model_atom ((-8:ℝ)/8) w0 b tt (by norm_num) (by norm_num) pos0 hb,
  let w1 : ℝ := (255874*m1 - 3864*m2 + 109968*m3 + 277248*m4 - 52480*m5 - 5949)/355698,
  have pos1 : 0 ≤ w1 := by dsimp [w1]; linarith,
  have a1 := model_atom ((-7:ℝ)/8) w1 b ff (by norm_num) (by norm_num) pos1 hb,
  let w2 : ℝ := (-174158*m1 + 2464*m2 - 60960*m3 - 129664*m4 + 40448*m5 + 46875)/131740,
  have pos2 : 0 ≤ w2 := by dsimp [w2]; linarith,
  have a2 := model_atom ((-6:ℝ)/8) w2 b ff (by norm_num) (by norm_num) pos2 hb,
  let w3 : ℝ := (885188*m1 - 65184*m2 + 955680*m3 + 309504*m4 - 194048*m5 - 140370)/296415,
  have pos3 : 0 ≤ w3 := by dsimp [w3]; linarith,
  have a3 := model_atom ((-1:ℝ)/8) w3 b ff (by norm_num) (by norm_num) pos3 hb,
  let w4 : ℝ := (-110734*m1 - 5208*m2 - 103152*m3 - 24320*m4 + 13056*m5 + 23403)/13174,
  have pos4 : 0 ≤ w4 := by dsimp [w4]; linarith,
  have a4 := model_atom ((1:ℝ)/8) w4 b ff (by norm_num) (by norm_num) pos4 hb,
  let w5 : ℝ := (634942*m1 + 10752*m2 + 530592*m3 + 124032*m4 - 42496*m5 - 113427)/101628,
  have pos5 : 0 ≤ w5 := by dsimp [w5]; linarith,
  have a5 := model_atom ((2:ℝ)/8) w5 b ff (by norm_num) (by norm_num) pos5 hb,
  let w6 : ℝ := (-47616*m1 + 336*m2 - 97280*m3 - 45056*m4 - 16384*m5 + 47240)/98805,
  have pos6 : 0 ≤ w6 := by dsimp [w6]; linarith,
  have a6 := model_atom ((7:ℝ)/8) w6 b tt (by norm_num) (by norm_num) pos6 hb,
  let w7 : ℝ := (31030*m1 + 13048*m2 + 36480*m3 + 16896*m4 + 6144*m5 - 4541)/52696,
  have pos7 : 0 ≤ w7 := by dsimp [w7]; linarith,
  have a7 := model_atom ((8:ℝ)/8) w7 b tt (by norm_num) (by norm_num) pos7 hb,
  rcases (model_add (model_add (model_add (model_add (model_add (model_add (model_add a0 a1) a2) a3) a4) a5) a6) a7) with ⟨C, hC, h0, hd⟩,
  have total : w0+w1+w2+w3+w4+w5+w6+w7 = 1 := by dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring,
  refine ⟨C, _, _, _, _, _, _, _, _, _⟩,
  { simpa only [T,mul_one,total] using hC },
  { have hz := h0 0, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 3, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 4, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 5, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := hd 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := hd 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
end
#print axioms design_12345

theorem design_12356 (b : ℝ) (hb : b ≠ 0)
  (m1 m2 m3 m5 m6 : ℝ)
  (lo1 : (207801:ℝ) ≤ 1000000*m1) (hi1 : 1000000*m1 ≤ (207803:ℝ))
  (lo2 : (-1547:ℝ) ≤ 1000000*m2) (hi2 : 1000000*m2 ≤ (-1545:ℝ))
  (lo3 : (3:ℝ) ≤ 1000000*m3) (hi3 : 1000000*m3 ≤ (5:ℝ))
  (lo5 : (-1:ℝ) ≤ 1000000*m5) (hi5 : 1000000*m5 ≤ (1:ℝ))
  (lo6 : (-1:ℝ) ≤ 1000000*m6) (hi6 : 1000000*m6 ≤ (1:ℝ))
  : ∃ C : point → ℝ, field C 1 ∧ C (0,0) = 1 ∧
    C (8,0) = m1 ∧ C (16,0) = m2 ∧ C (24,0) = m3 ∧ C (40,0) = m5 ∧ C (48,0) = m6 ∧ C (8,b) = 1/2 ∧ C (16,b) = 1/2 :=
begin
  let w0 : ℝ := (-7160846*m1 + 2812340*m2 - 6892040*m3 - 1451904*m5 + 1516544*m6 + 2475291)/10467100,
  have pos0 : 0 ≤ w0 := by dsimp [w0]; linarith,
  have a0 := model_atom ((-8:ℝ)/8) w0 b ff (by norm_num) (by norm_num) pos0 hb,
  let w1 : ℝ := (-1308608*m1 - 9898880*m2 + 3690880*m3 + 9591808*m5 - 6320128*m6 + 1821408)/30279825,
  have pos1 : 0 ≤ w1 := by dsimp [w1]; linarith,
  have a1 := model_atom ((-7:ℝ)/8) w1 b ff (by norm_num) (by norm_num) pos1 hb,
  let w2 : ℝ := (14477288*m1 + 12402980*m2 + 22716320*m3 - 4338688*m5 + 529408*m6 - 1881663)/10093275,
  have pos2 : 0 ≤ w2 := by dsimp [w2]; linarith,
  have a2 := model_atom ((-4:ℝ)/8) w2 b ff (by norm_num) (by norm_num) pos2 hb,
  let w3 : ℝ := (-31728592*m1 - 31241440*m2 - 37444000*m3 + 5146112*m5 + 483328*m6 + 8048712)/14130585,
  have pos3 : 0 ≤ w3 := by dsimp [w3]; linarith,
  have a3 := model_atom ((-1:ℝ)/8) w3 b ff (by norm_num) (by norm_num) pos3 hb,
  let w4 : ℝ := (25987112*m1 + 38841620*m2 + 29346680*m3 - 3747712*m5 - 877568*m6 + 2071398)/30279825,
  have pos4 : 0 ≤ w4 := by dsimp [w4]; linarith,
  have a4 := model_atom ((2:ℝ)/8) w4 b ff (by norm_num) (by norm_num) pos4 hb,
  let w5 : ℝ := (-27464*m1 - 997340*m2 - 549560*m3 + 187264*m5 + 101376*m6 + 29414)/373825,
  have pos5 : 0 ≤ w5 := by dsimp [w5]; linarith,
  have a5 := model_atom ((6:ℝ)/8) w5 b tt (by norm_num) (by norm_num) pos5 hb,
  let w6 : ℝ := (118736*m1 + 253920*m2 + 199840*m3 - 68096*m5 - 36864*m6 - 10696)/74765,
  have pos6 : 0 ≤ w6 := by dsimp [w6]; linarith,
  have a6 := model_atom ((7:ℝ)/8) w6 b tt (by norm_num) (by norm_num) pos6 hb,
  let w7 : ℝ := (-1247838*m1 - 1451580*m2 - 1848520*m3 + 629888*m5 + 340992*m6 + 472763)/1495300,
  have pos7 : 0 ≤ w7 := by dsimp [w7]; linarith,
  have a7 := model_atom ((8:ℝ)/8) w7 b tt (by norm_num) (by norm_num) pos7 hb,
  rcases (model_add (model_add (model_add (model_add (model_add (model_add (model_add a0 a1) a2) a3) a4) a5) a6) a7) with ⟨C, hC, h0, hd⟩,
  have total : w0+w1+w2+w3+w4+w5+w6+w7 = 1 := by dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring,
  refine ⟨C, _, _, _, _, _, _, _, _, _⟩,
  { simpa only [T,mul_one,total] using hC },
  { have hz := h0 0, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 3, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 5, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 6, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := hd 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := hd 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
end
#print axioms design_12356

theorem design_12456 (b : ℝ) (hb : b ≠ 0)
  (m1 m2 m4 m5 m6 : ℝ)
  (lo1 : (207801:ℝ) ≤ 1000000*m1) (hi1 : 1000000*m1 ≤ (207803:ℝ))
  (lo2 : (-1547:ℝ) ≤ 1000000*m2) (hi2 : 1000000*m2 ≤ (-1545:ℝ))
  (lo4 : (-1:ℝ) ≤ 1000000*m4) (hi4 : 1000000*m4 ≤ (1:ℝ))
  (lo5 : (-1:ℝ) ≤ 1000000*m5) (hi5 : 1000000*m5 ≤ (1:ℝ))
  (lo6 : (-1:ℝ) ≤ 1000000*m6) (hi6 : 1000000*m6 ≤ (1:ℝ))
  : ∃ C : point → ℝ, field C 1 ∧ C (0,0) = 1 ∧
    C (8,0) = m1 ∧ C (16,0) = m2 ∧ C (32,0) = m4 ∧ C (40,0) = m5 ∧ C (48,0) = m6 ∧ C (8,b) = 1/2 ∧ C (16,b) = 1/2 :=
begin
  let w0 : ℝ := (-10660*m1 + 105994*m2 + 37336*m4 - 52480*m5 + 22656*m6 + 17439)/481140,
  have pos0 : 0 ≤ w0 := by dsimp [w0]; linarith,
  have a0 := model_atom ((-8:ℝ)/8) w0 b tt (by norm_num) (by norm_num) pos0 hb,
  let w1 : ℝ := (-24512*m1 + 9152*m2 + 2048*m4 + 13312*m5 - 12288*m6 + 12288)/76545,
  have pos1 : 0 ≤ w1 := by dsimp [w1]; linarith,
  have a1 := model_atom ((-7:ℝ)/8) w1 b ff (by norm_num) (by norm_num) pos1 hb,
  let w2 : ℝ := (-57418*m1 - 21272*m2 - 76448*m4 + 2048*m5 + 35328*m6 + 41217)/153090,
  have pos2 : 0 ≤ w2 := by dsimp [w2]; linarith,
  have a2 := model_atom ((-4:ℝ)/8) w2 b ff (by norm_num) (by norm_num) pos2 hb,
  let w3 : ℝ := (-5200*m1 - 26672*m2 + 57472*m4 - 25600*m5 - 6144*m6 + 6144)/76545,
  have pos3 : 0 ≤ w3 := by dsimp [w3]; linarith,
  have a3 := model_atom ((-1:ℝ)/8) w3 b ff (by norm_num) (by norm_num) pos3 hb,
  let w4 : ℝ := (1040*m1 - 368*m2 - 5792*m4 + 5120*m5 - 1536*m6 + 1536)/10935,
  have pos4 : 0 ≤ w4 := by dsimp [w4]; linarith,
  have a4 := model_atom ((2:ℝ)/8) w4 b ff (by norm_num) (by norm_num) pos4 hb,
  let w5 : ℝ := (576998*m1 - 216164*m2 + 491824*m4 - 291328*m5 + 272640*m6 + 8025)/1683990,
  have pos5 : 0 ≤ w5 := by dsimp [w5]; linarith,
  have a5 := model_atom ((4:ℝ)/8) w5 b tt (by norm_num) (by norm_num) pos5 hb,
  let w6 : ℝ := (10256*m1 + 6256*m2 - 12416*m4 - 4096*m5 - 6144*m6 + 6144)/31185,
  have pos6 : 0 ≤ w6 := by dsimp [w6]; linarith,
  have a6 := model_atom ((7:ℝ)/8) w6 b tt (by norm_num) (by norm_num) pos6 hb,
  let w7 : ℝ := (52*m1 + 302*m2 + 776*m4 + 256*m5 + 384*m6 + 309)/2772,
  have pos7 : 0 ≤ w7 := by dsimp [w7]; linarith,
  have a7 := model_atom ((8:ℝ)/8) w7 b tt (by norm_num) (by norm_num) pos7 hb,
  rcases (model_add (model_add (model_add (model_add (model_add (model_add (model_add a0 a1) a2) a3) a4) a5) a6) a7) with ⟨C, hC, h0, hd⟩,
  have total : w0+w1+w2+w3+w4+w5+w6+w7 = 1 := by dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring,
  refine ⟨C, _, _, _, _, _, _, _, _, _⟩,
  { simpa only [T,mul_one,total] using hC },
  { have hz := h0 0, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 4, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 5, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 6, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := hd 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := hd 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
end
#print axioms design_12456

theorem design_23456 (b : ℝ) (hb : b ≠ 0)
  (m2 m3 m4 m5 m6 : ℝ)
  (lo2 : (-1547:ℝ) ≤ 1000000*m2) (hi2 : 1000000*m2 ≤ (-1545:ℝ))
  (lo3 : (3:ℝ) ≤ 1000000*m3) (hi3 : 1000000*m3 ≤ (5:ℝ))
  (lo4 : (-1:ℝ) ≤ 1000000*m4) (hi4 : 1000000*m4 ≤ (1:ℝ))
  (lo5 : (-1:ℝ) ≤ 1000000*m5) (hi5 : 1000000*m5 ≤ (1:ℝ))
  (lo6 : (-1:ℝ) ≤ 1000000*m6) (hi6 : 1000000*m6 ≤ (1:ℝ))
  : ∃ C : point → ℝ, field C 1 ∧ C (0,0) = 1 ∧
    C (16,0) = m2 ∧ C (24,0) = m3 ∧ C (32,0) = m4 ∧ C (40,0) = m5 ∧ C (48,0) = m6 ∧ C (8,b) = 1/2 ∧ C (16,b) = 1/2 :=
begin
  let w0 : ℝ := (8391262*m2 + 1119300*m3 + 2837328*m4 - 3949120*m5 + 1488128*m6 + 1032307)/36961020,
  have pos0 : 0 ≤ w0 := by dsimp [w0]; linarith,
  have a0 := model_atom ((-8:ℝ)/8) w0 b tt (by norm_num) (by norm_num) pos0 hb,
  let w1 : ℝ := (3607104*m2 + 7280064*m3 + 244608*m4 + 3428352*m5 - 4311040*m6 + 671008)/16632459,
  have pos1 : 0 ≤ w1 := by dsimp [w1]; linarith,
  have a1 := model_atom ((-7:ℝ)/8) w1 b ff (by norm_num) (by norm_num) pos1 hb,
  let w2 : ℝ := (-138504*m2 + 2842191*m3 - 2846802*m4 + 283344*m5 + 638752*m6 + 712229)/5544153,
  have pos2 : 0 ≤ w2 := by dsimp [w2]; linarith,
  have a2 := model_atom ((-4:ℝ)/8) w2 b ff (by norm_num) (by norm_num) pos2 hb,
  let w3 : ℝ := (-9087024*m2 + 2574000*m3 + 20742624*m4 - 9081600*m5 - 2805248*m6 + 1518248)/27720765,
  have pos3 : 0 ≤ w3 := by dsimp [w3]; linarith,
  have a3 := model_atom ((-1:ℝ)/8) w3 b ff (by norm_num) (by norm_num) pos3 hb,
  let w4 : ℝ := (-5202096*m2 - 10810800*m3 - 43751424*m4 + 38142720*m5 - 9244672*m6 + 14650072)/83162295,
  have pos4 : 0 ≤ w4 := by dsimp [w4]; linarith,
  have a4 := model_atom ((2:ℝ)/8) w4 b ff (by norm_num) (by norm_num) pos4 hb,
  let w5 : ℝ := (-2148182*m2 - 4327485*m3 + 2817822*m4 - 1917040*m5 + 2471456*m6 + 1232329)/9240255,
  have pos5 : 0 ≤ w5 := by dsimp [w5]; linarith,
  have a5 := model_atom ((4:ℝ)/8) w5 b tt (by norm_num) (by norm_num) pos5 hb,
  let w6 : ℝ := (930256*m2 - 4153680*m3 - 3564576*m4 - 1519360*m5 - 884224*m6 + 2961064)/9240255,
  have pos6 : 0 ≤ w6 := by dsimp [w6]; linarith,
  have a6 := model_atom ((7:ℝ)/8) w6 b tt (by norm_num) (by norm_num) pos6 hb,
  let w7 : ℝ := (84802*m2 - 21060*m3 + 230512*m4 + 74304*m5 + 118528*m6 + 97341)/821356,
  have pos7 : 0 ≤ w7 := by dsimp [w7]; linarith,
  have a7 := model_atom ((8:ℝ)/8) w7 b tt (by norm_num) (by norm_num) pos7 hb,
  rcases (model_add (model_add (model_add (model_add (model_add (model_add (model_add a0 a1) a2) a3) a4) a5) a6) a7) with ⟨C, hC, h0, hd⟩,
  have total : w0+w1+w2+w3+w4+w5+w6+w7 = 1 := by dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring,
  refine ⟨C, _, _, _, _, _, _, _, _, _⟩,
  { simpa only [T,mul_one,total] using hC },
  { have hz := h0 0, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 3, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 4, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 5, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := h0 6, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := hd 1, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
  { have hz := hd 2, norm_num [T] at hz, rw [hz], dsimp [w0,w1,w2,w3,w4,w5,w6,w7]; ring },
end
#print axioms design_23456

theorem feasible_subsets (b : ℝ) (hb : b ≠ 0) (M : ℕ → ℝ) (S : set ℕ)
  (lo1 : (207801:ℝ) ≤ 1000000*M 1) (hi1 : 1000000*M 1 ≤ (207803:ℝ))
  (lo2 : (-1547:ℝ) ≤ 1000000*M 2) (hi2 : 1000000*M 2 ≤ (-1545:ℝ))
  (lo3 : (3:ℝ) ≤ 1000000*M 3) (hi3 : 1000000*M 3 ≤ (5:ℝ))
  (lo4 : (-1:ℝ) ≤ 1000000*M 4) (hi4 : 1000000*M 4 ≤ (1:ℝ))
  (lo5 : (-1:ℝ) ≤ 1000000*M 5) (hi5 : 1000000*M 5 ≤ (1:ℝ))
  (lo6 : (-1:ℝ) ≤ 1000000*M 6) (hi6 : 1000000*M 6 ≤ (1:ℝ))
  (grid : ∀ j ∈ S, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6)
  (hA : ¬ (1 ∈ S ∧ 2 ∈ S ∧ 3 ∈ S ∧ 4 ∈ S ∧ 6 ∈ S))
  (hB : ¬ (1 ∈ S ∧ 3 ∈ S ∧ 4 ∈ S ∧ 5 ∈ S ∧ 6 ∈ S)) :
  ∃ C : point → ℝ, field C 1 ∧ C (0,0) = 1 ∧ C (8,b) = 1/2 ∧
    C (16,b) = 1/2 ∧ ∀ j ∈ S, C (8*(j:ℝ),0) = M j :=
begin
  classical,
  have caseset : (2 ∉ S ∧ 5 ∉ S) ∨ 6 ∉ S ∨ 4 ∉ S ∨ 3 ∉ S ∨ 1 ∉ S := by tauto,
  rcases caseset with ⟨n2,n5⟩ | n6 | n4 | n3 | n1,
  { rcases design_1346 b hb (M 1) (M 3) (M 4) (M 6) lo1 hi1 lo3 hi3 lo4 hi4 lo6 hi6 with ⟨C,f,v,e1,e3,e4,e6,da,db⟩,
    refine ⟨C,f,v,da,db,_⟩, intros j hj,
    rcases grid j hj with h|h|h|h|h|h; subst j,
    { norm_num; simpa only using e1 },
    { exact (n2 hj).elim },
    { norm_num; simpa only using e3 },
    { norm_num; simpa only using e4 },
    { exact (n5 hj).elim },
    { norm_num; simpa only using e6 },
  },
  { rcases design_12345 b hb (M 1) (M 2) (M 3) (M 4) (M 5) lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 lo5 hi5 with ⟨C,f,v,e1,e2,e3,e4,e5,da,db⟩,
    refine ⟨C,f,v,da,db,_⟩, intros j hj,
    rcases grid j hj with h|h|h|h|h|h; subst j,
    { norm_num; simpa only using e1 },
    { norm_num; simpa only using e2 },
    { norm_num; simpa only using e3 },
    { norm_num; simpa only using e4 },
    { norm_num; simpa only using e5 },
    { exact (n6 hj).elim },
  },
  { rcases design_12356 b hb (M 1) (M 2) (M 3) (M 5) (M 6) lo1 hi1 lo2 hi2 lo3 hi3 lo5 hi5 lo6 hi6 with ⟨C,f,v,e1,e2,e3,e5,e6,da,db⟩,
    refine ⟨C,f,v,da,db,_⟩, intros j hj,
    rcases grid j hj with h|h|h|h|h|h; subst j,
    { norm_num; simpa only using e1 },
    { norm_num; simpa only using e2 },
    { norm_num; simpa only using e3 },
    { exact (n4 hj).elim },
    { norm_num; simpa only using e5 },
    { norm_num; simpa only using e6 },
  },
  { rcases design_12456 b hb (M 1) (M 2) (M 4) (M 5) (M 6) lo1 hi1 lo2 hi2 lo4 hi4 lo5 hi5 lo6 hi6 with ⟨C,f,v,e1,e2,e4,e5,e6,da,db⟩,
    refine ⟨C,f,v,da,db,_⟩, intros j hj,
    rcases grid j hj with h|h|h|h|h|h; subst j,
    { norm_num; simpa only using e1 },
    { norm_num; simpa only using e2 },
    { exact (n3 hj).elim },
    { norm_num; simpa only using e4 },
    { norm_num; simpa only using e5 },
    { norm_num; simpa only using e6 },
  },
  { rcases design_23456 b hb (M 2) (M 3) (M 4) (M 5) (M 6) lo2 hi2 lo3 hi3 lo4 hi4 lo5 hi5 lo6 hi6 with ⟨C,f,v,e2,e3,e4,e5,e6,da,db⟩,
    refine ⟨C,f,v,da,db,_⟩, intros j hj,
    rcases grid j hj with h|h|h|h|h|h; subst j,
    { exact (n1 hj).elim },
    { norm_num; simpa only using e2 },
    { norm_num; simpa only using e3 },
    { norm_num; simpa only using e4 },
    { norm_num; simpa only using e5 },
    { norm_num; simpa only using e6 },
  },
end
#print axioms feasible_subsets
end paper_v_field
