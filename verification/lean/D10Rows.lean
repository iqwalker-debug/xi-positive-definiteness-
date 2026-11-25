import AxiomDraft

namespace GenesisD10Table

def retainedUnits : List ℤ := [
  1000000000000000001, 5875399905393114847, 13424219841544810227, 13396076099865968894,
  1160054622291994810, -11037035004251605374, -12959602251929494245, -8664007082024729534,
  -3757535367332790260, -49352090229069206, 1345746567701743961, 1096243040105647491,
  468753928834051682, -116625164913361197, -377066522922223500, -359443341350885813,
  -271395888666274356, -146941809176997803, -43222559154494932, 2891165055707849,
  15193525431079787, 10652198999551130, 1112303205651791, -5033757899158336, -7642577330885720,
  -7431301615053051, -4823873720125740, -2333740762226531, -830478628324186, 117770336288835,
  446924561151396, 413497713704814, 285803937786224, 129332021019953, 12591291952574,
  -35304851965606, -43070135203127, -28897841534969, -5862329427599, 9759888888460,
  18965398391040, 21464077170682, 16882459986048, 11321983957161, 7243734383560, 3715956256037,
  1188819239462, 19918590773, -352304141952, -328531623456, -112371149772, 69085964364,
  183588017698, 222976045102, 175085007924, 111613812292, 57768775504, 10122870105, -20328607182,
  -31133401293, -33491595154, -29246532126, -18640255188, -9614219872, -4046972705, -72738633,
  1844242417, 2200023683, 2018263880, 1438317649, 727208032, 235756312, -22714407, -132034959,
  -111228416, -38940461, 37006074, 105194511, 131215713, 131824608, 127746568, 107992840,
  74826787, 45198295, 26714448, 12856262, 2884548, -1597517, -3233323, -3139596, -1897849,
  -718486, 126160, 681765, 828011, 720075, 561470, 350958, 117257, -35634, -127989, -169099,
  -146536, -107651, -72153, -33346, 178, 19980, 31776, 37018, 31862, 24136, 19200, 13558, 7447,
  3480, 1278, -33, -544, -540, -369, -116, 113, 231, 296, 290, 201, 110, 34, -35, -80, -97, -108,
  -107, -84, -60, -46, -31, -16, -6, -1, 3, 4, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1,
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
  0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 1, 1
]

def omittedUnits : List ℤ := [
  1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0
]

set_option maxRecDepth 4096 in
theorem retainedUnits_sum : retainedUnits.sum = -12596367123836046 := by decide

set_option maxRecDepth 4096 in
theorem omittedUnits_sum : omittedUnits.sum = 258 := by decide

/-- An exact checker for summing entrywise real upper bounds on a common grid. -/
theorem sum_le_of_entry_bounds (d : ℝ) {xs : List ℝ} {us : List ℤ}
    (h : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / d) xs us) :
    xs.sum ≤ (us.sum : ℝ) / d := by
  induction h with
  | nil => simp
  | @cons a b as bs hab hrest ih =>
    simp only [List.sum_cons, Int.cast_add, add_div]
    exact add_le_add hab ih

theorem retained_le {xs : List ℝ}
    (h : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / 1000000000000000000) xs retainedUnits) :
    xs.sum ≤ -(125963671 : ℝ) / 10000000000 := by
  have hsum := sum_le_of_entry_bounds 1000000000000000000 h
  rw [retainedUnits_sum] at hsum
  exact hsum.trans (by norm_num)

theorem omitted_le {xs : List ℝ}
    (h : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / 1000000000000000000) xs omittedUnits) :
    xs.sum ≤ (1 : ℝ) / 1000000000 := by
  have hsum := sum_le_of_entry_bounds 1000000000000000000 h
  rw [omittedUnits_sum] at hsum
  exact hsum.trans (by norm_num)

end GenesisD10Table

#print axioms GenesisD10Table.retainedUnits_sum
#print axioms GenesisD10Table.omittedUnits_sum
#print axioms GenesisD10Table.sum_le_of_entry_bounds
#print axioms GenesisD10Table.retained_le
#print axioms GenesisD10Table.omitted_le

namespace GenesisD10Table

open GenesisD10Witness

/-- Standardized order and normalization for each entry checked by the certificate. -/
noncomputable def contributions (F : ℝ → ℝ) (s : Finset ℕ) : List ℝ :=
  s.sort.map (fun k => ((witnessPolynomial.coeff k : ℝ) * sample F k) /
    (normalization : ℝ))

theorem contributions_sum (F : ℝ → ℝ) (s : Finset ℕ) :
    (contributions F s).sum =
      (∑ k ∈ s, (witnessPolynomial.coeff k : ℝ) * sample F k) / (normalization : ℝ) := by
  rw [Finset.sum_div]
  unfold contributions
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq] <;> rfl

/-- The D10 obstruction follows from the row-wise certificate interface.
This does not assert that Lean has proved the transcendental evaluations. -/
theorem xi_not_radialPSD_d10_of_row_bounds
    (hret : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / 1000000000000000000)
      (contributions GenesisTidal.criticalXiProfile
        (witnessPolynomial.support.filter (fun k => k ≤ 293))) retainedUnits)
    (hom : List.Forall₂ (fun (x : ℝ) (u : ℤ) => x ≤ (u : ℝ) / 1000000000000000000)
      (contributions GenesisTidal.criticalXiProfile
        (witnessPolynomial.support.filter (fun k => ¬ k ≤ 293))) omittedUnits) :
    ¬ GenesisFormalV4.RadialPSD (EuclideanSpace ℝ (Fin 10)) GenesisTidal.criticalXiProfile := by
  apply xi_not_radialPSD_d10_of_enclosures
  · have h := retained_le hret
    rw [contributions_sum] at h
    exact h
  · have h := omitted_le hom
    rw [contributions_sum] at h
    exact h

end GenesisD10Table

#print axioms GenesisD10Table.contributions_sum
#print axioms GenesisD10Table.xi_not_radialPSD_d10_of_row_bounds
