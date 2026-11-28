"""Generate rational interpolation witnesses. Lean checks the emitted algebra."""
from pathlib import Path

import sympy as sp

# Each entry is (eight times the spatial cosine, temporal sign).
ROWS = [
    ([1, 3, 4, 6], [(-8,1),(-8,-1),(-4,-1),(2,-1),(6,1),(7,1),(8,1)]),
    ([1, 2, 3, 4, 5], [(-8,1),(-7,-1),(-6,-1),(-1,-1),(1,-1),(2,-1),(7,1),(8,1)]),
    ([1, 2, 3, 5, 6], [(-8,-1),(-7,-1),(-4,-1),(-1,-1),(2,-1),(6,1),(7,1),(8,1)]),
    ([1, 2, 4, 5, 6], [(-8,1),(-7,-1),(-4,-1),(-1,-1),(2,-1),(4,1),(7,1),(8,1)]),
    ([2, 3, 4, 5, 6], [(-8,1),(-7,-1),(-4,-1),(-1,-1),(2,-1),(4,1),(7,1),(8,1)]),
]
CENTERS = [0, 207802, -1546, 4, 0, 0, 0]


def emit():
    lines = ["import .Field", "namespace paper_v_field", "set_option max_memory 4096", ""]
    for indices, atoms in ROWS:
        name = "design_" + "".join(map(str,indices))
        lines += [f"theorem {name} (b : ℝ) (hb : b ≠ 0)",
                  "  ("+" ".join(f"m{j}" for j in indices)+" : ℝ)"]
        for j in indices:
            c = CENTERS[j]
            lines.append(f"  (lo{j} : ({c-1}:ℝ) ≤ 1000000*m{j}) (hi{j} : 1000000*m{j} ≤ ({c+1}:ℝ))")
        claims = [f"C ({8*j},0) = m{j}" for j in indices]
        lines += ["  : ∃ C : point → ℝ, field C 1 ∧ C (0,0) = 1 ∧",
                  "    " + " ∧ ".join(claims + ["C (8,b) = 1/2", "C (16,b) = 1/2"]) + " :=","begin"]
        vars_ = [sp.Integer(1)] + [sp.Symbol(f"m{j}") for j in indices]+[sp.Rational(1,2)]*2
        cols = []
        for k,q in atoms:
            T = [sp.chebyshevt(j,sp.Rational(k,8)) for j in range(7)]
            cols.append([T[j] for j in [0,*indices]]+[q*T[1],q*T[2]])
        weights = sp.Matrix(cols).T.inv()*sp.Matrix(vars_)
        for i,((k,q),w) in enumerate(zip(atoms,weights)):
            denom = sp.ilcm(*(r.q for r in sp.Poly(w).coeffs()))
            num = str(sp.expand(w*denom))
            lines += [f"  let w{i} : ℝ := ({num})/{denom},",
                      f"  have pos{i} : 0 ≤ w{i} := by dsimp [w{i}]; linarith,",
                      f"  have a{i} := model_atom (({k}:ℝ)/8) w{i} b {'tt' if q==1 else 'ff'} (by norm_num) (by norm_num) pos{i} hb,"]
        combined = "a0"
        for i in range(1,len(atoms)):
            combined = f"(model_add {combined} a{i})"
        lines.append(f"  rcases {combined} with ⟨C, hC, h0, hd⟩,")
        expr = "+".join(f"w{i}" for i in range(len(atoms)))
        unfold = ",".join(f"w{i}" for i in range(len(atoms)))
        lines += [f"  have total : {expr} = 1 := by dsimp [{unfold}]; ring,",
                  "  refine ⟨C, _, _, "+", ".join("_" for _ in claims+["",""])+"⟩,",
                  "  { simpa only [T,mul_one,total] using hC },"]
        for j,h in [(j,"h0") for j in [0,*indices]]+[(1,"hd"),(2,"hd")]:
            lines += [f"  {{ have hz := {h} {j}, norm_num [T] at hz, rw [hz], dsimp [{unfold}]; ring }},"]
        lines += ["end",f"#print axioms {name}",""]
    # Combine all five maximal designs by restriction to any compatible subset.
    lines += ["theorem feasible_subsets (b : ℝ) (hb : b ≠ 0) (M : ℕ → ℝ) (S : set ℕ)"]
    for j in range(1,7):
        c = CENTERS[j]
        lines.append(f"  (lo{j} : ({c-1}:ℝ) ≤ 1000000*M {j}) (hi{j} : 1000000*M {j} ≤ ({c+1}:ℝ))")
    lines += ["  (grid : ∀ j ∈ S, "+" ∨ ".join(f"j = {i}" for i in range(1,7))+")",
              "  (hA : ¬ (1 ∈ S ∧ 2 ∈ S ∧ 3 ∈ S ∧ 4 ∈ S ∧ 6 ∈ S))",
              "  (hB : ¬ (1 ∈ S ∧ 3 ∈ S ∧ 4 ∈ S ∧ 5 ∈ S ∧ 6 ∈ S)) :",
              "  ∃ C : point → ℝ, field C 1 ∧ C (0,0) = 1 ∧ C (8,b) = 1/2 ∧",
              "    C (16,b) = 1/2 ∧ ∀ j ∈ S, C (8*(j:ℝ),0) = M j :=",
              "begin", "  classical,",
              "  have caseset : (2 ∉ S ∧ 5 ∉ S) ∨ 6 ∉ S ∨ 4 ∉ S ∨ 3 ∉ S ∨ 1 ∉ S := by tauto,",
              "  rcases caseset with ⟨n2,n5⟩ | n6 | n4 | n3 | n1,"]
    for indices,_ in ROWS:
        args = " ".join(f"(M {j})" for j in indices)+" "+" ".join(f"lo{j} hi{j}" for j in indices)
        names = ",".join(f"e{j}" for j in indices)
        lines += [f"  {{ rcases design_{''.join(map(str,indices))} b hb {args} with ⟨C,f,v,{names},da,db⟩,",
                  "    refine ⟨C,f,v,da,db,_⟩, intros j hj,",
                  "    rcases grid j hj with h|h|h|h|h|h; subst j,"]
        for j in range(1,7):
            proof = f"norm_num; simpa only using e{j}" if j in indices else f"exact (n{j} hj).elim"
            lines.append("    { "+proof+" },")
        lines.append("  },")
    lines += ["end", "#print axioms feasible_subsets"]
    lines += ["end paper_v_field"]
    return "\n".join(lines)+"\n"


if __name__ == "__main__":
    Path(__file__).with_name("DesignFields.lean").write_text(emit())
