"""Replay a concrete lower bound for four points and a majority with five."""
import certificate18 as c

def replay(grid):
    keys = [None]+[c.factor_mask(n) for n in range(1,c.N+1)]
    accepted = set()
    for b in grid:
        if b > 2*c.N**2:
            raise ValueError("Invalid tail regime")
        centers = [0]*c.SIZE
        error = 0
        for n, lo, hi in c.enclose_weights(b):
            if keys[n] is None:
                error += n*hi
            else:
                centers[keys[n]] += n*lo
                error += n*(hi-lo)
        error += (b*hi+1)//2
        c.hadamard(centers)
        terms, second_error = c.direct_upper_weights(b)
        for m,v in enumerate(centers):
            if v+error<0 and m not in accepted:
                upper = second_error + sum(-w if (m&k).bit_count()%2 else w for w,k in terms)
                if upper >= 0:
                    raise ArithmeticError((m,b))
                accepted.add(m)
    return len(accepted)

if __name__ == "__main__":
    for grid, expected in [((4,52,212,1100),129840),((4,52,212,695,1438),131854)]:
        count = replay(grid)
        print(f"b={grid}: {count} certified",flush=True)
        if count!=expected:
            raise SystemExit("Different witness count")
