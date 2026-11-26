// Standalone alternative enclosure. Compile with g++ -std=c++17 -O2 tangent.cpp -o tangent.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

using I = std::int64_t;
using Wide = __int128_t;
constexpr I Q = I(1) << 32;
constexpr int N = 300, R = 128, HALF = 512, BITS = 18;
constexpr std::array<int, BITS> primes{2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61};
struct Bounds { I low, high; };
struct Pair { I left = 0, right = 0; };
using Bucket = std::array<Pair,10>;

I floor_div(Wide a, I b) {
    return a < 0 ? -I((-a+b-1)/b) : I(a/b);
}
Bounds multiply(Bounds a, Bounds b) {
    return {I(Wide(a.low)*b.low/Q), I((Wide(a.high)*b.high+Q-1)/Q)};
}
Bounds power(I x, int k) {
    Bounds acc{Q,Q}, base{x,x};
    while (k) {
        if (k & 1) acc = multiply(acc,base);
        base = multiply(base,base);
        k >>= 1;
    }
    return acc;
}
int parity_mask(int n) {
    int key = 0;
    for (int i=0; i<BITS; ++i)
        while (n % primes[i] == 0) {
            n /= primes[i];
            key ^= 1<<i;
        }
    return n == 1 ? key : -1;
}
int bit_index(unsigned bit) { return __builtin_ctz(bit); }

void enclose(I a, I b, std::ofstream& out) {
    if ((a+b)%2) throw std::logic_error("Midpoint is not integral.");
    const I m=(a+b)/2, h=b-m;
    std::array<Bucket, HALF> buckets{};
    Pair fixed{};
    for (int n=1;n<=N;++n) {
        const int k=n*n, key=parity_mask(n);
        const Bounds v=power(m,k);
        const I lnum=m-I(k)*h, rnum=m+I(k)*h;
        Pair t{floor_div(Wide(n)*(lnum<0?v.high:v.low)*lnum,m),
               floor_div(Wide(n)*v.low*rnum,m)};
        if (key<0) {
            fixed.left+=2*t.left;
            fixed.right+=2*t.right;
            continue;
        }
        Pair u{n*power(a,k).high, n*power(b,k).high};
        fixed.left+=t.left-u.left;
        fixed.right+=t.right-u.right;
        int high=key>>9;
        if ((high & (high-1))!=0) throw std::logic_error("Two high primes in a smooth term.");
        const int bucket = high ? bit_index(high)+1 : 0;
        for (int low=0;low<HALF;++low) {
            const int sign=__builtin_parity(unsigned(low & key)) ? -1 : 1;
            buckets[low][bucket].left+=sign*(t.left+u.left);
            buckets[low][bucket].right+=sign*(t.right+u.right);
        }
    }
    std::array<unsigned char,HALF*HALF/8> mask{};
    for (int low=0;low<HALF;++low) {
        Pair value=fixed;
        for (auto v : buckets[low]) {
            value.left+=v.left;
            value.right+=v.right;
        }
        unsigned previous=0;
        for (int i=0;i<HALF;++i) {
            const unsigned gray=unsigned(i^(i>>1));
            if (i) {
                const unsigned flip=previous^gray;
                const Pair delta=buckets[low][1+bit_index(flip)];
                const I change=(gray & flip) ? -2 : 2;
                value.left+=change*delta.left;
                value.right+=change*delta.right;
            }
            if (value.left<0 || value.right<0) {
                const unsigned idx=(gray<<9)|unsigned(low);
                mask[idx/8]|=1u<<(idx%8);
            }
            previous=gray;
        }
    }
    out.write(reinterpret_cast<const char*>(mask.data()),mask.size());
}

int main(int argc,char** argv) {
    if (argc!=2) { std::cerr<<"Usage: tangent OUTPUT.bin\n"; return 2; }
    std::ofstream out(argv[1],std::ios::binary);
    out.exceptions(std::ios::badbit | std::ios::failbit);
    for (int octave=1;octave<17;++octave) {
        const I start=Q-(Q>>octave), step=(Q>>(octave+1))/R;
        for (int i=0;i<R;++i) enclose(start+i*step,start+(i+1)*step,out);
    }
    enclose(Q-(Q>>17),Q,out);
    out.close();
    std::cout<<16*R+1<<" interval masks written.\n";
}
