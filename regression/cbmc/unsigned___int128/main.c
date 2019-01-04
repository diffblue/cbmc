#ifndef __GNUC__
void reduce()
{
}
#else
# include <stdint.h>

typedef unsigned __int128 uint128_t;

typedef uint64_t limb;
typedef uint128_t widelimb;

typedef limb felem[4];
typedef widelimb widefelem[7];

felem p = {0x1FFFFFFFFFFFFFF,
           0xFFFFFFFFFFFFFF,
           0xFFFFE000000000,
           0x00000000000002};


/*-
 * Reduce seven 128-bit coefficients to four 64-bit coefficients.
 * Requires in[i] < 2^126,
 * ensures out[0] < 2^56, out[1] < 2^56, out[2] < 2^56, out[3] <= 2^56 + 2^16 */
void reduce(
    limb out0, limb out1, limb out2, limb out3, widelimb in0, widelimb in1,
    widelimb in2, widelimb in3, widelimb in4, widelimb in5, widelimb in6)
{
    felem out = {out0, out1, out2, out3};
    const widefelem in = {in0, in1, in2, in3, in4, in5, in6};

    __CPROVER_assume(in[0]<(widelimb)((widelimb)1<<126));
    __CPROVER_assume(in[1]<((widelimb)1<<126));
    __CPROVER_assume(in[2]<((widelimb)1<<126));
    __CPROVER_assume(in[3]<((widelimb)1<<126));
    __CPROVER_assume(in[4]<((widelimb)1<<126));
    __CPROVER_assume(in[5]<((widelimb)1<<126));
    __CPROVER_assume(in[6]<((widelimb)1<<126));

    static const widelimb two127p15 = (((widelimb) 1) << 127) +
        (((widelimb) 1) << 15);
    static const widelimb two127m71 = (((widelimb) 1) << 127) -
        (((widelimb) 1) << 71);
    static const widelimb two127m71m55 = (((widelimb) 1) << 127) -
        (((widelimb) 1) << 71) - (((widelimb) 1) << 55);
    widelimb output[5];

    /* Add 0 mod 2^224-2^96+1 to ensure all differences are positive */
    output[0] = in[0] + two127p15;
    output[1] = in[1] + two127m71m55;
    output[2] = in[2] + two127m71;
    output[3] = in[3];
    output[4] = in[4];

    /* Eliminate in[4], in[5], in[6] */
    output[4] += in[6] >> 16;
    output[3] += (in[6] & 0xffff) << 40;
    output[2] -= in[6];

    output[3] += in[5] >> 16;
    output[2] += (in[5] & 0xffff) << 40;
    output[1] -= in[5];

    output[2] += output[4] >> 16;
    output[1] += (output[4] & 0xffff) << 40;
    output[0] -= output[4];

    /* Carry 2 -> 3 -> 4 */
    output[3] += output[2] >> 56;
    output[2] &= 0x00ffffffffffffff;

    output[4] = output[3] >> 56;
    output[3] &= 0x00ffffffffffffff;

    /* Now output[2] < 2^56, output[3] < 2^56, output[4] < 2^72 */

    /* Eliminate output[4] */
    output[2] += output[4] >> 16;
    /* output[2] < 2^56 + 2^56 = 2^57 */
    output[1] += (output[4] & 0xffff) << 40;
    output[0] -= output[4];

    /* Carry 0 -> 1 -> 2 -> 3 */
    output[1] += output[0] >> 56;
    out[0] = output[0] & 0x00ffffffffffffff;

    output[2] += output[1] >> 56;
    /* output[2] < 2^57 + 2^72 */

    assert(output[2] < (((widelimb)1)<<57)+(((widelimb)1)<<72));

    out[1] = output[1] & 0x00ffffffffffffff;
    output[3] += output[2] >> 56;
    /* output[3] <= 2^56 + 2^16 */
    assert(output[3] < (((widelimb)1)<<56)+(((widelimb)1)<<16));

    out[2] = output[2] & 0x00ffffffffffffff;

    /*-
     * out[0] < 2^56, out[1] < 2^56, out[2] < 2^56,
     * out[3] <= 2^56 + 2^16 (due to final carry),
     * so out < 2*p
     * p[0],p[1],p[2],p[3]
     * p = p[0] + 2**56 * p[1] ...
     *
     * out[3] < p[3] ||
     * out[3] == p[3] && (
     *
     */
    out[3] = output[3];
    assert(out[3] < p[0] ||
          (out[3] == p[0] && (
          out[2] < p[1] || (out[2]==p[1] && (out[1]<p[2] || out[1]==p[2]
          && (out[0]<p[3]))))));
}
#endif
