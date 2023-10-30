pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

template Num2BitsWIthSkipChecks(b) {
    signal input in;            // Input number to be converted to binary
    signal output bits[b];      // Array to store binary bits
    signal input skip_checks;   // Control to skip checks (0 to check, 1 to skip)

    var sum_of_bits = 0;                            // Initialize the decimal sum of bits
    for (var i = 0; i < b; i++) {                   // Loop through each bit position
        bits[i] <-- (in >> i) & 1;                  // Extract the i-th bit from 'in' and store it in 'bits[i]'
        bits[i] * (1 - bits[i]) === 0;              // Check if 'bits[i]' is a valid binary digit (0 or 1)
        sum_of_bits += (2 ** i) * bits[i];          // Update 'sum_of_bits' by adding the decimal value of the current bit
    }
    
    (sum_of_bits - in) * (1 - skip_checks) === 0;   // Conditional check: If 'skip_checks' is set to 0, validate the binary representation
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 * Assumes `n` bit inputs. The behavior is not well-defined if any input is more than `n`-bits long.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
 // TODO: DONE
template CheckBitLength(b) {
    assert(b < 254);                        // Check if the bit length 'b' is less than 254
    signal input in;                        // Declare input and output signals
    signal output out;

    signal bits[b];                         // Declare an array to store binary bits and initialize a variable for the sum of bits
    var sum_of_bits = 0;

    for (var i = 0; i < b; i++) {           // Loop through each bit position
        bits[i] <-- (in >> i) & 1;          // Extract the i-th bit from 'in' and store it in 'bits[i]'
        bits[i] * (1 - bits[i]) === 0;      // Check if 'bits[i]' is a valid binary digit (0 or 1)
        sum_of_bits += (2 ** i) * bits[i];  // Update 'sum_of_bits' by adding the decimal value of the current bit
    }

    component is_eq = IsEqual();            // Create a component 'is_eq' to check if 'sum_of_bits' is equal to 'in'

    is_eq.in[0] <== sum_of_bits;            // Connect inputs of 'is_eq' to 'sum_of_bits' and 'in'
    is_eq.in[1] <== in;

    out <== is_eq.out;                      // Output 'out' is connected to the output of 'is_eq'
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
 // TODO: DONE
template RightShift(b, shift) {
    assert(shift < b);                              // Check if the shift amount is less than 'b'

    signal input x;                                 // Declare input and output signals
    signal output y;

    component x_bits = Num2Bits(b);                 // Create a component 'x_bits' to convert 'x' into binary bits
    x_bits.in <== x;

    signal y_bits[ b - shift ];                     // Declare an array to store the resulting binary bits after right shift
    for (var i = 0; i < b - shift; i++) {           // Loop through each bit position after the shift
        y_bits[i] <== x_bits.bits[i + shift];       // Assign the i-th bit of 'x_bits' after the shift to 'y_bits'
    }

    component y_num = Bits2Num(b - shift);          // Create a component 'y_num' to convert 'y_bits' back into a decimal number
    y_num.bits <== y_bits;
    y <== y_num.out;                                // Assign the output 'y' with the decimal value obtained from 'y_num'
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    //// Although m_prime is P+1 bits long in no overflow case, it can be P+2 bits long
    //// in the overflow case and the constraints should not fail in either case
    component right_shift = RightShift(P+2, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

function log2(b){
    var n = 1, r = 1;
    while (n < b) {
        n *= 2;
        r++;
    }
    return r;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
 // TODO: DONE
template LeftShift(shift_bound) {
    // Declare input signals
    signal input x;                                 // The number to be left-shifted
    signal input shift;                             // The shift value
    signal input skip_checks;                       // Flag to control whether checks are skipped
    signal output y;                                // Output signal to store the result

    var n = log2(shift_bound);                      // Calculate 'n', which is the logarithm base 2 of 'shift_bound'

    // Create a component 'shift_bits' to convert 'shift' into binary bits
    component shift_bits = Num2BitsWIthSkipChecks(n);
    shift_bits.in <== shift;
    shift_bits.skip_checks <== skip_checks;

    // Create a component 'lt' to check if 'shift' is less than 'shift_bound'
    component lt = LessThan(shift_bound);
    lt.in[0] <== shift;
    lt.in[1] <== shift_bound;
    (1 - lt.out) * (1 - skip_checks) === 0;         // Perform a check to ensure 'shift' is less than 'shift_bound', but skip if 'skip_checks' is set

    // Initialize 'pow_shift' and an array of IfThenElse components 'muxes'
    var pow_shift = 1;
    component muxes[n];

    for (var i = 0; i < n; i++) {                   // Loop through each bit position
        muxes[i] = IfThenElse();
        muxes[i].cond <== shift_bits.bits[i];       // Set the condition for the mux based on the i-th bit of 'shift_bits'
        // Define the left and right inputs of the mux
        muxes[i].L <== pow_shift * (2 ** (2 ** i));
        muxes[i].R <== pow_shift;
        pow_shift = muxes[i].out;                   // Update 'pow_shift' with the output of the mux
    }
    
    component if_else = IfThenElse();
    if_else.cond <== skip_checks;
    if_else.L <== 0;
    if_else.R <== pow_shift;
    pow_shift = if_else.out;

    y <== x * pow_shift;                            // Assign the output 'y' with the result of the left shift
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    assert(b < 254);                                        // Check if 'b' is less than 254
    // Declare input and output signals
    signal input in;                                        // The input number
    signal input skip_checks;                               // Flag to control whether checks are skipped
    signal output one_hot[b];                               // One-hot encoding of the most significant non-zero bit

    // Loop through each bit position
    for (var i = 0 ; i < b; i++) {
        var temp;
        if (((1 << i) <= in) && (in < (1 << (i+1)))) {      // Check if the current bit position contains the most significant non-zero bit
            temp = 1;
        } else {
            temp = 0;
        }
        one_hot[i] <-- temp;                                // Assign 'temp' to the one-hot encoding at position 'i'
    }

    var lc;

    // Check that each one-hot bit is either 0 or 1, and count the number of ones (lc)
    for (var i = 0; i < b; i++) {
        one_hot[i] * (1 - one_hot[i]) === 0;
        lc += one_hot[i];
    }

    (lc - 1) * (1 - skip_checks) === 0;                     // Check that there is exactly one '1' in the one-hot encoding, but skip if 'skip_checks' is set

    var pow2 = 0;
    var pow21 = 0;

    for (var i = 0; i < b; i++) {                           // Calculate 'pow2' and 'pow21' based on the one-hot encoding
        pow2 += one_hot[i] * (1 << i);
        pow21 += one_hot[i] * (1 << (i+1));
    }

    component lt1 = LessThan(b+1);                          // Create a component 'lt1' to check if 'in' is less than 'pow21'
    lt1.in[0] <== in;
    lt1.in[1] <== pow21;
    ( lt1.out - 1 ) * (1 - skip_checks) === 0;              // Check that 'in' is less than 'pow21', but skip if 'skip_checks' is set

    component lt2 = LessThan(b+1);                          // Create a component 'lt2' to check if 'pow2 - 1' is less than 'in'
    lt2.in[0] <== pow2 - 1;
    lt2.in[1] <== in;
    ( lt2.out - 1 ) * (1 - skip_checks) === 0;              // Check that 'pow2 - 1' is less than 'in', but skip if 'skip_checks' is set

}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
 // TODO: DONE
template Normalize(k, p, P) {
    // Declare input signals
    signal input e;               // Exponent
    signal input m;               // Mantissa
    signal input skip_checks;     // Flag to control whether checks are skipped
    signal output e_out;          // Normalized exponent output
    signal output m_out;          // Normalized mantissa output

    // Check that 'P' is greater than 'p'
    assert(P > p);

    // Create a component 'msnzb' to find the Most Significant Non-Zero Bit in 'm'
    component msnzb = MSNZB(P + 1);
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;

    // Initialize variables 'ell' and 'l'
    var ell, l;

    // Loop through each bit position
    for (var i = 0; i < P + 1; i++) {
        // Calculate 'ell' based on the one-hot encoding from 'msnzb'
        ell += msnzb.one_hot[i] * i;

        // Calculate 'l' based on the one-hot encoding from 'msnzb'
        l += msnzb.one_hot[i] * (1 << (P - i));
    }

    // Calculate the normalized mantissa 'm_out'
    m_out <== m * l;

    // Calculate the normalized exponent 'e_out'
    e_out <== e + ell - p;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */

 // TODO: DONE
template FloatAdd(k, p) {
    // Declare input signals for exponents and mantissas of the two numbers
    signal input e[2];
    signal input m[2];

    // Declare output signals for the resulting exponent and mantissa
    signal output e_out;
    signal output m_out;

    // Check well-formedness of the first number
    component cwf1 = CheckWellFormedness(k, p);
    cwf1.e <== e[0];
    cwf1.m <== m[0];

    // Check well-formedness of the second number
    component cwf2 = CheckWellFormedness(k, p);
    cwf2.e <== e[1];
    cwf2.m <== m[1];

    // Calculate the magnitude of the first and second numbers
    signal mag1 <== (e[0] * (1 << (p + 1))) + m[0];
    signal mag2 <== (e[1] * (1 << (p + 1))) + m[1];

    // Compare the magnitudes to determine which number is larger
    component lt = LessThan(k + p + 2);
    lt.in[0] <== mag2;
    lt.in[1] <== mag1;

    // Create arrays for the input exponents and mantissas
    var input1[2] = [e[0], m[0]];
    var input2[2] = [e[1], m[1]];

    // Create a switcher component for selecting inputs based on the comparison result
    component switcher[2];

    for (var i = 0; i < 2; i++) {
        switcher[i] = Switcher();
        switcher[i].L <== input1[i];
        switcher[i].R <== input2[i];
        switcher[i].sel <== lt.out;
    }

    // Select the appropriate exponents based on the comparison result
    signal alpha_e <== switcher[0].outR;
    signal beta_e <== switcher[0].outL;

    // Select the appropriate mantissas based on the comparison result
    signal alpha_m <== switcher[1].outR;
    signal beta_m <== switcher[1].outL;

    // Calculate the difference in exponents
    signal diff <-- alpha_e - beta_e;

    // Check if the difference is greater than 'p'
    component lt1 = LessThan(k);
    lt1.in[0] <== (p+1);
    lt1.in[1] <== diff;

    // Determine if 'p+1' is less than 'diff' (greater_than = 1) or not (greater_than = 0)
    signal greater_than <== lt1.out;

    // Check if the exponent 'alpha_e' is zero
    component iz = IsZero();
    iz.in <== alpha_e;

    // Check if either 'alpha_e' is zero or 'p+1' is less than 'diff'
    component or = OR();
    or.a <== iz.out;
    or.b <== greater_than;

    // Determine the 'cond' based on the OR condition
    signal cond <== or.out;

    // Perform left shift on 'alpha_m' by 'diff'
    component lshift = LeftShift(p + 2);
    lshift.x <== alpha_m;
    lshift.shift <== diff;
    lshift.skip_checks <== cond;
    
    // Calculate 'alpha_m2' after left shift
    signal alpha_m2 <== lshift.y ;

    // Calculate the new mantissa 'm2' as the sum of 'alpha_m2' and 'beta_m'
    signal m2 <== alpha_m2 + beta_m;

    // Normalize the result 'm2' with exponent 'beta_e'
    component normalize = Normalize(k, p, 2*p + 1);
    normalize.m <== m2;
    normalize.e <== beta_e;
    normalize.skip_checks <== cond;

    // Round and check the result with appropriate rounding checks
    component round = RoundAndCheck(k, p, 2*p + 1);
    round.e <== normalize.e_out;
    round.m <== normalize.m_out;

    // Assign the final result based on the 'cond' value
    e_out <-- cond ? alpha_e : round.e_out;
    m_out <-- cond ? alpha_m : round.m_out;
}
