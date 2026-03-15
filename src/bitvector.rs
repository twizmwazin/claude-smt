//! Bitvector theory solver
//!
//! Implements bitvector operations using bit-blasting:
//! each bitvector variable of width W is represented as W Boolean variables,
//! and bitvector operations are translated to Boolean constraints (CNF clauses).

use crate::sat::{Lit, SatSolver};

/// Represents a bitvector as a sequence of SAT literals (LSB first)
#[derive(Debug, Clone)]
pub struct BitVec {
    pub bits: Vec<Lit>,
}

impl BitVec {
    pub fn width(&self) -> u32 {
        self.bits.len() as u32
    }

    /// Create a bitvector from a constant value
    pub fn from_constant(solver: &mut SatSolver, value: u64, width: u32) -> Self {
        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width {
            let bit = (value >> i) & 1;
            let v = solver.new_var();
            let lit = v as Lit;
            if bit == 1 {
                solver.add_clause(vec![lit]);
            } else {
                solver.add_clause(vec![-lit]);
            }
            bits.push(lit);
        }
        BitVec { bits }
    }

    /// Create a bitvector of fresh variables
    pub fn new_variable(solver: &mut SatSolver, width: u32) -> Self {
        let mut bits = Vec::with_capacity(width as usize);
        for _ in 0..width {
            let v = solver.new_var();
            bits.push(v as Lit);
        }
        BitVec { bits }
    }

    /// Get the value of this bitvector from the model
    pub fn get_value(&self, solver: &SatSolver) -> Option<u64> {
        let mut result: u64 = 0;
        for (i, &lit) in self.bits.iter().enumerate() {
            let v = lit.unsigned_abs();
            match solver.model_value(v) {
                Some(val) => {
                    let bit_val = if lit > 0 { val } else { !val };
                    if bit_val {
                        result |= 1u64 << i;
                    }
                }
                None => return None,
            }
        }
        Some(result)
    }
}

/// Bit-blasting operations
pub struct BitBlaster<'a> {
    solver: &'a mut SatSolver,
}

impl<'a> BitBlaster<'a> {
    pub fn new(solver: &'a mut SatSolver) -> Self {
        BitBlaster { solver }
    }

    // === Helper: create Tseitin encoding for common gates ===

    fn new_lit(&mut self) -> Lit {
        self.solver.new_var() as Lit
    }

    /// Encode: result = AND(a, b)
    fn and_gate(&mut self, a: Lit, b: Lit) -> Lit {
        let r = self.new_lit();
        // r => a: (-r OR a)
        self.solver.add_clause(vec![-r, a]);
        // r => b: (-r OR b)
        self.solver.add_clause(vec![-r, b]);
        // a AND b => r: (-a OR -b OR r)
        self.solver.add_clause(vec![-a, -b, r]);
        r
    }

    /// Encode: result = OR(a, b)
    fn or_gate(&mut self, a: Lit, b: Lit) -> Lit {
        let r = self.new_lit();
        // r => a OR b: (-r OR a OR b)
        self.solver.add_clause(vec![-r, a, b]);
        // a => r: (-a OR r)
        self.solver.add_clause(vec![-a, r]);
        // b => r: (-b OR r)
        self.solver.add_clause(vec![-b, r]);
        r
    }

    /// Encode: result = XOR(a, b)
    fn xor_gate(&mut self, a: Lit, b: Lit) -> Lit {
        let r = self.new_lit();
        // Tseitin XOR:
        // (-r OR -a OR -b) AND (-r OR a OR b) AND (r OR -a OR b) AND (r OR a OR -b)
        self.solver.add_clause(vec![-r, -a, -b]);
        self.solver.add_clause(vec![-r, a, b]);
        self.solver.add_clause(vec![r, -a, b]);
        self.solver.add_clause(vec![r, a, -b]);
        r
    }

    /// Encode: result = ITE(cond, then, else)
    fn ite_gate(&mut self, cond: Lit, then_lit: Lit, else_lit: Lit) -> Lit {
        let r = self.new_lit();
        // cond => (r <=> then)
        self.solver.add_clause(vec![-cond, -r, then_lit]);
        self.solver.add_clause(vec![-cond, r, -then_lit]);
        // !cond => (r <=> else)
        self.solver.add_clause(vec![cond, -r, else_lit]);
        self.solver.add_clause(vec![cond, r, -else_lit]);
        r
    }

    /// Full adder: (sum, carry) = a + b + cin
    fn full_adder(&mut self, a: Lit, b: Lit, cin: Lit) -> (Lit, Lit) {
        let axb = self.xor_gate(a, b);
        let sum = self.xor_gate(axb, cin);
        let ab = self.and_gate(a, b);
        let axb_c = self.and_gate(axb, cin);
        let carry = self.or_gate(ab, axb_c);
        (sum, carry)
    }

    // === Bitvector equality ===

    /// Assert a == b
    pub fn assert_eq(&mut self, a: &BitVec, b: &BitVec) {
        assert_eq!(a.width(), b.width(), "bitvector width mismatch");
        for i in 0..a.bits.len() {
            // a[i] <=> b[i]: (-a OR b) AND (a OR -b)
            self.solver.add_clause(vec![-a.bits[i], b.bits[i]]);
            self.solver.add_clause(vec![a.bits[i], -b.bits[i]]);
        }
    }

    /// Create a boolean literal that is true iff a == b
    pub fn eq(&mut self, a: &BitVec, b: &BitVec) -> Lit {
        assert_eq!(a.width(), b.width(), "bitvector width mismatch");
        let mut eq_bits = Vec::new();
        for i in 0..a.bits.len() {
            // xnor = NOT XOR
            let xor_bit = self.xor_gate(a.bits[i], b.bits[i]);
            eq_bits.push(-xor_bit); // XNOR
        }
        // AND all the equality bits together
        self.and_chain(&eq_bits)
    }

    fn and_chain(&mut self, lits: &[Lit]) -> Lit {
        if lits.len() == 1 {
            return lits[0];
        }
        let mut result = self.and_gate(lits[0], lits[1]);
        for &lit in &lits[2..] {
            result = self.and_gate(result, lit);
        }
        result
    }

    // === Bitwise operations ===

    pub fn bvnot(&mut self, a: &BitVec) -> BitVec {
        BitVec {
            bits: a.bits.iter().map(|&b| -b).collect(),
        }
    }

    pub fn bvand(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let bits: Vec<Lit> = (0..a.bits.len())
            .map(|i| self.and_gate(a.bits[i], b.bits[i]))
            .collect();
        BitVec { bits }
    }

    pub fn bvor(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let bits: Vec<Lit> = (0..a.bits.len())
            .map(|i| self.or_gate(a.bits[i], b.bits[i]))
            .collect();
        BitVec { bits }
    }

    pub fn bvxor(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let bits: Vec<Lit> = (0..a.bits.len())
            .map(|i| self.xor_gate(a.bits[i], b.bits[i]))
            .collect();
        BitVec { bits }
    }

    // === Arithmetic operations ===

    pub fn bvneg(&mut self, a: &BitVec) -> BitVec {
        let not_a = self.bvnot(a);
        let one = BitVec::from_constant(self.solver, 1, a.width());
        self.bvadd(&not_a, &one)
    }

    pub fn bvadd(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.bits.len();
        let mut bits = Vec::with_capacity(w);

        // Create a false literal for carry-in
        let false_var = self.solver.new_var();
        let false_lit = false_var as Lit;
        self.solver.add_clause(vec![-false_lit]);

        let mut carry = false_lit;
        for i in 0..w {
            let (sum, new_carry) = self.full_adder(a.bits[i], b.bits[i], carry);
            bits.push(sum);
            carry = new_carry;
        }
        // Overflow carry is discarded (modular arithmetic)
        BitVec { bits }
    }

    pub fn bvsub(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        let neg_b = self.bvneg(b);
        self.bvadd(a, &neg_b)
    }

    pub fn bvmul(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.bits.len();

        // Shift-and-add multiplication
        // Create initial zero
        let zero = BitVec::from_constant(self.solver, 0, a.width());
        let mut result = zero;

        for i in 0..w {
            // partial = a & (b[i] replicated)
            let mut partial_bits = Vec::with_capacity(w);
            for j in 0..w {
                if i + j < w {
                    partial_bits.push(self.and_gate(a.bits[j], b.bits[i]));
                }
            }

            // Shift partial left by i positions
            let mut shifted_bits = Vec::with_capacity(w);
            for _ in 0..i {
                // Lower bits are 0
                let zero_v = self.solver.new_var();
                let zero_lit = zero_v as Lit;
                self.solver.add_clause(vec![-zero_lit]);
                shifted_bits.push(zero_lit);
            }
            shifted_bits.extend_from_slice(&partial_bits);
            shifted_bits.truncate(w);
            // Pad if needed
            while shifted_bits.len() < w {
                let zero_v = self.solver.new_var();
                let zero_lit = zero_v as Lit;
                self.solver.add_clause(vec![-zero_lit]);
                shifted_bits.push(zero_lit);
            }

            let partial_bv = BitVec { bits: shifted_bits };
            result = self.bvadd(&result, &partial_bv);
        }

        result
    }

    pub fn bvudiv(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width();
        // q = a / b, r = a % b
        // Constraint: a = b * q + r AND r < b (unsigned)
        // When b = 0, result is all 1s per SMT-LIB spec
        let q = BitVec::new_variable(self.solver, w);
        let r = BitVec::new_variable(self.solver, w);

        let bq = self.bvmul(b, &q);
        let bq_r = self.bvadd(&bq, &r);
        self.assert_eq(a, &bq_r);

        // r < b (unsigned) when b != 0
        let zero_const = BitVec::from_constant(self.solver, 0, w);
        let b_zero = self.eq(b, &zero_const);
        let r_lt_b = self.bvult_lit(&r, b);

        // If b != 0, then r < b must hold
        // b_zero OR r_lt_b
        self.solver.add_clause(vec![b_zero, r_lt_b]);

        // If b == 0, q = all 1s
        let all_ones = BitVec::from_constant(self.solver, (1u64 << w) - 1, w);
        let q_eq_ones = self.eq(&q, &all_ones);
        // b_zero => q = all_ones: (-b_zero OR q_eq_ones)
        self.solver.add_clause(vec![-b_zero, q_eq_ones]);

        q
    }

    pub fn bvurem(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width();
        let q = BitVec::new_variable(self.solver, w);
        let r = BitVec::new_variable(self.solver, w);

        let bq = self.bvmul(b, &q);
        let bq_r = self.bvadd(&bq, &r);
        self.assert_eq(a, &bq_r);

        let zero_const = BitVec::from_constant(self.solver, 0, w);
        let b_zero = self.eq(b, &zero_const);
        let r_lt_b = self.bvult_lit(&r, b);
        self.solver.add_clause(vec![b_zero, r_lt_b]);

        // If b == 0, r = a (per SMT-LIB spec)
        let r_eq_a = self.eq(&r, a);
        self.solver.add_clause(vec![-b_zero, r_eq_a]);

        r
    }

    pub fn bvsdiv(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width();
        let msb_idx = w as usize - 1;

        // Signed division: convert to unsigned, divide, fix sign
        let a_neg = self.bvneg(a);
        let b_neg = self.bvneg(b);

        let a_sign = a.bits[msb_idx];
        let b_sign = b.bits[msb_idx];

        // abs(a) = a_sign ? -a : a
        let abs_a = self.bvite(a_sign, &a_neg, a);
        // abs(b) = b_sign ? -b : b
        let abs_b = self.bvite(b_sign, &b_neg, b);

        let q = self.bvudiv(&abs_a, &abs_b);

        // If signs differ, negate result
        let signs_differ = self.xor_gate(a_sign, b_sign);
        let neg_q = self.bvneg(&q);
        self.bvite(signs_differ, &neg_q, &q)
    }

    pub fn bvsrem(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width();
        let msb_idx = w as usize - 1;

        let a_neg = self.bvneg(a);
        let b_neg = self.bvneg(b);

        let a_sign = a.bits[msb_idx];
        let b_sign = b.bits[msb_idx];

        let abs_a = self.bvite(a_sign, &a_neg, a);
        let abs_b = self.bvite(b_sign, &b_neg, b);

        let r = self.bvurem(&abs_a, &abs_b);

        // Remainder has sign of dividend
        let neg_r = self.bvneg(&r);
        self.bvite(a_sign, &neg_r, &r)
    }

    // === Shift operations ===

    pub fn bvshl(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width() as usize;
        let mut result = a.clone();

        // Barrel shifter: for each bit position i in shift amount
        for i in 0..w {
            if (1 << i) >= w {
                // Shifting by >= width gives 0
                let zero = BitVec::from_constant(self.solver, 0, a.width());
                result = self.bvite(b.bits[i], &zero, &result);
                continue;
            }
            let shift_amount = 1 << i;
            let mut shifted_bits = Vec::with_capacity(w);
            for j in 0..w {
                if j < shift_amount {
                    // Fill with 0
                    let zero_v = self.solver.new_var();
                    let zero_lit = zero_v as Lit;
                    self.solver.add_clause(vec![-zero_lit]);
                    shifted_bits.push(zero_lit);
                } else {
                    shifted_bits.push(result.bits[j - shift_amount]);
                }
            }
            let shifted = BitVec { bits: shifted_bits };
            result = self.bvite(b.bits[i], &shifted, &result);
        }

        result
    }

    pub fn bvlshr(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width() as usize;
        let mut result = a.clone();

        for i in 0..w {
            if (1 << i) >= w {
                let zero = BitVec::from_constant(self.solver, 0, a.width());
                result = self.bvite(b.bits[i], &zero, &result);
                continue;
            }
            let shift_amount = 1 << i;
            let mut shifted_bits = Vec::with_capacity(w);
            for j in 0..w {
                if j + shift_amount < w {
                    shifted_bits.push(result.bits[j + shift_amount]);
                } else {
                    let zero_v = self.solver.new_var();
                    let zero_lit = zero_v as Lit;
                    self.solver.add_clause(vec![-zero_lit]);
                    shifted_bits.push(zero_lit);
                }
            }
            let shifted = BitVec { bits: shifted_bits };
            result = self.bvite(b.bits[i], &shifted, &result);
        }

        result
    }

    pub fn bvashr(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width() as usize;
        let sign_bit = a.bits[w - 1];
        let mut result = a.clone();

        for i in 0..w {
            if (1 << i) >= w {
                // Fill with sign bit
                let fill = BitVec {
                    bits: vec![sign_bit; w],
                };
                result = self.bvite(b.bits[i], &fill, &result);
                continue;
            }
            let shift_amount = 1 << i;
            let mut shifted_bits = Vec::with_capacity(w);
            for j in 0..w {
                if j + shift_amount < w {
                    shifted_bits.push(result.bits[j + shift_amount]);
                } else {
                    shifted_bits.push(sign_bit); // sign extend
                }
            }
            let shifted = BitVec { bits: shifted_bits };
            result = self.bvite(b.bits[i], &shifted, &result);
        }

        result
    }

    // === Comparison operations ===

    /// Returns a lit that is true iff a < b (unsigned)
    pub fn bvult_lit(&mut self, a: &BitVec, b: &BitVec) -> Lit {
        assert_eq!(a.width(), b.width());
        // a < b unsigned: compare from MSB to LSB
        // Iterative: maintain "is_less" and "is_equal"
        let w = a.bits.len();

        let true_v = self.solver.new_var();
        let true_lit = true_v as Lit;
        self.solver.add_clause(vec![true_lit]);

        let false_v = self.solver.new_var();
        let false_lit = false_v as Lit;
        self.solver.add_clause(vec![-false_lit]);

        let mut is_less = false_lit;
        let mut is_eq = true_lit;

        for i in (0..w).rev() {
            // At this bit position, a < b if !a[i] && b[i]
            let a_lt_b_here = self.and_gate(-a.bits[i], b.bits[i]);
            let bits_eq = self.xor_gate(a.bits[i], b.bits[i]);
            let bits_eq = -bits_eq; // XNOR

            // is_less = old_is_less OR (is_eq AND a_lt_b_here)
            let eq_and_lt = self.and_gate(is_eq, a_lt_b_here);
            is_less = self.or_gate(is_less, eq_and_lt);

            // is_eq = old_is_eq AND bits_eq
            is_eq = self.and_gate(is_eq, bits_eq);
        }

        is_less
    }

    pub fn bvult(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        let lit = self.bvult_lit(a, b);
        bool_to_bv1(self.solver, lit)
    }

    pub fn bvule(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        // a <= b  iff !(b < a)
        let b_lt_a = self.bvult_lit(b, a);
        bool_to_bv1(self.solver, -b_lt_a)
    }

    pub fn bvugt(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        self.bvult(b, a)
    }

    pub fn bvuge(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        self.bvule(b, a)
    }

    /// Signed less-than
    pub fn bvslt_lit(&mut self, a: &BitVec, b: &BitVec) -> Lit {
        assert_eq!(a.width(), b.width());
        let w = a.bits.len();
        let msb = w - 1;

        // Signed comparison:
        // If signs differ: a < b iff a is negative (a[msb] = 1, b[msb] = 0)
        // If signs same: a < b iff unsigned(a) < unsigned(b)
        let a_neg = a.bits[msb];
        let b_neg = b.bits[msb];
        let signs_differ = self.xor_gate(a_neg, b_neg);
        let ult = self.bvult_lit(a, b);

        // signs_differ ? a_neg : ult
        self.ite_gate(signs_differ, a_neg, ult)
    }

    pub fn bvslt(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        let lit = self.bvslt_lit(a, b);
        bool_to_bv1(self.solver, lit)
    }

    pub fn bvsle(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        let b_lt_a = self.bvslt_lit(b, a);
        bool_to_bv1(self.solver, -b_lt_a)
    }

    pub fn bvsgt(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        self.bvslt(b, a)
    }

    pub fn bvsge(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        self.bvsle(b, a)
    }

    // === Concat and Extract ===

    pub fn concat(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        // concat(a, b) = b is lower bits, a is upper bits
        let mut bits = b.bits.clone();
        bits.extend_from_slice(&a.bits);
        BitVec { bits }
    }

    pub fn extract(&mut self, high: u32, low: u32, bv: &BitVec) -> BitVec {
        let bits = bv.bits[low as usize..=high as usize].to_vec();
        BitVec { bits }
    }

    pub fn zero_extend(&mut self, n: u32, bv: &BitVec) -> BitVec {
        let mut bits = bv.bits.clone();
        for _ in 0..n {
            let zero_v = self.solver.new_var();
            let zero_lit = zero_v as Lit;
            self.solver.add_clause(vec![-zero_lit]);
            bits.push(zero_lit);
        }
        BitVec { bits }
    }

    pub fn sign_extend(&mut self, n: u32, bv: &BitVec) -> BitVec {
        let sign_bit = *bv.bits.last().unwrap();
        let mut bits = bv.bits.clone();
        for _ in 0..n {
            // Each extended bit equals the sign bit
            let ext = self.solver.new_var() as Lit;
            self.solver.add_clause(vec![-ext, sign_bit]);
            self.solver.add_clause(vec![ext, -sign_bit]);
            bits.push(ext);
        }
        BitVec { bits }
    }

    /// ITE on bitvectors: cond ? then : else
    fn bvite(&mut self, cond: Lit, then_bv: &BitVec, else_bv: &BitVec) -> BitVec {
        assert_eq!(then_bv.width(), else_bv.width());
        let bits: Vec<Lit> = (0..then_bv.bits.len())
            .map(|i| self.ite_gate(cond, then_bv.bits[i], else_bv.bits[i]))
            .collect();
        BitVec { bits }
    }
}

/// Convert a boolean literal to a 1-bit bitvector
fn bool_to_bv1(solver: &mut SatSolver, lit: Lit) -> BitVec {
    let v = solver.new_var();
    let r = v as Lit;
    solver.add_clause(vec![-r, lit]);
    solver.add_clause(vec![r, -lit]);
    BitVec { bits: vec![r] }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::SatResult;

    #[test]
    fn test_constant() {
        let mut solver = SatSolver::new();
        let bv = BitVec::from_constant(&mut solver, 0xA, 4);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(bv.get_value(&solver), Some(0xA));
    }

    #[test]
    fn test_add() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 3, 4);
        let b = BitVec::from_constant(&mut solver, 5, 4);
        let mut bb = BitBlaster::new(&mut solver);
        let c = bb.bvadd(&a, &b);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(c.get_value(&solver), Some(8));
    }

    #[test]
    fn test_add_overflow() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 15, 4); // 0xF
        let b = BitVec::from_constant(&mut solver, 1, 4);
        let mut bb = BitBlaster::new(&mut solver);
        let c = bb.bvadd(&a, &b);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(c.get_value(&solver), Some(0)); // overflow wraps
    }

    #[test]
    fn test_and() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 0b1100, 4);
        let b = BitVec::from_constant(&mut solver, 0b1010, 4);
        let mut bb = BitBlaster::new(&mut solver);
        let c = bb.bvand(&a, &b);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(c.get_value(&solver), Some(0b1000));
    }

    #[test]
    fn test_eq() {
        let mut solver = SatSolver::new();
        let a = BitVec::new_variable(&mut solver, 4);
        let b = BitVec::from_constant(&mut solver, 7, 4);
        let mut bb = BitBlaster::new(&mut solver);
        bb.assert_eq(&a, &b);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(a.get_value(&solver), Some(7));
    }

    #[test]
    fn test_sub() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 10, 8);
        let b = BitVec::from_constant(&mut solver, 3, 8);
        let mut bb = BitBlaster::new(&mut solver);
        let c = bb.bvsub(&a, &b);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(c.get_value(&solver), Some(7));
    }

    #[test]
    fn test_mul() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 3, 8);
        let b = BitVec::from_constant(&mut solver, 7, 8);
        let mut bb = BitBlaster::new(&mut solver);
        let c = bb.bvmul(&a, &b);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(c.get_value(&solver), Some(21));
    }

    #[test]
    fn test_concat_extract() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 0xA, 4);
        let b = BitVec::from_constant(&mut solver, 0xB, 4);
        let (c, low) = {
            let mut bb = BitBlaster::new(&mut solver);
            let c = bb.concat(&a, &b); // 0xAB
            let low = bb.extract(3, 0, &c);
            (c, low)
        };
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(c.get_value(&solver), Some(0xAB));
        assert_eq!(low.get_value(&solver), Some(0xB));
    }

    #[test]
    fn test_shl() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 0b0011, 4);
        let b = BitVec::from_constant(&mut solver, 1, 4);
        let mut bb = BitBlaster::new(&mut solver);
        let c = bb.bvshl(&a, &b);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(c.get_value(&solver), Some(0b0110));
    }

    #[test]
    fn test_ult() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 3, 4);
        let b = BitVec::from_constant(&mut solver, 5, 4);
        let mut bb = BitBlaster::new(&mut solver);
        let lt = bb.bvult_lit(&a, &b);
        // lt should be true
        solver.add_clause(vec![lt]);
        assert_eq!(solver.solve(), SatResult::Sat);
    }

    #[test]
    fn test_ult_false() {
        let mut solver = SatSolver::new();
        let a = BitVec::from_constant(&mut solver, 5, 4);
        let b = BitVec::from_constant(&mut solver, 3, 4);
        let mut bb = BitBlaster::new(&mut solver);
        let lt = bb.bvult_lit(&a, &b);
        // lt should be false, asserting it true should be UNSAT
        solver.add_clause(vec![lt]);
        assert_eq!(solver.solve(), SatResult::Unsat);
    }
}
