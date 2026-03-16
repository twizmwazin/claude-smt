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
        let false_lit = solver.get_false_lit();
        let true_lit = -false_lit;
        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width {
            let bit = (value >> i) & 1;
            if bit == 1 {
                bits.push(true_lit);
            } else {
                bits.push(false_lit);
            }
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
    /// Cached false literal to avoid creating new variables
    false_lit: Lit,
}

impl<'a> BitBlaster<'a> {
    pub fn new(solver: &'a mut SatSolver) -> Self {
        let false_lit = solver.get_false_lit();
        BitBlaster { solver, false_lit }
    }

    // === Helper: create Tseitin encoding for common gates ===

    #[inline]
    fn new_lit(&mut self) -> Lit {
        self.solver.new_var() as Lit
    }

    /// Encode: result = AND(a, b)
    #[inline]
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
    #[inline]
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
    #[inline]
    fn xor_gate(&mut self, a: Lit, b: Lit) -> Lit {
        let r = self.new_lit();
        self.solver.add_clause(vec![-r, -a, -b]);
        self.solver.add_clause(vec![-r, a, b]);
        self.solver.add_clause(vec![r, -a, b]);
        self.solver.add_clause(vec![r, a, -b]);
        r
    }

    /// Encode: result = ITE(cond, then, else)
    #[inline]
    fn ite_gate(&mut self, cond: Lit, then_lit: Lit, else_lit: Lit) -> Lit {
        let r = self.new_lit();
        self.solver.add_clause(vec![-cond, -r, then_lit]);
        self.solver.add_clause(vec![-cond, r, -then_lit]);
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
            self.solver.add_clause(vec![-a.bits[i], b.bits[i]]);
            self.solver.add_clause(vec![a.bits[i], -b.bits[i]]);
        }
    }

    /// Create a boolean literal that is true iff a == b
    pub fn eq(&mut self, a: &BitVec, b: &BitVec) -> Lit {
        assert_eq!(a.width(), b.width(), "bitvector width mismatch");
        let mut eq_bits = Vec::with_capacity(a.bits.len());
        for i in 0..a.bits.len() {
            let xor_bit = self.xor_gate(a.bits[i], b.bits[i]);
            eq_bits.push(-xor_bit); // XNOR
        }
        self.and_chain(&eq_bits)
    }

    fn and_chain(&mut self, lits: &[Lit]) -> Lit {
        if lits.len() == 1 {
            return lits[0];
        }
        // Use balanced binary tree for shorter propagation chains
        let mut current: Vec<Lit> = lits.to_vec();
        while current.len() > 1 {
            let mut next = Vec::with_capacity((current.len() + 1) / 2);
            let mut i = 0;
            while i + 1 < current.len() {
                next.push(self.and_gate(current[i], current[i + 1]));
                i += 2;
            }
            if i < current.len() {
                next.push(current[i]);
            }
            current = next;
        }
        current[0]
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

        let mut carry = self.false_lit;
        for i in 0..w {
            let (sum, new_carry) = self.full_adder(a.bits[i], b.bits[i], carry);
            bits.push(sum);
            carry = new_carry;
        }
        BitVec { bits }
    }

    pub fn bvsub(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        let neg_b = self.bvneg(b);
        self.bvadd(a, &neg_b)
    }

    pub fn bvmul(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.bits.len();
        let false_lit = self.false_lit;

        // Shift-and-add multiplication
        let zero = BitVec::from_constant(self.solver, 0, a.width());
        let mut result = zero;

        for i in 0..w {
            // partial = a & (b[i] replicated), shifted left by i
            let mut shifted_bits = Vec::with_capacity(w);
            // Lower i bits are 0
            for _ in 0..i {
                shifted_bits.push(false_lit);
            }
            // AND each bit of a with b[i], for positions that fit
            for j in 0..(w - i) {
                shifted_bits.push(self.and_gate(a.bits[j], b.bits[i]));
            }
            // Pad if needed (shouldn't be since we count exactly)
            while shifted_bits.len() < w {
                shifted_bits.push(false_lit);
            }

            let partial_bv = BitVec { bits: shifted_bits };
            result = self.bvadd(&result, &partial_bv);
        }

        result
    }

    /// Compute both quotient and remainder for unsigned division.
    /// Returns (quotient, remainder) sharing the same q,r variables so that
    /// the Euclidean property a = b*q + r always holds.
    pub fn bvdivrem(&mut self, a: &BitVec, b: &BitVec) -> (BitVec, BitVec) {
        assert_eq!(a.width(), b.width());
        let w = a.width();
        let q = BitVec::new_variable(self.solver, w);
        let r = BitVec::new_variable(self.solver, w);

        // Core constraint: a = b*q + r
        let bq = self.bvmul(b, &q);
        let bq_r = self.bvadd(&bq, &r);
        self.assert_eq(a, &bq_r);

        let zero_const = BitVec::from_constant(self.solver, 0, w);
        let b_zero = self.eq(b, &zero_const);

        // When b != 0: r < b (remainder is bounded)
        let r_lt_b = self.bvult_lit(&r, b);
        self.solver.add_clause(vec![b_zero, r_lt_b]);

        // When b == 0: q = all_ones (SMT-LIB semantics for division by zero)
        let all_ones = BitVec::from_constant(self.solver, (1u64 << w) - 1, w);
        let q_eq_ones = self.eq(&q, &all_ones);
        self.solver.add_clause(vec![-b_zero, q_eq_ones]);

        // When b == 0: r = a (SMT-LIB semantics for remainder by zero)
        let r_eq_a = self.eq(&r, a);
        self.solver.add_clause(vec![-b_zero, r_eq_a]);

        (q, r)
    }

    pub fn bvudiv(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        let (q, _r) = self.bvdivrem(a, b);
        q
    }

    pub fn bvurem(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        let (_q, r) = self.bvdivrem(a, b);
        r
    }

    pub fn bvsdiv(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width();
        let msb_idx = w as usize - 1;

        let a_neg = self.bvneg(a);
        let b_neg = self.bvneg(b);

        let a_sign = a.bits[msb_idx];
        let b_sign = b.bits[msb_idx];

        let abs_a = self.bvite(a_sign, &a_neg, a);
        let abs_b = self.bvite(b_sign, &b_neg, b);

        let q = self.bvudiv(&abs_a, &abs_b);

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

        let neg_r = self.bvneg(&r);
        self.bvite(a_sign, &neg_r, &r)
    }

    // === Shift operations ===

    pub fn bvshl(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        assert_eq!(a.width(), b.width());
        let w = a.width() as usize;
        let false_lit = self.false_lit;
        let mut result = a.clone();

        for i in 0..w {
            if (1 << i) >= w {
                let zero = BitVec {
                    bits: vec![false_lit; w],
                };
                result = self.bvite(b.bits[i], &zero, &result);
                continue;
            }
            let shift_amount = 1 << i;
            let mut shifted_bits = Vec::with_capacity(w);
            for j in 0..w {
                if j < shift_amount {
                    shifted_bits.push(false_lit);
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
        let false_lit = self.false_lit;
        let mut result = a.clone();

        for i in 0..w {
            if (1 << i) >= w {
                let zero = BitVec {
                    bits: vec![false_lit; w],
                };
                result = self.bvite(b.bits[i], &zero, &result);
                continue;
            }
            let shift_amount = 1 << i;
            let mut shifted_bits = Vec::with_capacity(w);
            for j in 0..w {
                if j + shift_amount < w {
                    shifted_bits.push(result.bits[j + shift_amount]);
                } else {
                    shifted_bits.push(false_lit);
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
                    shifted_bits.push(sign_bit);
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
        let w = a.bits.len();

        let true_lit = -self.false_lit;
        let false_lit = self.false_lit;

        let mut is_less = false_lit;
        let mut is_eq = true_lit;

        for i in (0..w).rev() {
            let a_lt_b_here = self.and_gate(-a.bits[i], b.bits[i]);
            let bits_eq = self.xor_gate(a.bits[i], b.bits[i]);
            let bits_eq = -bits_eq; // XNOR

            let eq_and_lt = self.and_gate(is_eq, a_lt_b_here);
            is_less = self.or_gate(is_less, eq_and_lt);
            is_eq = self.and_gate(is_eq, bits_eq);
        }

        is_less
    }

    pub fn bvult(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
        let lit = self.bvult_lit(a, b);
        bool_to_bv1(self.solver, lit)
    }

    pub fn bvule(&mut self, a: &BitVec, b: &BitVec) -> BitVec {
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

        let a_neg = a.bits[msb];
        let b_neg = b.bits[msb];
        let signs_differ = self.xor_gate(a_neg, b_neg);
        let ult = self.bvult_lit(a, b);

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
        let mut bits = b.bits.clone();
        bits.extend_from_slice(&a.bits);
        BitVec { bits }
    }

    pub fn extract(&mut self, high: u32, low: u32, bv: &BitVec) -> BitVec {
        let bits = bv.bits[low as usize..=high as usize].to_vec();
        BitVec { bits }
    }

    pub fn zero_extend(&mut self, n: u32, bv: &BitVec) -> BitVec {
        let false_lit = self.false_lit;
        let mut bits = bv.bits.clone();
        for _ in 0..n {
            bits.push(false_lit);
        }
        BitVec { bits }
    }

    pub fn sign_extend(&mut self, n: u32, bv: &BitVec) -> BitVec {
        let sign_bit = *bv.bits.last().unwrap();
        let mut bits = bv.bits.clone();
        // Reuse the sign bit literal directly - no need for new variables
        for _ in 0..n {
            bits.push(sign_bit);
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
        let a = BitVec::from_constant(&mut solver, 15, 4);
        let b = BitVec::from_constant(&mut solver, 1, 4);
        let mut bb = BitBlaster::new(&mut solver);
        let c = bb.bvadd(&a, &b);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(c.get_value(&solver), Some(0));
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
            let c = bb.concat(&a, &b);
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
        solver.add_clause(vec![lt]);
        assert_eq!(solver.solve(), SatResult::Unsat);
    }
}
