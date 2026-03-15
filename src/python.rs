use pyo3::prelude::*;
use pyo3::exceptions::PyRuntimeError;

use crate::solver::SmtSolver;

/// Python wrapper around the SMT solver.
///
/// Provides an SMT-LIB 2.6 compatible solver supporting Boolean,
/// bitvector, integer, real, and string theories.
///
/// Example usage::
///
///     from claude_smt import Solver
///     s = Solver()
///     result = s.run("(set-logic QF_LIA)")
///     result = s.run("(declare-const x Int)")
///     result = s.run("(assert (= (+ x 3) 10))")
///     result = s.run("(check-sat)")
///     assert result == ["sat"]
#[pyclass]
pub struct Solver {
    inner: SmtSolver,
}

#[pymethods]
impl Solver {
    /// Create a new SMT solver instance.
    #[new]
    fn new() -> Self {
        Solver {
            inner: SmtSolver::new(),
        }
    }

    /// Process SMT-LIB input and return a list of response strings.
    ///
    /// Each SMT-LIB command that produces output (e.g. check-sat, get-model)
    /// adds an entry to the returned list. Commands that produce no output
    /// (e.g. declare-const, assert) return an empty list.
    ///
    /// Args:
    ///     input: A string containing one or more SMT-LIB commands.
    ///
    /// Returns:
    ///     A list of response strings.
    ///
    /// Raises:
    ///     RuntimeError: If parsing or execution fails.
    #[pyo3(text_signature = "(self, input)")]
    fn run(&mut self, input: &str) -> PyResult<Vec<String>> {
        self.inner
            .process_input(input)
            .map_err(|e| PyRuntimeError::new_err(e))
    }

    /// Convenience method: declare a constant of the given sort.
    ///
    /// Args:
    ///     name: Variable name.
    ///     sort: SMT-LIB sort string (e.g. "Bool", "Int", "(_ BitVec 8)").
    #[pyo3(text_signature = "(self, name, sort)")]
    fn declare_const(&mut self, name: &str, sort: &str) -> PyResult<Vec<String>> {
        let cmd = format!("(declare-const {} {})", name, sort);
        self.run(&cmd)
    }

    /// Convenience method: assert a formula.
    ///
    /// Args:
    ///     formula: SMT-LIB term string.
    #[pyo3(text_signature = "(self, formula)")]
    fn assert_formula(&mut self, formula: &str) -> PyResult<Vec<String>> {
        let cmd = format!("(assert {})", formula);
        self.run(&cmd)
    }

    /// Check satisfiability of the current assertions.
    ///
    /// Returns:
    ///     "sat", "unsat", or "unknown".
    #[pyo3(text_signature = "(self)")]
    fn check_sat(&mut self) -> PyResult<String> {
        let results = self.run("(check-sat)")?;
        Ok(results.into_iter().next().unwrap_or_else(|| "unknown".into()))
    }

    /// Get the model after a sat result.
    ///
    /// Returns:
    ///     The model as a string in SMT-LIB format.
    #[pyo3(text_signature = "(self)")]
    fn get_model(&mut self) -> PyResult<String> {
        let results = self.run("(get-model)")?;
        Ok(results.join("\n"))
    }

    /// Push a new assertion scope.
    #[pyo3(text_signature = "(self)")]
    fn push(&mut self) -> PyResult<Vec<String>> {
        self.run("(push 1)")
    }

    /// Pop an assertion scope.
    #[pyo3(text_signature = "(self)")]
    fn pop(&mut self) -> PyResult<Vec<String>> {
        self.run("(pop 1)")
    }

    /// Reset the solver to its initial state.
    #[pyo3(text_signature = "(self)")]
    fn reset(&mut self) -> PyResult<Vec<String>> {
        self.run("(reset)")
    }

    fn __repr__(&self) -> String {
        "Solver()".to_string()
    }
}
