pub mod ast;
pub mod bitvector;
pub mod lexer;
pub mod parser;
pub mod sat;
pub mod solver;
pub mod theories;

#[cfg(feature = "python")]
mod python;

#[cfg(feature = "python")]
use pyo3::prelude::*;

#[cfg(feature = "python")]
#[pymodule]
fn claude_smt(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<python::Solver>()?;
    Ok(())
}
