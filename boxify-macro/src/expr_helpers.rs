use syn::{Expr, ExprCall};

pub trait ExprCallExt {
    /// Replace all parameters in the call with the given expression.
    fn replace_params(&mut self, param_replacement: Expr);
}

impl ExprCallExt for ExprCall {
    fn replace_params(&mut self, param_replacement: Expr) {
        for param in self.args.iter_mut() {
            *param = param_replacement.clone();
        }
    }
}
