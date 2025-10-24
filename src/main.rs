use std::fmt;

#[derive(Copy, Debug, PartialEq, Clone)]
enum Var {
    X,
    Y,
    Z,
}

#[derive(Debug, Clone)]
enum Const {
    Numeric(i64),
    Named(String),
}

#[derive(Debug, Clone)]
enum E {
    Add(Box<E>, Box<E>),
    Neg(Box<E>),
    Mul(Box<E>, Box<E>),
    Inv(Box<E>),
    Const(Const),
    Func {name: String, arg: Box<E>},
    Var(Var),
}

impl E {
    fn add(arg1: Box<Self>, arg2:  Box<Self>) -> Box<Self> {
        Box::new(Self::Add(arg1, arg2))
    }

    fn var(arg1: Var) -> Box<Self> {
        Box::new(Self::Var(arg1))
    }

    fn constant(c: Const) -> Box<Self> {
        Box::new(Self::Const(c))
    }

    fn mul(arg1: Box<Self>, arg2:  Box<Self>) -> Box<Self> {
        Box::new(Self::Mul(arg1, arg2))
    }

    fn inv(arg1: Box<Self>) -> Box<Self> {
        Box::new(Self::Inv(arg1))
    }

    fn neg(arg1: Box<Self>) -> Box<Self> {
        Box::new(Self::Neg(arg1))
    }

    fn func(name: String, arg: Box<Self>) -> Box<Self> {
        Box::new(Self::Func { name, arg })
    }

    fn arg_count(&self) -> u32 {
        match &self {
            E::Add(_, _) | E::Mul(_, _) => 2,
            E::Const(_) | E::Var(_) => 0,
            _ => 1,
        }
    }

    fn diff(self, by: Var) -> Box<Self> {
        match self {
            Self::Add(e1, e2) => Self::add(e1.diff(by), e2.diff(by)),
            Self::Neg(e) => Self::neg(e.diff(by)),
            Self::Mul(e1, e2) => {
                let f = e1.clone();
                let g = e2.clone();
                let f_prime = e1.diff(by);
                let g_prime = e2.diff(by);
                Self::add(Self::mul(f_prime, g), Self::mul(f, g_prime))
            }
            Self::Inv(e) => {
                let f = e.clone();
                let f_prime = e.diff(by);
                let f_squared = Self::mul(f.clone(), f);
                Self::mul(Self::neg(Self::inv(f_squared)), f_prime)
            }
            Self::Const(_) => Self::constant(Const::Numeric(0)),
            Self::Var(v) => {
                if v == by {
                    Self::constant(Const::Numeric(1))
                } else {
                    Self::constant(Const::Numeric(0))
                }
            }
            Self::Func { name, arg } => {
                let f_diff = Self::func(
                    format!("{}_{}", name, by), arg.clone());
                let arg_diff = arg.diff(by);
                Self::mul(f_diff, arg_diff)
            },
        }
    }

    fn unpack_inv_inv(self) -> Option<Box<Self>> {
        let Self::Inv(in1) = self else {return None};
        let Self::Inv(in2) = *in1 else {return None};
        Some(in2)
    }

    fn uninv(mut self: Box<Self>) -> Box<Self> {
        while let Some(next) = self.clone().unpack_inv_inv() {
            self = next;
        }
        self
    }

    fn unpack_neg_neg(self) -> Option<Box<Self>> {
        if let Self::Neg(neg) = self && let Self::Neg(res) = *neg {
            return Some(res)
        }
        None
    }

    fn unneg(mut self: Box<Self>) -> Box<Self> {
        while let Some(next) = self.clone().unpack_neg_neg() {
            self = next;
        }
        self
    }

    fn substitute(self, name: &str, value: Box<Self>) -> Box<Self> {
        match self {
            Self::Add(e1, e2) => Self::add(e1.substitute(name, value.clone()),
                                           e2.substitute(name, value)),
            Self::Neg(e) => Self::neg(e.substitute(name, value)),
            Self::Mul(e1, e2) => Self::mul(e1.substitute(name, value.clone()),
                                           e2.substitute(name, value)),
            Self::Inv(e) => Self::inv(e.substitute(name, value)),
            Self::Var(v) => Self::var(v),
            Self::Func { name:n, arg } => Self::func(n, arg.substitute(name, value)),
            Self::Const(Const::Named(n)) if n == name => value,
            Self::Const(c) => Self::constant(c),
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Var::X => write!(f, "X"),
            Var::Y => write!(f, "Y"),
            Var::Z => write!(f, "Z"),
        }
    }
}

impl fmt::Display for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Const::Numeric(n) => write!(f, "{}", n),
            Const::Named(n) => write!(f, "{}", n),
        }
    }
}

impl fmt::Display for E {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            E::Add(e1, e2) => write!(f, "({} + {})", e1, e2),
            E::Neg(e) => write!(f, "-({})", e),
            E::Mul(e1, e2) => write!(f, "({} * {})", e1, e2),
            E::Inv(e) => write!(f, "1/({})", e),
            E::Const(c) => write!(f, "{}", c),
            E::Var(v) => write!(f, "{}", v),
            E::Func { name, arg } => write!(f, "{}({})", name, arg),
        }
    }
}

fn main() {
    // Creating expression
    let x = E::var(Var::X);
    let y = E::var(Var::Y);
    let a = E::constant(Const::Named(String::from("a")));

    // -(-sin(a * X))
    let ax = E::mul(a.clone(), x.clone());
    let sin_ax = E::func(String::from("sin"), ax);
    let neg_neg_sin = E::neg(E::neg(sin_ax));

    // 1/(1/Y)
    let inv_inv_y = E::inv(E::inv(y));
    println!("Expression components: {}, {}",neg_neg_sin ,inv_inv_y);

    // Simplifying components
    let simple_y = inv_inv_y.uninv();
    let simple_x = neg_neg_sin.unneg();
    println!("Simplified expression components: {}, {}", simple_x, simple_y);

    // f(X,Y) = sin(a * X) + Y
    let f = E::add(simple_x, simple_y);
    println!("Created expression: {}", f);
    println!("Number of arguments: {}", f.arg_count());

    // Derivative
    let df_dx = f.clone().diff(Var::X);
    println!("Derivative expression of X: {}", df_dx);

    // Substituting value
    let a_value = E::constant(Const::Numeric(3));
    let df_dx_substituted = df_dx.substitute("a", a_value);
    println!("Derivative with substitution: {}", df_dx_substituted);

    // Sample usage of previously not used functions
    let g = E::add(E::var(Var::Z), E::constant(Const::Numeric(100)));
    println!("Expression g = {}", g);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_to_string() {
        let c_num = Const::Numeric(42);
        let c_name = Const::Named("a".into());
        assert_eq!(c_num.to_string(), "42");
        assert_eq!(c_name.to_string(), "a");
    }

    #[test]
    fn test_var_to_string() {
        assert_eq!(Var::X.to_string(), "X");
        assert_eq!(Var::Y.to_string(), "Y");
        assert_eq!(Var::Z.to_string(), "Z");
    }

    #[test]
    fn test_builder_constant_var() {
        let e_const = E::constant(Const::Numeric(5));
        let e_var = E::var(Var::X);
        assert_eq!(e_const.to_string(), "5");
        assert_eq!(e_var.to_string(), "X");
    }

    #[test]
    fn test_builder_add() {
        let expr = E::add(E::constant(Const::Numeric(2)), E::var(Var::X));
        assert_eq!(expr.to_string(), "(2 + X)");
    }

    #[test]
    fn test_builder_neg() {
        let expr = E::neg(E::var(Var::X));
        assert_eq!(expr.to_string(), "-(X)");
    }

    #[test]
    fn test_builder_mul() {
        let expr = E::mul(E::var(Var::X), E::var(Var::Y));
        assert_eq!(expr.to_string(), "(X * Y)");
    }

    #[test]
    fn test_builder_inv() {
        let expr = E::inv(E::var(Var::X));
        assert_eq!(expr.to_string(), "1/(X)");
    }

    #[test]
    fn test_builder_func() {
        let expr = E::func("f".into(), E::var(Var::X));
        assert_eq!(expr.to_string(), "f(X)");
    }

    #[test]
    fn test_expr_to_string_complex() {
        let expr1 = E::add(E::constant(Const::Numeric(2)), E::var(Var::X));
        let expr2 = E::mul(E::neg(E::var(Var::Y)), E::inv(E::var(Var::Z)));
        let complex = E::add(
            E::func("f".into(), expr1.clone()),
            E::func("g".into(), expr2.clone()),
        );
        assert_eq!(complex.to_string(), "(f((2 + X)) + g((-(Y) * 1/(Z))))");
    }

    #[test]
    fn test_diff_add_vars() {
        let expr = E::add(E::var(Var::X), E::var(Var::Y));
        let d = expr.diff(Var::X);
        assert_eq!(d.to_string(), "(1 + 0)");
    }

    #[test]
    fn test_unpack_inv_inv() {
        let double_inv = E::inv(E::inv(E::var(Var::X)));
        let inner = double_inv.clone().unpack_inv_inv().unwrap();
        assert_eq!(inner.to_string(), "X");
    }

    #[test]
    fn test_unpack_neg_neg() {
        let double_neg = E::neg(E::neg(E::neg(E::neg(E::neg(E::var(Var::Y))))));
        let inner = double_neg.clone().unneg();
        assert_eq!(inner.to_string(), "-(Y)");
    }

    #[test]
    fn test_simplify_double_inv() {
        let double_inv = E::inv(E::inv(E::var(Var::X)));
        let simplified = double_inv.uninv();
        assert_eq!(simplified.to_string(), "X");
    }

    #[test]
    fn test_simplify_double_neg() {
        let double_neg = E::neg(E::neg(E::var(Var::X)));
        let simplified = double_neg.unneg();
        assert_eq!(simplified.to_string(), "X");
    }

    #[test]
    fn test_substitute_named_constant() {
        let expr = E::add(E::constant(Const::Named("a".into())), E::var(Var::X));
        let substituted = expr.substitute("a", E::constant(Const::Numeric(10)));
        assert_eq!(substituted.to_string(), "(10 + X)");
    }

    #[test]
    fn test_substitute_deep() {
        let expr = E::mul(
            E::constant(Const::Named("a".into())),
            E::func("f".into(), E::constant(Const::Named("a".into()))),
        );
        let substituted = expr.substitute("a", E::constant(Const::Numeric(3)));
        assert_eq!(substituted.to_string(), "(3 * f(3))");
    }

    #[test]
    fn test_diff_neg() {
        let expr = E::neg(E::var(Var::X));
        let d = expr.diff(Var::X);
        assert_eq!(d.to_string(), "-(1)");
    }

    #[test]
    fn test_diff_mul() {
        let expr = E::mul(E::var(Var::X), E::var(Var::Y));
        let d = expr.diff(Var::X);
        assert_eq!(d.to_string(), "((1 * Y) + (X * 0))");
    }

    #[test]
    fn test_diff_inv() {
        let expr = E::inv(E::var(Var::X));
        let d = expr.diff(Var::X);
        assert_eq!(d.to_string(), "(-(1/((X * X))) * 1)");
    }

    #[test]
    fn test_diff_const_numeric() {
        let expr = E::constant(Const::Numeric(7));
        let d = expr.diff(Var::X);
        assert_eq!(d.to_string(), "0");
    }

    #[test]
    fn test_diff_const_named() {
        let expr = E::constant(Const::Named("a".into()));
        let d = expr.diff(Var::X);
        assert_eq!(d.to_string(), "0");
    }

    #[test]
    fn test_diff_func() {
        let expr = E::func("f".into(), E::var(Var::X));
        let d = expr.diff(Var::X);
        assert_eq!(d.to_string(), "(f_X(X) * 1)");
    }

    #[test]
    fn test_diff_var_same() {
        let d = E::var(Var::X).diff(Var::X);
        assert_eq!(d.to_string(), "1");
    }

    #[test]
    fn test_diff_var_other() {
        let d = E::var(Var::Y).diff(Var::X);
        assert_eq!(d.to_string(), "0");
    }

    #[test]
    fn test_diff_big_expression() {
        // (((X + -(Y)) * 1/(Z)) + (f((X * Y)) + g(1/(X))))
        let part1 = E::add(E::var(Var::X), E::neg(E::var(Var::Y)));
        let part2 = E::inv(E::var(Var::Z));
        let a = E::mul(part1.clone(), part2.clone());
        let xy = E::mul(E::var(Var::X), E::var(Var::Y));
        let b = E::func("f".into(), xy);
        let inv_x = E::inv(E::var(Var::X));
        let c = E::func("g".into(), inv_x);
        let big = E::add(a.clone(), E::add(b.clone(), c.clone()));

        assert_eq!(
            big.to_string(),
            "(((X + -(Y)) * 1/(Z)) + (f((X * Y)) + g(1/(X))))"
        );

        let d = big.diff(Var::X);
        assert_eq!(
            d.to_string(),
            "((((1 + -(0)) * 1/(Z)) + ((X + -(Y)) * (-(1/((Z * Z))) * 0))) + ((f_X((X * Y)) * ((1 * Y) + (X * 0))) + (g_X(1/(X)) * (-(1/((X * X))) * 1))))"
        );
    }

    #[test]
    fn test_arg_count_zeroary() {
        assert_eq!(E::constant(Const::Numeric(1)).arg_count(), 0);
        assert_eq!(E::var(Var::X).arg_count(), 0);
    }

    #[test]
    fn test_arg_count_unary() {
        assert_eq!(E::neg(E::var(Var::X)).arg_count(), 1);
        assert_eq!(E::inv(E::var(Var::X)).arg_count(), 1);
        assert_eq!(E::func("f".into(), E::var(Var::X)).arg_count(), 1);
    }

    #[test]
    fn test_arg_count_binary() {
        assert_eq!(E::add(E::var(Var::X), E::var(Var::Y)).arg_count(), 2);
        assert_eq!(E::mul(E::var(Var::X), E::var(Var::Z)).arg_count(), 2);
    }
}


/* Questions
1. What are Const(Const) and Var(Var)?
    It's a Rust pattern where the variant name is the same name as the data type it holds. First
Const represents the name of the variant of enum E. The second is the data type that this variant
stores. Situation with Var it's exactly the same.
2. Can we replace Box<E> with E? If not, then why not?
    We cannot replace Box<E> with E. It's because of how Rust handles memory. If we replaced it
there would be a problem of potential "infinite" size of E structure. Compiler can't know size_of(E)
because in case of having Add(E,E) or Mul(E,E) it would have to calculate size(E) = size(E) +
size(E) + ... making it infinite. That's why we use intelligent pointer making size fixed and known.
It points to next E that's on the heap.
*/